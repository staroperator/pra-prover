module

public meta import Lean

/-!
# Static PRA documentation pages

`writeSite` assembles extracted declarations into module pages, a module index, and a browser
search index. Each module has one page with an anchor for every declaration. Navigation uses
relative URLs so the directory can be published under a GitHub Pages project.
-/

meta section

namespace LeanPRA.DocGen

open Lean

private structure CodeSpan where
  text : String
  target : Option String := none
  deriving FromJson, Inhabited

private structure Entry where
  name : String
  kind : String
  signature : String
  body : Option String
  doc : Option String
  signatureCode : Array CodeSpan := #[]
  bodyCode : Option (Array CodeSpan) := none
  deriving FromJson, Inhabited

private structure ModuleComment where
  doc : String
  before : Nat
  deriving FromJson

private structure ModuleData where
  owner : String
  entries : Array Entry
  docs : Array ModuleComment := #[]

private def escape (s : String) : String :=
  s.foldl (init := "") fun out c =>
    match c with
    | '&' => out ++ "&amp;"
    | '<' => out ++ "&lt;"
    | '>' => out ++ "&gt;"
    | '"' => out ++ "&quot;"
    | '\'' => out ++ "&#39;"
    | c => out.push c

private def url (s : String) : String := String.join <| s.toUTF8.toList.map fun b =>
  let c := Char.ofNat b.toNat
  if c.isAlphanum && b.toNat < 128 || "-_.~".contains c then String.singleton c
  else "%" ++ String.ofList ["0123456789ABCDEF".toList[b.toNat / 16]!,
    "0123456789ABCDEF".toList[b.toNat % 16]!]

private def pageName (owner : String) : String := owner ++ ".html"

private def anchor (name : String) : String := "d-" ++ name

private def link (href label : String) : String :=
  s!"<a href=\"{escape href}\">{escape label}</a>"

private def safeUrl (href : String) : Bool :=
  !href.toList.any (fun c => c.isWhitespace || c == '\\' || c.toNat < 32) &&
    (href.startsWith "https://" || href.startsWith "http://" || href.startsWith "mailto:" ||
      (!href.contains ':' && !href.startsWith "//"))

private def takeUntil (delimiter : List Char) (input : List Char) : Option (String × List Char) :=
  go input []
where
  go : List Char → List Char → Option (String × List Char)
    | [], _ => none
    | c :: cs, acc =>
      if delimiter.isPrefixOf (c :: cs) then some (String.ofList acc.reverse, (c :: cs).drop
        delimiter.length)
      else go cs (c :: acc)

private partial def markdownInline (text : String) : String := go text.toList
where
  go : List Char → String
    | [] => ""
    | '\\' :: c :: cs => escape (String.singleton c) ++ go cs
    | '`' :: cs =>
      let ticks := cs.takeWhile (· == '`')
      let delimiter := '`' :: ticks
      match takeUntil delimiter (cs.drop ticks.length) with
      | some (body, rest) => "<code>" ++ escape (body.replace "\n" " ") ++ "</code>" ++ go rest
      | none => escape (String.ofList delimiter) ++ go (cs.drop ticks.length)
    | '[' :: cs =>
      match takeUntil [']', '('] cs with
      | some (label, rest) =>
        match takeUntil [')'] rest with
        | some (href, rest) =>
          let label := markdownInline label
          (if safeUrl href then "<a href=\"" ++ escape href ++ "\">" ++ label ++ "</a>"
            else label) ++ go rest
        | none => "[" ++ go cs
      | none => "[" ++ go cs
    | c :: cs =>
      if c == '*' || c == '_' then
        let double := cs.head? == some c
        let delimiter := if double then [c, c] else [c]
        let rest := if double then cs.drop 1 else cs
        match takeUntil delimiter rest with
        | some (body, rest) =>
          let tag := if double then "strong" else "em"
          "<" ++ tag ++ ">" ++ markdownInline body ++ "</" ++ tag ++ ">" ++ go rest
        | none => escape (String.ofList delimiter) ++ go rest
      else escape (String.singleton c) ++ go cs

private def trimmed (s : String) : String := s.trimAscii.toString

private def fence? (s : String) : Option (Char × Nat × String) := do
  let chars := (trimmed s).toList
  let c ← chars.head?
  unless c == '`' || c == '~' do none
  let count := (chars.takeWhile (· == c)).length
  unless count ≥ 3 do none
  some (c, count, trimmed (String.ofList (chars.drop count)))

private def heading? (s : String) : Option (Nat × String) := do
  let chars := (trimmed s).toList
  let count := (chars.takeWhile (· == '#')).length
  unless count > 0 && count ≤ 6 && chars[count]? == some ' ' do none
  some (min 6 (count + 1), trimmed (String.ofList (chars.drop (count + 1))))

private def listItem? (s : String) : Option (Bool × String) := do
  let chars := s.toList
  match chars with
  | '-' :: ' ' :: rest | '*' :: ' ' :: rest | '+' :: ' ' :: rest =>
    some (false, String.ofList rest)
  | _ =>
    let digits := chars.takeWhile Char.isDigit
    unless !digits.isEmpty do none
    match chars.drop digits.length with
    | '.' :: ' ' :: rest | ')' :: ' ' :: rest => some (true, String.ofList rest)
    | _ => none

private def startsBlock (s : String) : Bool :=
  (trimmed s).isEmpty || (fence? s).isSome || (heading? s).isSome ||
    (listItem? s).isSome || s.startsWith "> "

private partial def markdownBlocks (lines : List String) : String :=
  match lines with
  | [] => ""
  | line :: rest => Id.run do
    if (trimmed line).isEmpty then return markdownBlocks rest
    if let some (marker, width, language) := fence? line then
      let (body, remaining) := rest.span fun s =>
        match fence? s with
        | some (c, n, tail) => !(c == marker && n ≥ width && tail.isEmpty)
        | none => true
      let cls := if language.isEmpty then "" else
        " class=\"language-" ++ escape language ++ "\""
      return "<pre><code" ++ cls ++ ">" ++
        escape (String.intercalate "\n" body) ++ "</code></pre>" ++
        markdownBlocks (remaining.drop 1)
    if let some (level, text) := heading? line then
      let tag := s!"h{level}"
      return s!"<{tag}>" ++ markdownInline text ++ s!"</{tag}>" ++ markdownBlocks rest
    if line.startsWith "> " then
      let (body, remaining) := lines.span (·.startsWith "> ")
      return "<blockquote>" ++ markdownBlocks (body.map (fun s => (s.drop 2).toString)) ++
        "</blockquote>" ++ markdownBlocks remaining
    if let some (ordered, _) := listItem? line then
      let (items, remaining) := listItems ordered lines
      let tag := if ordered then "ol" else "ul"
      return s!"<{tag}>" ++ items ++ s!"</{tag}>" ++ markdownBlocks remaining
    let (paragraph, remaining) := rest.span (fun s => !startsBlock s)
    return "<p>" ++ markdownInline (String.intercalate "\n" (line :: paragraph)) ++
      "</p>" ++ markdownBlocks remaining
where
  listItems (ordered : Bool) (lines : List String) : String × List String := Id.run do
    let line :: rest := lines | return ("", [])
    let some (kind, first) := listItem? line | return ("", lines)
    if kind != ordered then return ("", lines)
    let (continuation, rest) := rest.span fun s =>
      s.startsWith "  " || (!(trimmed s).isEmpty && !startsBlock s)
    let continuation := continuation.map fun s =>
      if s.startsWith "  " then (s.drop 2).toString else s
    let body := markdownBlocks (first :: continuation)
    let (next, rest) := listItems ordered rest
    return ("<li>" ++ body ++ "</li>" ++ next, rest)

private def markdown (s : String) : String := markdownBlocks (s.splitOn "\n")

private abbrev Links := Std.HashMap String String

private def codeHtml (links : Links) (plain : String) (code : Array CodeSpan) : String :=
  if code.isEmpty then escape plain else
    String.join (code.toList.map fun span =>
      match span.target.bind links.get? with
      | some href => link href span.text
      | none => escape span.text)

private partial def moduleTree (paths : Array (List String × String)) (current : String) :
    String := Id.run do
  let mut labels : Array String := #[]
  for (parts, _) in paths do
    if let label :: _ := parts then
      unless labels.contains label do labels := labels.push label
  let mut items := #[]
  for label in labels.qsort (· < ·) do
    let branch := paths.filter fun (parts, _) => parts.head? == some label
    let owner := branch.findSome? fun (parts, owner) =>
      if parts.length == 1 then some owner else none
    let children := branch.filterMap fun (parts, owner) =>
      match parts with
      | _ :: child :: rest => some (child :: rest, owner)
      | _ => none
    let heading := match owner with
      | none => escape label
      | some owner =>
        let selected := if owner == current then " aria-current=\"page\"" else ""
        let href := pageName owner
        s!"<a href=\"{escape href}\"{selected}>{escape label}</a>"
    if children.isEmpty then
      items := items.push ("<li class=\"module-leaf\">" ++ heading ++ "</li>")
    else
      let expanded := if current.isEmpty || branch.any (fun (_, owner) => owner == current)
        then " open" else ""
      items := items.push (s!"<li><details class=\"module-branch\"{expanded}><summary>" ++
        heading ++ "</summary>" ++ moduleTree children current ++ "</details></li>")
  return "<ul>" ++ String.join items.toList ++ "</ul>"

private def navigation (modules : Array ModuleData) (current : String := "") : String :=
  "<nav class=\"modules\" aria-label=\"Modules\"><details class=\"module-index\" open>" ++
    "<summary>Modules</summary><div class=\"module-tree\">" ++
    moduleTree (modules.map fun m => (m.owner.splitOn ".", m.owner)) current ++
    "</div></details></nav>"

private def shell (title nav body toc : String) : String :=
  "<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\">" ++
  "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">" ++
  s!"<title>{escape title} · PRA Library</title>" ++
  "<link rel=\"stylesheet\" href=\"style.css\"></head><body>" ++
  "<header><a class=\"brand\" href=\"index.html\">PRA Library</a>" ++
  "<span class=\"subtitle\">Definitions &amp; theorems</span>" ++
  "<a href=\"index.html#search\">Search</a></header><div class=\"layout\">" ++
  nav ++ "<main id=\"content\">" ++ body ++ "</main>" ++
  "<nav class=\"toc\" aria-label=\"On this page\"><h2>On this page</h2>" ++
  link "#content" "Return to top" ++ toc ++
  "</nav></div></body></html>"

private def entryHtml (links : Links) (entry : Entry) : String :=
  let heading := "<div class=\"decl-heading\">" ++
    s!"<span class=\"kind\">{escape entry.kind}</span><h2>" ++
    link ("#" ++ url (anchor entry.name)) entry.name ++ "</h2></div>"
  let doc := entry.doc.map (fun s => s!"<div class=\"doc\">{markdown s}</div>") |>.getD ""
  let body := entry.body.map (fun s =>
    "<details class=\"definition\"><summary>Definition</summary>" ++
    s!"<pre class=\"definition-body\"><code>" ++
    codeHtml links s (entry.bodyCode.getD #[]) ++ "</code></pre></details>") |>.getD ""
  s!"<section class=\"declaration\" id=\"{escape (anchor entry.name)}\">" ++ heading ++
    doc ++ "<pre class=\"signature\"><code>" ++
    codeHtml links entry.signature entry.signatureCode ++ "</code></pre>" ++
    body ++ "</section>"

private def writeModulePage (dir : System.FilePath) (nav : String) (links : Links)
    (m : ModuleData) : IO Unit := do
  let declarations := "<h2>Declarations</h2><ul class=\"declaration-list\">" ++
    String.join (m.entries.toList.map fun e =>
      "<li>" ++ link ("#" ++ url (anchor e.name)) e.name ++ "</li>") ++ "</ul>"
  let toc := (if m.docs.isEmpty then "" else
    link "#module-docs" "Module documentation") ++ declarations
  let mut docs := Array.replicate (m.entries.size + 1) ""
  for doc in m.docs, i in [:m.docs.size] do
    unless doc.before ≤ m.entries.size do
      throw (IO.userError s!"invalid module comment position in {m.owner}: {doc.before}")
    let id := if i == 0 then "module-docs" else s!"module-docs-{i + 1}"
    let html := s!"<section id=\"{id}\" class=\"doc module-doc\">" ++
      markdown doc.doc ++ "</section>"
    docs := docs.modify doc.before (· ++ html)
  let mut parts := #[]
  for entry in m.entries, i in [:m.entries.size] do
    parts := parts.push (docs[i]! ++ entryHtml links entry)
  parts := parts.push docs.back!
  let count := s!"<p class=\"muted\">{m.entries.size} PRA declarations</p>"
  let body := "<div class=\"breadcrumb\">Library / Module</div>" ++
    s!"<h1>{escape m.owner}</h1>" ++ count ++ String.join parts.toList
  IO.FS.writeFile (dir / pageName m.owner) (shell m.owner nav body toc)

private def fileStamp (path : System.FilePath) : IO Json := do
  let info ← path.metadata
  unless info.type == .file do throw (IO.userError s!"expected a file: {path}")
  return toJson #[path.fileName.getD "", toString info.byteSize,
    toString info.modified.sec, toString info.modified.nsec]

private def siteInputs (dataDir assets : System.FilePath) (owners : List String) : IO Json := do
  let inputs ← owners.mapM fun owner => fileStamp (dataDir / s!"{owner}.json")
  let assets ← ["style.css", "search.js"].mapM fun (name : String) => do
    return toJson (name, hash (← IO.FS.readFile (assets / name)))
  return Json.mkObj [
    ("renderer", toJson (hash (include_str "Site.lean"))),
    ("modules", toJson inputs), ("assets", toJson assets)]

private def siteOutputs (directory : System.FilePath) : IO Json := do
  let files := (← directory.readDir).qsort (fun a b => a.fileName < b.fileName)
  return toJson (← files.mapM fun file => fileStamp file.path)

private def siteUnchanged (directory : System.FilePath) (inputs : Json) : IO Bool := do
  try
    let .ok cache := Json.parse (← IO.FS.readFile (directory.addExtension "cache.json"))
      | return false
    let .ok previous := cache.getObjVal? "inputs" | return false
    unless previous == inputs do return false
    let .ok outputs := cache.getObjVal? "outputs" | return false
    return outputs == (← siteOutputs directory)
  catch _ => return false

/-- Build module pages and a search index from the data files named in `owners`.
Reuse the site when its inputs and output files match the saved cache. -/
public def writeSite (dataDir directory assets : System.FilePath) (owners : List String) :
    IO Unit := do
  let inputs ← siteInputs dataDir assets owners
  if ← siteUnchanged directory inputs then
    IO.println s!"PRA docs are up to date: {directory / "index.html"}"
    return
  let mut modules := #[]
  for owner in owners do
    let raw ← IO.FS.readFile (dataDir / s!"{owner}.json")
    let parsed := do
      let json ← Json.parse raw
      let found ← json.getObjValAs? String "module"
      unless found == owner do throw s!"module mismatch: expected {owner}, found {found}"
      let entries ← json.getObjValAs? (Array Entry) "declarations"
      let docs ← json.getObjValAs? (Array ModuleComment) "moduleDocs"
      return { owner, entries, docs : ModuleData }
    let m ← IO.ofExcept parsed
    unless m.entries.isEmpty do modules := modules.push m
  let mut links : Links := {}
  for m in modules do
    for e in m.entries do
      let name := e.name
      if links.contains name then throw (IO.userError s!"duplicate PRA declaration: {name}")
      links := links.insert name (pageName m.owner ++ "#" ++ url (anchor name))
  let nav := navigation modules
  let temporary := directory.addExtension "next"
  if ← temporary.pathExists then IO.FS.removeDirAll temporary
  IO.FS.createDirAll temporary
  let mut search := #[]
  let mut manifest := #[]
  let mut definitions := 0
  let mut theorems := 0
  for m in modules do
    writeModulePage temporary (navigation modules m.owner) links m
    for e in m.entries do
      if e.kind == "theorem" then theorems := theorems + 1
      else definitions := definitions + 1
      search := search.push (toJson #[e.name, pageName m.owner, e.kind])
    manifest := manifest.push (Json.mkObj [("module", toJson m.owner),
      ("declarations", toJson m.entries.size), ("pages", toJson (1 : Nat))])
  IO.FS.writeFile (temporary / "declarations.js")
    ("window.praDeclarations=" ++ (Json.arr search).compress ++ ";\n")
  let summary := s!"{modules.size} modules · {definitions} definitions · {theorems} theorems"
  let listing := "<ul class=\"module-list\">" ++ String.join (modules.toList.map fun m =>
    "<li>" ++ link (pageName m.owner) m.owner ++
    s!" <span class=\"muted\">({m.entries.size})</span></li>") ++ "</ul>"
  let body := "<div class=\"breadcrumb\">Documentation</div><h1>PRA Library</h1>" ++
    s!"<p class=\"muted\">{summary}</p>" ++
    "<label for=\"search\">Find a declaration</label>" ++
    "<input id=\"search\" type=\"search\" placeholder=\"Search by name, e.g. add_comm\">" ++
    "<p id=\"search-status\" role=\"status\"></p><ul id=\"search-results\"></ul>" ++
    "<noscript>Search requires JavaScript.</noscript>" ++
    "<h2 id=\"modules\">Modules</h2>" ++ listing ++
    "<script src=\"declarations.js\"></script><script src=\"search.js\"></script>"
  IO.FS.writeFile (temporary / "index.html")
    (shell "Index" nav body (link "#modules" "Modules"))
  IO.FS.writeFile (temporary / "manifest.json") (Json.mkObj [
    ("modules", .arr manifest), ("definitions", toJson definitions),
    ("theorems", toJson theorems)]).pretty
  for asset in ["style.css", "search.js"] do
    IO.FS.writeFile (temporary / asset) (← IO.FS.readFile (assets / asset))
  IO.FS.writeFile (temporary / ".nojekyll") ""
  if ← directory.pathExists then IO.FS.removeDirAll directory
  IO.FS.rename temporary directory
  if inputs == (← siteInputs dataDir assets owners) then
    let cache := directory.addExtension "cache.json"
    let temporary := cache.addExtension "tmp"
    IO.FS.writeFile temporary (Json.mkObj [
      ("inputs", inputs), ("outputs", ← siteOutputs directory)]).compress
    IO.FS.rename temporary cache
  IO.println s!"PRA docs: {summary}\n{directory / "index.html"}"

end LeanPRA.DocGen
