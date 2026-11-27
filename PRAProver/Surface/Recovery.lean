module

public meta import Lean

/-!
# Recovery of empty PRA expression slots

`recoverPraExpr` inserts a synthetic `recoveredHole` node when an expected expression is missing,
so the elaborator can still show goals at the cursor. Importing this module registers the parser
alias before `PRAProver.Surface.Syntax` uses it.
-/

public meta section

namespace PRAProver.Surface

private partial def whitespaceStart (c : Lean.Parser.ParserContext)
    (pos : String.Pos.Raw) : String.Pos.Raw :=
  if pos.byteIdx == 0 then pos else
    let previous := c.prev pos
    if (c.get previous).isWhitespace then whitespaceStart c previous else pos

/-- Insert `recoveredHole` when `p` fails without consuming input. -/
def recoverPraExpr (p : Lean.Parser.Parser) : Lean.Parser.Parser := {
  info := p.info
  fn := fun c s =>
    let result := p.fn c s
    if result.hasError && result.pos == s.pos then
      let info := Lean.SourceInfo.synthetic (whitespaceStart c s.pos) s.pos true
      s.pushSyntax (.node info `PRAProver.Surface.recoveredHole #[])
    else result }

/-- Pass formatting through to `p`. -/
@[combinator_formatter recoverPraExpr] def recoverPraExpr.formatter
    (p : Lean.PrettyPrinter.Formatter) : Lean.PrettyPrinter.Formatter := p

/-- Pass parenthesization through to `p`. -/
@[combinator_parenthesizer recoverPraExpr] def recoverPraExpr.parenthesizer
    (p : Lean.PrettyPrinter.Parenthesizer) : Lean.PrettyPrinter.Parenthesizer := p

initialize
  register_parser_alias "recoverPraExpr" recoverPraExpr { stackSz? := some 1 }

end PRAProver.Surface
