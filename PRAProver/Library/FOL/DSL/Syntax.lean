module

public meta import PRAProver.Library.FOL.DSL.Declaration
public meta import PRAProver.Library.Tactic.Logic

/-!
# Syntax for first-order declarations and proofs

Language and theory commands live inside the ordinary PRA command scope. Formula quotations have
their own binder and symbol syntax. These parsers only provide frontend input; elaboration emits
ordinary numerical PRA definitions and proofs.

First-order application binds tighter than PRA application. `D(t₁, …, tₖ)` fills the term slots
of `D` and `f[k]` selects a family member; the parentheses and brackets follow the name without a
space. `(D a₁ … aₘ)` applies `D` to its PRA parameters, and `(D a₁ … aₘ)(t₁, …, tₖ)` then
fills its slots. Spaces never apply a first-order value to a term.
-/

public meta section

namespace PRAProver.Library.FOL.DSL

open Lean Parser

open PRAProver.Surface
open PRAProver.Library.Tactic

declare_syntax_cat folSymbol

syntax "constant " ident : folSymbol
syntax "function " ident " of " num : folSymbol
syntax "relation " ident " of " num : folSymbol
syntax folFamilyIndex := "(" ident+ " : " &"Nat" ")"
syntax ident folFamilyIndex+ " : " "constant" : folSymbol
syntax ident folFamilyIndex+ " : " "function " "of " num : folSymbol
syntax ident folFamilyIndex+ " : " "relation " "of " num : folSymbol
syntax folSymbolSeq := sepBy1IndentSemicolon(folSymbol)
syntax (name := languageDecl) "fol_language " ident " where" ppIndent(colGt folSymbolSeq) : praDecl

declare_syntax_cat folTerm (behavior := both)
declare_syntax_cat folFormula
declare_syntax_cat folArg

syntax:max ident : folTerm
syntax:max (name := termSplice) (priority := high) "$" "{" praExpr "}" : folTerm
syntax:max (priority := high) "(" folTerm ")" : folTerm
syntax:max (priority := high) ident noWs "(" folTerm,* ")" : folTerm
syntax:max (priority := high) ident noWs "[" praExpr,+ "]" : folTerm
syntax:max (priority := high) ident noWs "[" praExpr,+ "]" noWs "(" folTerm,* ")" : folTerm
syntax:max (name := termApplication) "(" ident (ppSpace folArg)+ ")" : folTerm
syntax:max (name := termApplicationSlots)
  "(" ident (ppSpace folArg)+ ")" noWs "(" folTerm,* ")" : folTerm

/-! A term in a formula position: a term actual of a parameter, or a term argument of the
application form. The second production admits a term of any precedence inside parentheses;
the first keeps an argument of the application form atomic. -/
syntax:max (name := formulaTerm) (priority := low) folTerm:max : folFormula
syntax:lead (name := formulaTermWide) (priority := 1) folTerm : folFormula
syntax:max "⊥" : folFormula
syntax:max (name := formulaSplice) (priority := high) "$" "{" praExpr "}" : folFormula
syntax:max (name := formulaSpliceApplication) (priority := high)
  "$" "{" praExpr "}" "[" folTerm,* "]" : folFormula
syntax:max ident : folFormula
syntax:max (priority := high) "(" folFormula ")" : folFormula
syntax:max (priority := high) ident noWs "(" folTerm,* ")" : folFormula
syntax:max (priority := high) ident noWs "[" praExpr,+ "]" noWs "(" folTerm,* ")" : folFormula
syntax:max (name := formulaApplication) "(" ident (ppSpace folArg)+ ")" : folFormula
syntax:max (name := formulaApplicationSlots)
  "(" ident (ppSpace folArg)+ ")" noWs "(" folTerm,* ")" : folFormula
/-! The application form without slots may drop its parentheses where the position accepts a
formula or term of any precedence, as in `isTotal p ∧ q` or `x + num n`. Inside an argument
list each argument is atomic, so there the form keeps its parentheses. The arguments must
start to the right of the head's column, so a declaration on the next line is not read as an
argument. These two productions have low priority, so any other notation that reads the same
text wins: `succ(x)` applies the symbol, and `S a` is the successor notation of arithmetic. In
parentheses, `(D a)` reads as this form and expands to the application form. -/
syntax:lead (name := formulaApplied) (priority := low)
  withPosition(ident ppIndent((ppSpace colGt folArg)+)) : folFormula
syntax:lead (name := termApplied) (priority := low)
  withPosition(ident ppIndent((ppSpace colGt folArg)+)) : folTerm
/-- The parenthesized application form with the same head and arguments. The node is built
directly: in parentheses the text would parse again as this form. -/
private def parenthesizedApplication (kind : SyntaxNodeKind) (head : Syntax) (args : Syntax) :
    Syntax :=
  mkNode kind #[mkAtom "(", head, args, mkAtom ")"]
macro_rules
  | `(folFormula| $n:ident $args:folArg*) =>
    pure (parenthesizedApplication ``formulaApplication n (mkNullNode args))
macro_rules
  | `(folTerm| $n:ident $args:folArg*) =>
    pure (parenthesizedApplication ``termApplication n (mkNullNode args))
syntax:50 folTerm " = " folTerm : folFormula
syntax:50 folTerm " ≠ " folTerm : folFormula
syntax:40 "¬ " folFormula:40 : folFormula
syntax:35 folFormula:36 " ∧ " folFormula:35 : folFormula
syntax:30 folFormula:31 " ∨ " folFormula:30 : folFormula
syntax:25 folFormula:26 " → " folFormula:25 : folFormula
syntax:20 folFormula:21 " ↔ " folFormula:21 : folFormula
syntax:lead "∀ " ident+ ", " folFormula : folFormula
syntax:lead "∃ " ident+ ", " folFormula : folFormula

/-! An argument of the application form `(D a₁ … aₘ)` is parsed both as an atomic first-order
formula or term and as an atomic PRA expression. When both grammars accept the text, the parser
keeps the two readings in a `choice` node, and the reader selects one by the declared kind of
the parameter the argument fills: the PRA reading for a PRA parameter, the first-order reading
for a term or formula parameter. A lambda `(fun x y => A)` supplies a formula or term with
explicit arguments, and a named argument `(x := a)` fills an implicit parameter. -/
syntax:max (name := formulaArg) folFormula:max : folArg
syntax:max (name := praArg) praExpr:max : folArg
syntax:max (name := lambdaArg) "(" "fun " ident+ " => " folFormula ")" : folArg
syntax:max (name := namedArg) atomic("(" ident " := ") folArg ")" : folArg

declare_syntax_cat folAxiom

syntax:max (name := termParameterType) (priority := high) &"term" (" of " num)? : praExpr
syntax:max (name := formulaParameterType) (priority := high) &"formula" (" of " num)? : praExpr
syntax "axiom " ident (ppSpace praParam)* (" assuming " praExpr)? " := "
  folFormula : folAxiom
syntax folAxiomSeq := sepBy1IndentSemicolon(folAxiom)
syntax (name := theoryDecl) "fol_theory " ident " over " ident
  (" extends " ident)? " where" ppIndent(colGt folAxiomSeq) : praDecl
syntax (name := termQuote) "fol_term" "[" ident " | " folTerm "]" : praExpr
syntax (name := formulaQuote) "fol_formula" "[" ident " | " folFormula "]" : praExpr
syntax:20 (name := provableQuote) ident " ⊢ " folFormula : praExpr
syntax:20 (name := openProvableQuote) ident " ⊢ " &"free " ident+ " | "
  folFormula : praExpr
declare_syntax_cat folDefInput

syntax ident (" of " num)? : folDefInput
syntax (name := termDefinition) "fol_def " ident " over " ident (ppSpace praParam)*
  " : " (atomic(folDefInput " → "))* &"term" (" of " num)? " := " ("fun " ident+ " => ")?
  folTerm : praDecl
syntax (name := formulaDefinition) "fol_def " ident " over " ident (ppSpace praParam)*
  " : " (atomic(folDefInput " → "))* &"formula" (" of " num)? " := " ("fun " ident+ " => ")?
  folFormula : praDecl
syntax (name := folTheorem) "fol_theorem " ident (ppSpace praParam)* " : "
  ident " ⊢ " folFormula " := " praExpr : praDecl
syntax (name := openFolTheorem) "fol_theorem " ident (ppSpace praParam)* " : "
  ident " ⊢ " &"free " ident+ " | " folFormula " := " praExpr : praDecl

/-! A proof reference names an assumption, an axiom, or a PRA proof, applies one to its
arguments in the application form, or splices a PRA proof expression. The bracketed list that
may follow instantiates the leading object quantifiers of the proof. -/
declare_syntax_cat folRef

syntax:max (name := nameRef) ident : folRef
syntax:max (name := applicationRef) "(" ident folArg+ ")" : folRef
/-! An applied reference without parentheses. The instantiation list `[t₁, …]` of a tactic
follows a reference without a space, so it attaches to a name, a parenthesized reference, or a
splice; an applied reference is instantiated in parentheses, `(thm a b)[x]`. -/
syntax:max (name := appliedRef) ident (colGt folArg)+ : folRef
syntax:max (name := spliceRef) "$" "{" praExpr "}" : folRef
syntax (name := pintroTac) "pintro" (ppSpace colGt ident)+ : praTactic
syntax (name := papplyTac) "papply " folRef (noWs "[" folTerm,* "]")? : praTactic
syntax (name := passumptionTac) "passumption" : praTactic
syntax (name := pconstructorTac) "pconstructor" : praTactic
syntax (name := pleftTac) "pleft" : praTactic
syntax (name := prightTac) "pright" : praTactic
syntax (name := pexistsTac) "pexists " folTerm : praTactic
syntax (name := pcasesTac) "pcases " folRef (noWs "[" folTerm,* "]")?
  " with " praCasesPattern : praTactic
syntax (name := phaveTac) "phave " ident " : " folFormula : praTactic
syntax (name := pcontradictionTac) "pcontradiction" : praTactic
syntax (name := pexfalsoTac) "pexfalso" : praTactic
syntax (name := preflTac) "prefl" : praTactic
syntax (name := ptransTac) "ptrans " folTerm : praTactic
syntax (name := psymmTac) "psymm" : praTactic
syntax (name := pcongrTac) "pcongr" : praTactic
syntax folRewriteRule := ("← ")? folRef
syntax (name := prwTac) "prw" (" [" folRewriteRule,* "]")? (" at " ident)? : praTactic
syntax (name := pexactTac) "pexact " folRef (noWs "[" folTerm,* "]")? : praTactic
syntax (name := pinductionTac) "pinduction " ident (" using " ident)?
  (atomic(" (" &"motive") " := " "fun " ident " => " folFormula ")")?
  (atomic(" (" "assuming") " := " praExpr ")")? " with"
  ppLine "| " &"zero" "=>" ppIndent(colGt praTacticSeq)
  ppLine "| " &"succ" ident ident " =>" ppIndent(colGt praTacticSeq) : praTactic
syntax (name := pstrongInductionTac) "pinduction " ident (" using " ident)?
  (atomic(" (" &"motive") " := " "fun " ident " => " folFormula ")")?
  (atomic(" (" "assuming") " := " praExpr ")")? " with"
  ppLine "| " &"step" ident ident " =>" ppIndent(colGt praTacticSeq) : praTactic

end PRAProver.Library.FOL.DSL
