module

public meta import LeanPRA.Library.FOL.DSL.Declaration
public meta import LeanPRA.Library.Tactic.Logic

/-!
# Syntax for first-order declarations and proofs

Language and theory commands live inside the ordinary PRA command scope. Formula quotations have
their own binder and symbol syntax. These parsers only provide frontend input; elaboration emits
ordinary numerical PRA definitions and proofs.
-/

public meta section

namespace LeanPRA.Library.FOL.DSL

open Lean Parser

open LeanPRA.Surface
open LeanPRA.Library.Tactic

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

syntax:max ident : folTerm
syntax:max (name := termSplice) (priority := high) "$" "{" praExpr "}" : folTerm
declare_syntax_cat folPraActual

syntax (name := numericalActual) (priority := low) atomic("(" ident " := ")
  praExpr ")" : folPraActual
syntax:max (name := termDefinedApplication) ident folPraActual+ "(" folTerm,* ")" : folTerm
syntax:max "(" folTerm ")" : folTerm
syntax:max ident "(" folTerm,* ")" : folTerm
syntax:max ident "[" praExpr,+ "]" : folTerm
syntax:max ident "[" praExpr,+ "]" "(" folTerm,* ")" : folTerm

declare_syntax_cat folFormula

syntax:max (name := formulaTerm) (priority := low) folTerm : folFormula
syntax:max "⊥" : folFormula
syntax:max (name := formulaSplice) (priority := high) "$" "{" praExpr "}" : folFormula
syntax:max (name := formulaSpliceApplication) (priority := high)
  "$" "{" praExpr "}" "[" folTerm,* "]" : folFormula
syntax:max (name := formulaDefinedApplication) ident folPraActual+ "(" folTerm,* ")" : folFormula
syntax:max ident : folFormula
syntax:max ident ppSpace folTerm:max+ : folFormula
syntax:max "(" folFormula ")" : folFormula
syntax:max (priority := high) ident "(" folTerm,* ")" : folFormula
syntax:max (priority := high) ident "[" praExpr,+ "]" "(" folTerm,* ")" : folFormula
syntax:50 folTerm " = " folTerm : folFormula
syntax:50 folTerm " ≠ " folTerm : folFormula
syntax:40 "¬ " folFormula:40 : folFormula
syntax:35 folFormula:36 " ∧ " folFormula:35 : folFormula
syntax:30 folFormula:31 " ∨ " folFormula:30 : folFormula
syntax:25 folFormula:26 " → " folFormula:25 : folFormula
syntax:20 folFormula:21 " ↔ " folFormula:21 : folFormula
syntax:lead "∀ " ident+ ", " folFormula : folFormula
syntax:lead "∃ " ident+ ", " folFormula : folFormula

declare_syntax_cat folAxiom

syntax:max (name := termParameterType) (priority := high) &"term" (" of " num)? : praExpr
syntax:max (name := formulaParameterType) (priority := high) &"formula" (" of " num)? : praExpr
syntax (name := formulaActual) (priority := high) atomic("(" ident " := ")
  "fun " ident* " => " folFormula ")" : folPraActual
syntax (name := formulaValueActual) atomic("(" ident " := ") folFormula ")" : folPraActual
syntax (name := formulaCodeActual) (priority := high) atomic("(" ident " := ")
  "$" "{" praExpr "}" ")" : folPraActual

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

declare_syntax_cat folSchemaActual

syntax "(" ident " := " "fun " ident+ " => " folFormula ")" : folSchemaActual
syntax "(" ident " := " folFormula ")" : folSchemaActual
syntax (name := numericalSchemaActual) (priority := low)
  "(" ident " := " praExpr ")" : folSchemaActual
syntax (name := guardActual) "(" "assuming" " := " praExpr ")" : folSchemaActual
syntax (name := pintroTac) "pintro" (ppSpace colGt ident)+ : praTactic
syntax (name := papplyTac) "papply " praExpr ("[" folTerm,* "]")? : praTactic
syntax (name := passumptionTac) "passumption" : praTactic
syntax (name := pconstructorTac) "pconstructor" : praTactic
syntax (name := pleftTac) "pleft" : praTactic
syntax (name := prightTac) "pright" : praTactic
syntax (name := pexistsTac) "pexists " folTerm : praTactic
syntax (name := pcasesTac) "pcases " praExpr ("[" folTerm,* "]")?
  " with " praCasesPattern : praTactic
syntax (name := phaveTac) "phave " ident " : " folFormula : praTactic
syntax (name := pcontradictionTac) "pcontradiction" : praTactic
syntax (name := pexfalsoTac) "pexfalso" : praTactic
syntax (name := preflTac) "prefl" : praTactic
syntax (name := ptransTac) "ptrans " folTerm : praTactic
syntax (name := psymmTac) "psymm" : praTactic
syntax (name := pcongrTac) "pcongr" : praTactic
syntax (name := prwTac) "prw" (" [" praExpr,* "]")? (" at " ident)? : praTactic
syntax (name := pexactTac) "pexact " ident folSchemaActual*
  ("[" folTerm,* "]")? : praTactic
syntax (name := pexactProofTac) "pexact " "(" praExpr ")"
  ("[" folTerm,* "]")? : praTactic
syntax (name := pinductionTac) "pinduction " ident (" using " ident)?
  (atomic(" (" &"motive") " := " "fun " ident " => " folFormula ")")?
  (atomic(" (" "assuming") " := " praExpr ")")? " with"
  ppLine "| " &"zero" "=>" ppIndent(colGt praTacticSeq)
  ppLine "| " &"succ" ident ident " =>" ppIndent(colGt praTacticSeq) : praTactic
syntax (name := pstrongInductionTac) "pinduction " ident (" using " ident)?
  (atomic(" (" &"motive") " := " "fun " ident " => " folFormula ")")?
  (atomic(" (" "assuming") " := " praExpr ")")? " with"
  ppLine "| " &"step" ident ident " =>" ppIndent(colGt praTacticSeq) : praTactic

end LeanPRA.Library.FOL.DSL
