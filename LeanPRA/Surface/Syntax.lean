module

public meta import LeanPRA.Surface.Recovery

/-!
# PRA surface grammar

Surface syntax for the PRA language. Terms, predicates, and proofs share the `praExpr` category;
the elaborator disambiguates them from the expected category.

- `praExpr` parses expressions and type annotations.
- `praParam` parses declaration parameter groups.
- `praDecl` parses declarations, `#check`, `#print`, `open`, and `namespace` inside `pra … end`.
- `praBlock` parses a `pra … end` command block.
-/

public meta section

namespace LeanPRA.Surface

declare_syntax_cat praBinder
syntax ident : praBinder
syntax "_" : praBinder

/-- Lambda binders, which allow tuple patterns for destructuring proofs. -/
declare_syntax_cat praFunBinder
syntax ident : praFunBinder
syntax "_" : praFunBinder
syntax (name := praTupleBinder) "(" praFunBinder ", " praFunBinder,+ ")" : praFunBinder

declare_syntax_cat praExpr (behavior := both)
syntax:max ident : praExpr
syntax:max (name := praUnknown) "?" num : praExpr
syntax:max "@" ident : praExpr
syntax:max "@" "(" praExpr ")" : praExpr
syntax:max "(" ident " := " praExpr ")" : praExpr
syntax:max "Prop" : praExpr
syntax:max num : praExpr
syntax:max (name := praHole) "_" : praExpr
syntax:max (name := praSyntheticHole) "?" (ident <|> "_") : praExpr
syntax:max "(" praExpr ")" : praExpr
syntax:max "(" praExpr " : " praExpr ")" : praExpr
syntax:max "(" praExpr ", " praExpr,+ ")" : praExpr
syntax:max "(" ")" : praExpr
syntax:max atomic(&"induction" " (" &"motive" " := ") praExpr ")" : praExpr
syntax:70 praExpr:70 ppSpace praExpr:71 : praExpr
syntax:50 praExpr:51 " = " praExpr:51 : praExpr
syntax:35 praExpr:36 " ∧ " praExpr:35 : praExpr
syntax:30 praExpr:31 " ∨ " praExpr:30 : praExpr
syntax:25 praExpr:26 " → " praExpr:25 : praExpr
syntax:20 praExpr:21 " ↔ " praExpr:20 : praExpr
syntax:40 "¬" praExpr:40 : praExpr
syntax:lead "fun " praFunBinder+ " => " recoverPraExpr(praExpr) : praExpr
syntax:lead "fun " praFunBinder+ " : " praExpr " => " recoverPraExpr(praExpr) : praExpr
syntax:lead "∀ " praBinder+ " : " &"Nat" ", " recoverPraExpr(praExpr) : praExpr
syntax:lead "∃ " praBinder+ " : " &"Nat" ", " recoverPraExpr(praExpr) : praExpr
syntax:lead "∀ " praBinder+ ", " recoverPraExpr(praExpr) : praExpr
syntax:lead "∀ " "{" praBinder+ "}" ", " recoverPraExpr(praExpr) : praExpr
syntax:lead "∀ " "{" praBinder+ " : " &"Nat" "}" ", " recoverPraExpr(praExpr) : praExpr
syntax:lead "∃ " praBinder+ ", " recoverPraExpr(praExpr) : praExpr
syntax:lead "let " ident " := " recoverPraExpr(praExpr) "; " recoverPraExpr(praExpr) : praExpr
syntax:lead "let " "(" praBinder ", " praBinder,+ ")" " := "
  recoverPraExpr(praExpr) "; " recoverPraExpr(praExpr) : praExpr
syntax:lead "let " ident " : " praExpr " := "
  recoverPraExpr(praExpr) "; " recoverPraExpr(praExpr) : praExpr


open Lean PrettyPrinter Parenthesizer in
/-- Parenthesize `praExpr` by precedence, copying source info onto added parentheses. -/
@[category_parenthesizer praExpr] def parenthesizePraExpr : CategoryParenthesizer := fun prec =>
  maybeParenthesize `praExpr true wrapParens prec (parenthesizeCategoryCore `praExpr prec)
where
  wrapParens (stx : Syntax) : Syntax := Unhygienic.run do
    let info := SourceInfo.fromRef stx
    let inner : TSyntax `praExpr := ⟨stx.setInfo .none⟩
    return (← `(praExpr| ($inner))).raw.setInfo info

declare_syntax_cat praParam
syntax "(" ident+ " : " praExpr ")" : praParam
syntax "{" ident+ " : " praExpr "}" : praParam

declare_syntax_cat praDecl
syntax "def " ident (ppSpace praParam)* " : " recoverPraExpr(praExpr)
  " := " recoverPraExpr(praExpr) : praDecl
syntax "theorem " ident (ppSpace praParam)* " : " recoverPraExpr(praExpr)
  " := " recoverPraExpr(praExpr) : praDecl
syntax "#check " praExpr : praDecl
syntax "#print " ident : praDecl
syntax "open " ident+ : praDecl
syntax "namespace " ident praDecl* "end" (ppSpace ident)? : praDecl
syntax (name := praBlock) "pra" praDecl* "end" : command

end LeanPRA.Surface
