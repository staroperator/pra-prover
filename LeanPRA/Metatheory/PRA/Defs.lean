module

/-!
# First-order and quantifier-free primitive recursive arithmetic

Syntax and proof rules for the first-order theory of PRA and two quantifier-free presentations:

- `Primrec n` represents primitive recursive expressions of arity `n`.
- `PRA.Term n` and `PRA.Formula n` represent terms and formulas in `n` free variables.
- `PRA.QFFormula n` represents quantifier-free formulas; `PRA.QFFormula.toFormula` embeds them
  into `PRA.Formula n`.
- `PRA.Proof` defines classical first-order PRA with quantifier-free induction axioms.
- `PRA.QFProof` defines classical quantifier-free PRA with induction and substitution rules.
- `PRA.QFProofI` defines intuitionistic quantifier-free PRA with the same arithmetic rules.

Variable `0` is the innermost bound variable. Quantifiers bind variable `0`, and substitution shifts
terms under binders to avoid capture. In `Primrec.prec f g`, the recursion argument comes first,
followed by the parameters; the step `g` takes the predecessor, the recursive value, and the
parameters in that order.
-/

@[expose] public section

/-- Syntax of primitive recursive expressions, indexed by their arity. -/
inductive Primrec : Nat → Type
  | zero : Primrec 0
  | proj {n} : Fin n → Primrec n
  | succ : Primrec 1
  | comp {n m} : Primrec n → (Fin n → Primrec m) → Primrec m
  | prec {n} : Primrec n → Primrec (n + 2) → Primrec (n + 1)

namespace Primrec

variable {n m : Nat}

/-- Lift a nullary expression to any arity, ignoring all arguments. -/
def comp₀ (f : Primrec 0) : Primrec n :=
  comp f Fin.elim0

/-- Compose a unary expression with one expression of arity `n`. -/
def comp₁ (f : Primrec 1) (g : Primrec n) : Primrec n :=
  comp f (Fin.cases g Fin.elim0)

/-- Compose a binary expression with arguments `g₁`, `g₂`, in that order. -/
def comp₂ (f : Primrec 2) (g₁ g₂ : Primrec n) : Primrec n :=
  comp f (Fin.cases g₁ (Fin.cases g₂ Fin.elim0))

/-- Compose a ternary expression with arguments `g₁`, `g₂`, `g₃`, in that order. -/
def comp₃ (f : Primrec 3) (g₁ g₂ g₃ : Primrec n) : Primrec n :=
  comp f (Fin.cases g₁ (Fin.cases g₂ (Fin.cases g₃ Fin.elim0)))

/-- A nullary numeral, constructed by iterating successor on zero. -/
def const : Nat → Primrec 0
  | 0 => zero
  | c + 1 => comp₁ succ (const c)

/-- The numeral `c` as an expression of arity `n`, ignoring all arguments. -/
def const' (n c : Nat) : Primrec n :=
  comp₀ (const c)

/-- The unary identity expression. -/
def id : Primrec 1 :=
  proj 0

/-- Project the first argument, with any number of additional arguments. -/
def proj₀ : Primrec (n + 1) :=
  proj 0

/-- Project the second argument, with any number of additional arguments. -/
def proj₁ : Primrec (n + 2) :=
  proj 1

/-- Project the third argument, with any number of additional arguments. -/
def proj₂ : Primrec (n + 3) :=
  proj 2

/-- Replace argument `i` of `f` by argument `ρ i`. This permits permutation, duplication, and
omission of arguments. -/
def reindex (f : Primrec n) (ρ : Fin n → Fin m) : Primrec m :=
  comp f (fun i => proj (ρ i))

/-- Add an unused first argument, shifting all original arguments by one. -/
def weaken (f : Primrec n) : Primrec (n + 1) :=
  reindex f Fin.succ

/-- Exchange the two arguments of a binary expression. -/
def swap (f : Primrec 2) : Primrec 2 :=
  comp₂ f proj₁ proj₀

/-- Case distinction on the first argument. The zero branch `f` receives only the parameters; the
successor branch `g` receives the predecessor followed by the parameters. The recursive result is
ignored. -/
def cases (f : Primrec n) (g : Primrec (n + 1)) : Primrec (n + 1) :=
  prec f (reindex g (Fin.cases 0 (fun i => Fin.succ (Fin.succ i))))

end Primrec

namespace PRA

/-! ## Terms -/

/-- Terms in PRA with `n` available variables. -/
inductive Term : Nat → Type
  /-- A variable. -/
  | var {n} : Fin n → Term n
  /-- A primitive recursive function application. -/
  | app {n m} : Primrec n → (Fin n → Term m) → Term m

/-- Apply a nullary primitive recursive expression. -/
def Term.app₀ {n} (f : Primrec 0) : Term n :=
  .app f Fin.elim0

/-- Apply a unary primitive recursive expression to a term. -/
def Term.app₁ {n} (f : Primrec 1) (t : Term n) : Term n :=
  .app f (Fin.cases t Fin.elim0)

/-- Apply a binary primitive recursive expression to two terms. -/
def Term.app₂ {n} (f : Primrec 2) (t₁ t₂ : Term n) : Term n :=
  .app f (Fin.cases t₁ (Fin.cases t₂ Fin.elim0))

/-- Apply a ternary primitive recursive expression to three terms. -/
def Term.app₃ {n} (f : Primrec 3) (t₁ t₂ t₃ : Term n) : Term n :=
  .app f (Fin.cases t₁ (Fin.cases t₂ (Fin.cases t₃ Fin.elim0)))

/-- Apply the successor symbol to a term. -/
def Term.succ {n} (t : Term n) : Term n :=
  .app₁ .succ t

instance {c n} : OfNat (Term n) c := ⟨.app₀ (.const c)⟩

/-- Simultaneously replace each variable by the term assigned to it. -/
def Term.subst : ∀ {n m}, Term n → (Fin n → Term m) → Term m
  | _, _, .var i, v => v i
  | _, _, .app f v, w => .app f fun i => subst (v i) w

/-- Add an unused variable at position zero, increasing every variable index by one. -/
def Term.shift {n} (t : Term n) : Term (n + 1) :=
  t.subst (Term.var ∘ Fin.succ)

/-- Replace variable zero by `t'` and lower every remaining variable index by one. -/
def Term.inst {n} (t : Term (n + 1)) (t' : Term n) : Term n :=
  t.subst (Fin.cases t' Term.var)

/-! ## Quantifier-free formulas -/

/-- Quantifier-free formulas in PRA with `n` available variables. -/
inductive QFFormula (n : Nat) : Type
  | false : QFFormula n
  | eq : Term n → Term n → QFFormula n
  | imp : QFFormula n → QFFormula n → QFFormula n
  | and : QFFormula n → QFFormula n → QFFormula n
  | or : QFFormula n → QFFormula n → QFFormula n

namespace QFFormula

scoped notation "⊥" => false

scoped infix:60 " ≡ " => eq

scoped infixr:51 " ⇒ " => imp

scoped infixr:53 " ⊓ " => and

scoped infixr:52 " ⊔ " => or

/-- Negation of a quantifier-free formula, defined as implication into falsity. -/
def neg {n} (φ : QFFormula n) :=
  φ ⇒ ⊥

scoped prefix:max "∼ " => neg

/-- Truth as a quantifier-free formula, defined as negated falsity. -/
def true {n} : QFFormula n :=
  ∼ ⊥

scoped notation "⊤" => true

/-- Bi-implication of quantifier-free formulas. -/
def iff {n} (φ ψ : QFFormula n) : QFFormula n :=
  (φ ⇒ ψ) ⊓ (ψ ⇒ φ)

scoped infix:51 " ⇔ " => iff

/-- Simultaneously substitute terms for the free variables of a quantifier-free formula. -/
def subst {n m} : QFFormula n → (Fin n → Term m) → QFFormula m
  | ⊥, _ => ⊥
  | t₁ ≡ t₂, v => t₁.subst v ≡ t₂.subst v
  | φ ⇒ ψ, v => φ.subst v ⇒ ψ.subst v
  | φ ⊓ ψ, v => φ.subst v ⊓ ψ.subst v
  | φ ⊔ ψ, v => φ.subst v ⊔ ψ.subst v

/-- Add an unused free variable at position zero, shifting the existing free variables by one. -/
def shift {n} (φ : QFFormula n) : QFFormula (n + 1) :=
  subst φ (Term.var ∘ Fin.succ)

/-- Replace free variable zero by `t` and lower the remaining free variable indices by one. -/
def inst {n} (φ : QFFormula (n + 1)) (t : Term n) : QFFormula n :=
  subst φ (Fin.cases t Term.var)

/-- Replace free variable zero by `t`, preserving the indices of the remaining free variables. -/
def replace {n} (φ : QFFormula (n + 1)) (t : Term (n + 1)) : QFFormula (n + 1) :=
  subst φ (Fin.cases t (Term.var ∘ Fin.succ))

end QFFormula

/-! ## Quantified formulas -/

/-- Quantified formulas in PRA with `n` available variables. -/
inductive Formula : Nat → Type
  | false {n} : Formula n
  | eq {n} : Term n → Term n → Formula n
  | imp {n} : Formula n → Formula n → Formula n
  | and {n} : Formula n → Formula n → Formula n
  | or {n} : Formula n → Formula n → Formula n
  | all {n} : Formula (n + 1) → Formula n
  | ex {n} : Formula (n + 1) → Formula n

namespace Formula

scoped notation "⊥" => false

scoped infix:60 " ≡ " => eq

scoped infixr:51 " ⇒ " => imp

scoped infixr:53 " ⊓ " => and

scoped infixr:52 " ⊔ " => or

scoped prefix:max "∀' " => all

scoped prefix:max "∃' " => ex

/-- Negation of a formula, defined as implication into falsity. -/
def neg {n} (φ : Formula n) :=
  φ ⇒ ⊥

scoped prefix:max "∼ " => neg

/-- Truth, defined as negated falsity. -/
def true {n} : Formula n :=
  ∼ ⊥

scoped notation "⊤" => true

/-- Bi-implication of formulas. -/
def iff {n} (φ ψ : Formula n) : Formula n :=
  (φ ⇒ ψ) ⊓ (ψ ⇒ φ)

scoped infix:51 " ⇔ " => iff

/-- Whether a formula contains no quantifiers. -/
def QuantifierFree {n} : Formula n → Prop
  | ⊥ | _ ≡ _ => True
  | φ ⇒ ψ | φ ⊓ ψ | φ ⊔ ψ => φ.QuantifierFree ∧ ψ.QuantifierFree
  | ∀' _ | ∃' _ => False

/-- Simultaneously substitute terms for free variables, preserving variable zero under each binder
and shifting the substituted terms to avoid capture. -/
def subst {n m} : Formula n → (Fin n → Term m) → Formula m
  | ⊥, _ => ⊥
  | t₁ ≡ t₂, v => t₁.subst v ≡ t₂.subst v
  | φ ⇒ ψ, v => φ.subst v ⇒ ψ.subst v
  | φ ⊓ ψ, v => φ.subst v ⊓ ψ.subst v
  | φ ⊔ ψ, v => φ.subst v ⊔ ψ.subst v
  | ∀' φ, v => ∀' (φ.subst (Fin.cases (.var 0) fun i => (v i).shift))
  | ∃' φ, v => ∃' (φ.subst (Fin.cases (.var 0) fun i => (v i).shift))

/-- Add an unused free variable at position zero, shifting the existing free variables by one. -/
def shift {n} (φ : Formula n) : Formula (n + 1) :=
  subst φ (Term.var ∘ Fin.succ)

/-- Replace free variable zero by `t` and lower the remaining free variable indices by one. -/
def inst {n} (φ : Formula (n + 1)) (t : Term n) : Formula n :=
  subst φ (Fin.cases t Term.var)

/-- Replace free variable zero by `t`, preserving the indices of the remaining free variables. -/
def replace {n} (φ : Formula (n + 1)) (t : Term (n + 1)) : Formula (n + 1) :=
  subst φ (Fin.cases t (Term.var ∘ Fin.succ))

end Formula

open QFFormula Formula in
/-- Embed a quantifier-free formula into the quantified formula syntax. -/
def QFFormula.toFormula {n} : QFFormula n → Formula n
  | ⊥ => ⊥
  | t₁ ≡ t₂ => t₁ ≡ t₂
  | φ ⇒ ψ => φ.toFormula ⇒ ψ.toFormula
  | φ ⊓ ψ => φ.toFormula ⊓ ψ.toFormula
  | φ ⊔ ψ => φ.toFormula ⊔ ψ.toFormula

end PRA

namespace PRA

open Formula

/-- Classical first-order PRA. Quantifier rules express their variable side conditions through
`Formula.shift`. Induction applies only to formulas satisfying `Formula.QuantifierFree`. -/
inductive Proof : ∀ {n}, Formula n → Prop
  | imp_imp_self {n} {φ ψ : Formula n} :
    Proof (φ ⇒ ψ ⇒ φ)
  | imp_distrib {n} {φ ψ χ : Formula n} :
    Proof ((φ ⇒ ψ ⇒ χ) ⇒ (φ ⇒ ψ) ⇒ φ ⇒ χ)
  | imp_contra {n} {φ ψ : Formula n} :
    Proof ((∼ φ ⇒ ∼ ψ) ⇒ ψ ⇒ φ)
  | and_intro {n} {φ ψ : Formula n} :
    Proof (φ ⇒ ψ ⇒ φ ⊓ ψ)
  | and_left {n} {φ ψ : Formula n} :
    Proof (φ ⊓ ψ ⇒ φ)
  | and_right {n} {φ ψ : Formula n} :
    Proof (φ ⊓ ψ ⇒ ψ)
  | or_left {n} {φ ψ : Formula n} :
    Proof (φ ⇒ φ ⊔ ψ)
  | or_right {n} {φ ψ : Formula n} :
    Proof (ψ ⇒ φ ⊔ ψ)
  | or_elim {n} {φ ψ χ : Formula n} :
    Proof ((φ ⇒ χ) ⇒ (ψ ⇒ χ) ⇒ φ ⊔ ψ ⇒ χ)
  | mp {n} {φ ψ : Formula n} :
    Proof (φ ⇒ ψ)
    → Proof φ
    → Proof ψ
  | forall_elim {n} {φ : Formula (n + 1)} {t : Term n} :
    Proof (∀' φ ⇒ φ.inst t)
  | forall_imp {n} {φ : Formula n} {ψ : Formula (n + 1)} :
    Proof (∀' (φ.shift ⇒ ψ) ⇒ φ ⇒ ∀' ψ)
  | exists_intro {n} {φ : Formula (n + 1)} {t : Term n} :
    Proof (φ.inst t ⇒ ∃' φ)
  | exists_elim {n} {φ : Formula (n + 1)} {ψ : Formula n} :
    Proof (∀' (φ ⇒ ψ.shift) ⇒ ∃' φ ⇒ ψ)
  | gen {n} {φ : Formula (n + 1)} :
    Proof φ
    → Proof (∀' φ)
  | eq_refl {n} {t : Term n} :
    Proof (t ≡ t)
  | eq_symm {n} {t₁ t₂ : Term n} :
    Proof (t₁ ≡ t₂ ⇒ t₂ ≡ t₁)
  | eq_trans {n} {t₁ t₂ t₃ : Term n} :
    Proof (t₁ ≡ t₂ ⇒ t₂ ≡ t₃ ⇒ t₁ ≡ t₃)
  | eq_congr_ith {n m} {f : Primrec m} {v : Fin m → Term n} {i : Fin m} {t : Term n} :
    Proof (v i ≡ t ⇒ .app f v ≡ .app f (fun j => if j = i then t else v j))
  | succ_ne_zero {n} {t : Term n} :
    Proof (∼ (.succ t ≡ 0))
  | succ_inj {t₁ t₂} :
    Proof (.succ t₁ ≡ .succ t₂ ⇒ t₁ ≡ t₂)
  | app_proj {n m i} {v : Fin m → Term n} :
    Proof (.app (.proj i) v ≡ v i)
  | app_comp {m k} {f : Primrec m} {g : Fin m → Primrec k} {v} :
    Proof (.app (.comp f g) v ≡ .app f fun i => .app (g i) v)
  | app_prec_zero {n m} {f : Primrec m} {g} {v : Fin m → Term n} :
    Proof (.app (.prec f g) (Fin.cases 0 v) ≡ .app f v)
  | app_prec_succ {n m} {f : Primrec m} {g} {t} {v : Fin m → Term n} :
    Proof (.app (.prec f g) (Fin.cases (.succ t) v)
      ≡ .app g (Fin.cases t (Fin.cases (.app (.prec f g) (Fin.cases t v)) v)))
  | induction {n} {φ : Formula (n + 1)} (hφ : φ.QuantifierFree) :
    Proof (φ.inst 0 ⇒ ∀' (φ ⇒ φ.replace (.succ (.var 0))) ⇒ ∀' φ)

end PRA

namespace PRA

open QFFormula

/-- Classical quantifier-free PRA. Induction derives the open formula from its zero case and
successor implication. Simultaneous term substitution is an explicit rule. -/
inductive QFProof : ∀ {n}, QFFormula n → Prop
  | imp_imp_self {n} {φ ψ : QFFormula n} :
    QFProof (φ ⇒ ψ ⇒ φ)
  | imp_distrib {n} {φ ψ χ : QFFormula n} :
    QFProof ((φ ⇒ ψ ⇒ χ) ⇒ (φ ⇒ ψ) ⇒ φ ⇒ χ)
  | imp_contra {n} {φ ψ : QFFormula n} :
    QFProof ((∼ φ ⇒ ∼ ψ) ⇒ ψ ⇒ φ)
  | and_intro {n} {φ ψ : QFFormula n} :
    QFProof (φ ⇒ ψ ⇒ φ ⊓ ψ)
  | and_left {n} {φ ψ : QFFormula n} :
    QFProof (φ ⊓ ψ ⇒ φ)
  | and_right {n} {φ ψ : QFFormula n} :
    QFProof (φ ⊓ ψ ⇒ ψ)
  | or_left {n} {φ ψ : QFFormula n} :
    QFProof (φ ⇒ φ ⊔ ψ)
  | or_right {n} {φ ψ : QFFormula n} :
    QFProof (ψ ⇒ φ ⊔ ψ)
  | or_elim {n} {φ ψ χ : QFFormula n} :
    QFProof ((φ ⇒ χ) ⇒ (ψ ⇒ χ) ⇒ φ ⊔ ψ ⇒ χ)
  | mp {n} {φ ψ : QFFormula n} :
    QFProof (φ ⇒ ψ)
    → QFProof φ
    → QFProof ψ
  | eq_refl {n} {t : Term n} :
    QFProof (t ≡ t)
  | eq_symm {n} {t₁ t₂ : Term n} :
    QFProof (t₁ ≡ t₂ ⇒ t₂ ≡ t₁)
  | eq_trans {n} {t₁ t₂ t₃ : Term n} :
    QFProof (t₁ ≡ t₂ ⇒ t₂ ≡ t₃ ⇒ t₁ ≡ t₃)
  | eq_congr_ith {n m} {f : Primrec m} {v : Fin m → Term n} {i : Fin m} {t : Term n} :
    QFProof (v i ≡ t ⇒ .app f v ≡ .app f (fun j => if j = i then t else v j))
  | succ_ne_zero {n} {t : Term n} :
    QFProof (∼ (.succ t ≡ 0))
  | succ_inj {t₁ t₂} :
    QFProof (.succ t₁ ≡ .succ t₂ ⇒ t₁ ≡ t₂)
  | app_proj {n m i} {v : Fin m → Term n} :
    QFProof (.app (.proj i) v ≡ v i)
  | app_comp {m k} {f : Primrec m} {g : Fin m → Primrec k} {v} :
    QFProof (.app (.comp f g) v ≡ .app f fun i => .app (g i) v)
  | app_prec_zero {n m} {f : Primrec m} {g} {v : Fin m → Term n} :
    QFProof (.app (.prec f g) (Fin.cases 0 v) ≡ .app f v)
  | app_prec_succ {n m} {f : Primrec m} {g} {t} {v : Fin m → Term n} :
    QFProof (.app (.prec f g) (Fin.cases (.succ t) v)
      ≡ .app g (Fin.cases t (Fin.cases (.app (.prec f g) (Fin.cases t v)) v)))
  | induction {n} {φ : QFFormula (n + 1)} :
    QFProof (φ.inst 0)
    → QFProof (φ ⇒ φ.replace (.succ (.var 0)))
    → QFProof φ
  | subst {n m} {φ : QFFormula m} {v : Fin m → Term n} :
    QFProof φ
    → QFProof (φ.subst v)

/-- Intuitionistic quantifier-free PRA. Its propositional rules include falsity elimination;
its equality, primitive recursion, induction, and substitution rules agree with `QFProof`. -/
inductive QFProofI : ∀ {n}, QFFormula n → Prop
  | imp_imp_self {n} {φ ψ : QFFormula n} :
    QFProofI (φ ⇒ ψ ⇒ φ)
  | imp_distrib {n} {φ ψ χ : QFFormula n} :
    QFProofI ((φ ⇒ ψ ⇒ χ) ⇒ (φ ⇒ ψ) ⇒ φ ⇒ χ)
  | false_elim {n} {φ : QFFormula n} :
    QFProofI (⊥ ⇒ φ)
  | and_intro {n} {φ ψ : QFFormula n} :
    QFProofI (φ ⇒ ψ ⇒ φ ⊓ ψ)
  | and_left {n} {φ ψ : QFFormula n} :
    QFProofI (φ ⊓ ψ ⇒ φ)
  | and_right {n} {φ ψ : QFFormula n} :
    QFProofI (φ ⊓ ψ ⇒ ψ)
  | or_left {n} {φ ψ : QFFormula n} :
    QFProofI (φ ⇒ φ ⊔ ψ)
  | or_right {n} {φ ψ : QFFormula n} :
    QFProofI (ψ ⇒ φ ⊔ ψ)
  | or_elim {n} {φ ψ χ : QFFormula n} :
    QFProofI ((φ ⇒ χ) ⇒ (ψ ⇒ χ) ⇒ φ ⊔ ψ ⇒ χ)
  | mp {n} {φ ψ : QFFormula n} :
    QFProofI (φ ⇒ ψ)
    → QFProofI φ
    → QFProofI ψ
  | eq_refl {n} {t : Term n} :
    QFProofI (t ≡ t)
  | eq_symm {n} {t₁ t₂ : Term n} :
    QFProofI (t₁ ≡ t₂ ⇒ t₂ ≡ t₁)
  | eq_trans {n} {t₁ t₂ t₃ : Term n} :
    QFProofI (t₁ ≡ t₂ ⇒ t₂ ≡ t₃ ⇒ t₁ ≡ t₃)
  | eq_congr_ith {n m} {f : Primrec m} {v : Fin m → Term n} {i : Fin m} {t : Term n} :
    QFProofI (v i ≡ t ⇒ .app f v ≡ .app f (fun j => if j = i then t else v j))
  | succ_ne_zero {n} {t : Term n} :
    QFProofI (∼ (.succ t ≡ 0))
  | succ_inj {t₁ t₂} :
    QFProofI (.succ t₁ ≡ .succ t₂ ⇒ t₁ ≡ t₂)
  | app_proj {n m i} {v : Fin m → Term n} :
    QFProofI (.app (.proj i) v ≡ v i)
  | app_comp {m k} {f : Primrec m} {g : Fin m → Primrec k} {v} :
    QFProofI (.app (.comp f g) v ≡ .app f fun i => .app (g i) v)
  | app_prec_zero {n m} {f : Primrec m} {g} {v : Fin m → Term n} :
    QFProofI (.app (.prec f g) (Fin.cases 0 v) ≡ .app f v)
  | app_prec_succ {n m} {f : Primrec m} {g} {t} {v : Fin m → Term n} :
    QFProofI (.app (.prec f g) (Fin.cases (.succ t) v)
      ≡ .app g (Fin.cases t (Fin.cases (.app (.prec f g) (Fin.cases t v)) v)))
  | induction {n} {φ : QFFormula (n + 1)} :
    QFProofI (φ.inst 0)
    → QFProofI (φ ⇒ φ.replace (.succ (.var 0)))
    → QFProofI φ
  | subst {n m} {φ : QFFormula m} {v : Fin m → Term n} :
    QFProofI φ
    → QFProofI (φ.subst v)

end PRA
