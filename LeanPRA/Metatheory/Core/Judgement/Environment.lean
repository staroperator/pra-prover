module

public import LeanPRA.Metatheory.Core.Judgement.Defs
import Std.Data.ExtHashMap.Lemmas

/-!
# Global environments and declarative judgements

- `EnvironmentExtends.insert` describes fresh insertion while preserving earlier lookups.
- `TermTyping.weakenEnvironment` and its counterparts preserve all judgements under extension.
- `ProofTyping.environmentEquiv` and its counterparts transport judgements along map equality.
- `EnvironmentWF.lookup` gives a declaration's name and well-formedness in the final map.
- `EnvironmentWF.of_lookup_eq` derives validity transfer from equality of all global lookups.
- `DeclarationsWF.valid` propagates validity through an ordered declaration list.

Extension theorems apply to existing derivations over any larger map that preserves their lookups.
Valid lookup uses the construction history in `EnvironmentWF`, then weakens the original
declaration derivation into the final map.
-/

namespace LeanPRA.Core.Theory

private theorem extends_refl (E : Environment) : EnvironmentExtends E E := by
  intro name d h
  exact h

private theorem extends_trans {E F G} (h : EnvironmentExtends E F)
    (g : EnvironmentExtends F G) : EnvironmentExtends E G := by
  intro name d lookup
  exact g name d (h name d lookup)

private theorem extends_insert {E : Environment} {d : Declaration}
    (fresh : E[d.name]? = none) : EnvironmentExtends E (E.insert d.name d) := by
  intro name e lookup
  by_cases heq : d.name = name
  · subst name
    rw [fresh] at lookup
    contradiction
  · simpa [Std.ExtHashMap.getElem?_insert, heq] using lookup

private theorem term_weaken {E Ξ Γ t k} (h : TermTyping E Ξ Γ t k)
    {F} (ext : EnvironmentExtends E F) : TermTyping F Ξ Γ t k := by
  induction h using TermTyping.rec
    (motive_2 := fun Γ fs ks _ => FunctionArguments F Ξ Γ fs ks) with
  | bvar lookup => exact .bvar lookup
  | parameter lookup => exact .parameter lookup
  | zero => exact .zero
  | succ => exact .succ
  | lam body ih => exact .lam ih
  | app f a ihf iha => exact .app ihf iha
  | letE a t iha iht => exact .letE iha iht
  | primrec b s ihb ihs => exact .primrec ihb ihs
  | definition lookup args ih => exact .definition (ext _ _ lookup) ih
  | nil => exact .nil
  | cons head tail ihh iht => exact .cons ihh iht

private theorem functions_weaken {E Ξ Γ fs ks} (h : FunctionArguments E Ξ Γ fs ks)
    {F} (ext : EnvironmentExtends E F) : FunctionArguments F Ξ Γ fs ks := by
  induction h using FunctionArguments.rec (motive_1 := fun _ _ _ _ => True)
  case nil => exact .nil
  case cons head tail ihh iht => exact .cons (term_weaken head ext) iht
  all_goals trivial

private theorem predicate_weaken {E Ξ Γ P σ} (h : PredicateTyping E Ξ Γ P σ)
    {F} (ext : EnvironmentExtends E F) : PredicateTyping F Ξ Γ P σ := by
  induction h using PredicateTyping.rec
    (motive_2 := fun Γ ps signatures _ => PredicateArguments F Ξ Γ ps signatures) with
  | false => exact .false
  | true => exact .true
  | equal a b => exact .equal (term_weaken a ext) (term_weaken b ext)
  | imp A B ihA ihB => exact .imp ihA ihB
  | and A B ihA ihB => exact .and ihA ihB
  | or A B ihA ihB => exact .or ihA ihB
  | all P ih => exact .all ih
  | ex P ih => exact .ex ih
  | parameter lookup => exact .parameter lookup
  | lam P ih => exact .lam ih
  | app P a ih => exact .app ih (term_weaken a ext)
  | letTerm a P ih => exact .letTerm (term_weaken a ext) ih
  | letPredicate Q P ihQ ihP => exact .letPredicate ihQ ihP
  | definition lookup functions predicates ihp =>
      exact .definition (ext _ _ lookup) (functions_weaken functions ext) ihp
  | subsumption h sub ih => exact .subsumption ih sub
  | nil => exact .nil
  | cons head tail ihh iht => exact .cons ihh iht

private theorem predicates_weaken {E Ξ Γ ps signatures}
    (h : PredicateArguments E Ξ Γ ps signatures) {F} (ext : EnvironmentExtends E F) :
    PredicateArguments F Ξ Γ ps signatures := by
  induction h using PredicateArguments.rec (motive_1 := fun _ _ _ _ => True)
  case nil => exact .nil
  case cons head tail ihh iht => exact .cons (predicate_weaken head ext) iht
  all_goals trivial

private theorem term_eq_weaken {E Ξ Γ t u k} (h : TermEq E Ξ Γ t u k)
    {F} (ext : EnvironmentExtends E F) : TermEq F Ξ Γ t u k := by
  induction h using TermEq.rec
    (motive_2 := fun Γ fs gs ks _ => FunctionArgumentEq F Ξ Γ fs gs ks) with
  | refl typing => exact .refl (term_weaken typing ext)
  | symm h ih => exact .symm ih
  | trans h g ihh ihg => exact .trans ihh ihg
  | beta body arg => exact .beta (term_weaken body ext) (term_weaken arg ext)
  | eta function => exact .eta (term_weaken function ext)
  | zeta value body => exact .zeta (term_weaken value ext) (term_weaken body ext)
  | delta lookup args body =>
      exact .delta (ext _ _ lookup) (functions_weaken args ext) (term_weaken body ext)
  | primrecZero base step => exact .primrecZero (term_weaken base ext) (term_weaken step ext)
  | primrecSucc base step arg =>
      exact .primrecSucc (term_weaken base ext) (term_weaken step ext) (term_weaken arg ext)
  | lam body ih => exact .lam ih
  | app f a ihf iha => exact .app ihf iha
  | letE a body iha ihb => exact .letE iha ihb
  | primrec b s ihb ihs => exact .primrec ihb ihs
  | definition lookup args ih => exact .definition (ext _ _ lookup) ih
  | nil => exact .nil
  | cons head tail ihh iht => exact .cons ihh iht

private theorem function_eq_weaken {E Ξ Γ fs gs ks} (h : FunctionArgumentEq E Ξ Γ fs gs ks)
    {F} (ext : EnvironmentExtends E F) : FunctionArgumentEq F Ξ Γ fs gs ks := by
  induction h using FunctionArgumentEq.rec (motive_1 := fun _ _ _ _ _ => True)
  case nil => exact .nil
  case cons head tail ihh iht => exact .cons (term_eq_weaken head ext) iht
  all_goals trivial

private theorem predicate_eq_weaken {E Ξ Γ P Q σ} (h : PredicateEq E Ξ Γ P Q σ)
    {F} (ext : EnvironmentExtends E F) : PredicateEq F Ξ Γ P Q σ := by
  induction h using PredicateEq.rec
    (motive_2 := fun Γ ps qs signatures _ => PredicateArgumentEq F Ξ Γ ps qs signatures) with
  | refl typing => exact .refl (predicate_weaken typing ext)
  | symm h ih => exact .symm ih
  | trans h g ihh ihg => exact .trans ihh ihg
  | subsumption h sub ih => exact .subsumption ih sub
  | beta body arg => exact .beta (predicate_weaken body ext) (term_weaken arg ext)
  | eta function => exact .eta (predicate_weaken function ext)
  | zetaTerm a P => exact .zetaTerm (term_weaken a ext) (predicate_weaken P ext)
  | zetaPredicate Q P => exact .zetaPredicate (predicate_weaken Q ext) (predicate_weaken P ext)
  | delta lookup functions predicates body bound =>
      exact .delta (ext _ _ lookup) (functions_weaken functions ext)
        (predicates_weaken predicates ext) (predicate_weaken body ext) bound
  | equal a b => exact .equal (term_eq_weaken a ext) (term_eq_weaken b ext)
  | imp A B ihA ihB => exact .imp ihA ihB
  | and A B ihA ihB => exact .and ihA ihB
  | or A B ihA ihB => exact .or ihA ihB
  | all P ih => exact .all ih
  | ex P ih => exact .ex ih
  | lam P ih => exact .lam ih
  | app P a ih => exact .app ih (term_eq_weaken a ext)
  | definition lookup functions predicates left right ih =>
      exact .definition (ext _ _ lookup) (function_eq_weaken functions ext) ih
        (predicate_weaken left ext) (predicate_weaken right ext)
  | nil => exact .nil
  | cons head tail ihh iht => exact .cons ihh iht

private theorem proof_weaken {E Ξ Γ H p A} (h : ProofTyping E Ξ Γ H p A)
    {F} (ext : EnvironmentExtends E F) : ProofTyping F Ξ Γ H p A := by
  induction h with
  | hyp lookup => exact .hyp lookup
  | trueIntro => exact .trueIntro
  | theoremE lookup functions predicates =>
      exact .theoremE (ext _ _ lookup) (functions_weaken functions ext)
        (predicates_weaken predicates ext)
  | impIntro A body ih => exact .impIntro (predicate_weaken A ext) ih
  | impElim p q ihp ihq => exact .impElim ihp ihq
  | andIntro p q ihp ihq => exact .andIntro ihp ihq
  | andLeft a b => exact .andLeft (predicate_weaken a ext) (predicate_weaken b ext)
  | andRight a b => exact .andRight (predicate_weaken a ext) (predicate_weaken b ext)
  | orLeft a b => exact .orLeft (predicate_weaken a ext) (predicate_weaken b ext)
  | orRight a b => exact .orRight (predicate_weaken a ext) (predicate_weaken b ext)
  | orElim a b c =>
      exact .orElim (predicate_weaken a ext) (predicate_weaken b ext) (predicate_weaken c ext)
  | falseElim a => exact .falseElim (predicate_weaken a ext)
  | forallIntro P p ih => exact .forallIntro (predicate_weaken P ext) ih
  | forallElim p a ih => exact .forallElim ih (term_weaken a ext)
  | existsIntro P a p ih => exact .existsIntro (predicate_weaken P ext) (term_weaken a ext) ih
  | existsElim a b => exact .existsElim (predicate_weaken a ext) (predicate_weaken b ext)
  | letE A p q ihp ihq => exact .letE (predicate_weaken A ext) ihp ihq
  | letTerm a p ih => exact .letTerm (term_weaken a ext) ih
  | letPredicate P p ih => exact .letPredicate (predicate_weaken P ext) ih
  | ascribe A p ih => exact .ascribe (predicate_weaken A ext) ih
  | eqRefl => exact .eqRefl
  | eqSubst a => exact .eqSubst (predicate_weaken a ext)
  | succNeZero => exact .succNeZero
  | succInj => exact .succInj
  | lem A => exact .lem (predicate_weaken A ext)
  | induction a => exact .induction (predicate_weaken a ext)
  | conversion p type ih => exact .conversion ih (predicate_eq_weaken type ext)

private theorem predicate_list_eq_weaken {E Ξ Γ ps qs signatures}
    (h : PredicateArgumentEq E Ξ Γ ps qs signatures) {F} (ext : EnvironmentExtends E F) :
    PredicateArgumentEq F Ξ Γ ps qs signatures := by
  induction h using PredicateArgumentEq.rec (motive_1 := fun _ _ _ _ _ => True)
  case nil => exact .nil
  case cons head tail ihh iht => exact .cons (predicate_eq_weaken head ext) iht
  all_goals trivial

private theorem context_weaken {E Ξ Γ H} (h : ContextWF E Ξ Γ H)
    {F} (ext : EnvironmentExtends E F) : ContextWF F Ξ Γ H := by
  induction h with
  | nil => exact .nil
  | cons head tail ih => exact .cons (predicate_weaken head ext) ih

private theorem context_eq_weaken {E Ξ Γ H K} (h : ProofContextEq E Ξ Γ H K)
    {F} (ext : EnvironmentExtends E F) : ProofContextEq F Ξ Γ H K := by
  induction h with
  | nil => exact .nil
  | cons head tail ih => exact .cons (predicate_eq_weaken head ext) ih

private theorem declaration_weaken {E d} (h : DeclarationWF E d)
    {F} (ext : EnvironmentExtends E F) : DeclarationWF F d := by
  cases h with
  | function body => exact .function (term_weaken body ext)
  | predicate body => exact .predicate (predicate_weaken body ext)
  | theoremE type body => exact .theoremE (predicate_weaken type ext) (proof_weaken body ext)

private theorem valid_lookup {E} (h : EnvironmentWF E) :
    ∀ (name : Lean.Name) d, E[name]? = some d → d.name = name ∧ DeclarationWF E d := by
  induction h with
  | empty => intro name d lookup; simp at lookup
  | @insert E d valid fresh wellformed ih =>
      intro name e lookup
      have ext := extends_insert fresh
      by_cases heq : d.name = name
      · subst name
        have : d = e := Option.some.inj (by simpa using lookup)
        subst e
        exact ⟨rfl, declaration_weaken wellformed ext⟩
      · have old : E[name]? = some e := by
          simpa [Std.ExtHashMap.getElem?_insert, heq] using lookup
        obtain ⟨hname, hwf⟩ := ih _ _ old
        exact ⟨hname, declaration_weaken hwf ext⟩

/-- Every map preserves its own successful lookups. -/
public theorem EnvironmentExtends.refl (E : Environment) : EnvironmentExtends E E := extends_refl E

/-- Lookup-preserving extensions compose. -/
public theorem EnvironmentExtends.trans {E F G} (h : EnvironmentExtends E F)
    (g : EnvironmentExtends F G) : EnvironmentExtends E G := extends_trans h g

/-- Inserting a fresh declaration preserves all earlier successful lookups. -/
public theorem EnvironmentExtends.insert {E : Environment} {d : Declaration}
    (fresh : E[d.name]? = none) : EnvironmentExtends E (E.insert d.name d) := extends_insert fresh

/-- Term typing is preserved under lookup-preserving environment extension. -/
public theorem TermTyping.weakenEnvironment {E Ξ Γ t k} (h : TermTyping E Ξ Γ t k)
    {F} (ext : EnvironmentExtends E F) : TermTyping F Ξ Γ t k := term_weaken h ext

/-- Complete function actual lists remain typed in an extending map. -/
public theorem FunctionArguments.weakenEnvironment {E Ξ Γ fs ks}
    (h : FunctionArguments E Ξ Γ fs ks) {F} (ext : EnvironmentExtends E F) :
    FunctionArguments F Ξ Γ fs ks := functions_weaken h ext

/-- Predicate typing at its full signature is preserved in an extending map. -/
public theorem PredicateTyping.weakenEnvironment {E Ξ Γ P σ} (h : PredicateTyping E Ξ Γ P σ)
    {F} (ext : EnvironmentExtends E F) : PredicateTyping F Ξ Γ P σ := predicate_weaken h ext

/-- Complete predicate actual lists remain typed in an extending map. -/
public theorem PredicateArguments.weakenEnvironment {E Ξ Γ ps signatures}
    (h : PredicateArguments E Ξ Γ ps signatures) {F} (ext : EnvironmentExtends E F) :
    PredicateArguments F Ξ Γ ps signatures := predicates_weaken h ext

/-- Typed computational equality is preserved in an extending map. -/
public theorem TermEq.weakenEnvironment {E Ξ Γ t u k} (h : TermEq E Ξ Γ t u k)
    {F} (ext : EnvironmentExtends E F) : TermEq F Ξ Γ t u k := term_eq_weaken h ext

/-- Equality of function actual lists is preserved in an extending map. -/
public theorem FunctionArgumentEq.weakenEnvironment {E Ξ Γ fs gs ks}
    (h : FunctionArgumentEq E Ξ Γ fs gs ks) {F} (ext : EnvironmentExtends E F) :
    FunctionArgumentEq F Ξ Γ fs gs ks := function_eq_weaken h ext

/-- Typed predicate equality is preserved in an extending map. -/
public theorem PredicateEq.weakenEnvironment {E Ξ Γ P Q σ} (h : PredicateEq E Ξ Γ P Q σ)
    {F} (ext : EnvironmentExtends E F) : PredicateEq F Ξ Γ P Q σ := predicate_eq_weaken h ext

/-- Predicate-actual equality is preserved in an extending map. -/
public theorem PredicateArgumentEq.weakenEnvironment {E Ξ Γ ps qs signatures}
    (h : PredicateArgumentEq E Ξ Γ ps qs signatures) {F} (ext : EnvironmentExtends E F) :
    PredicateArgumentEq F Ξ Γ ps qs signatures := predicate_list_eq_weaken h ext

/-- Formed assumptions remain formed in an extending map. -/
public theorem ContextWF.weakenEnvironment {E Ξ Γ H} (h : ContextWF E Ξ Γ H)
    {F} (ext : EnvironmentExtends E F) : ContextWF F Ξ Γ H := context_weaken h ext

/-- Conversion of assumptions is preserved in an extending map. -/
public theorem ProofContextEq.weakenEnvironment {E Ξ Γ H K} (h : ProofContextEq E Ξ Γ H K)
    {F} (ext : EnvironmentExtends E F) : ProofContextEq F Ξ Γ H K := context_eq_weaken h ext

/-- Proof typing is preserved in an extending map, with the same proof data and conclusion. -/
public theorem ProofTyping.weakenEnvironment {E Ξ Γ H p A} (h : ProofTyping E Ξ Γ H p A)
    {F} (ext : EnvironmentExtends E F) : ProofTyping F Ξ Γ H p A := proof_weaken h ext

/-- Declaration validity is preserved when the preceding environment extends. -/
public theorem DeclarationWF.weakenEnvironment {E d} (h : DeclarationWF E d)
    {F} (ext : EnvironmentExtends E F) : DeclarationWF F d := declaration_weaken h ext

/-- Every declaration in a valid map has its own key as name and is well formed in that map. -/
public theorem EnvironmentWF.lookup {E} (h : EnvironmentWF E) {name : Lean.Name} {d}
    (lookup : E[name]? = some d) : d.name = name ∧ DeclarationWF E d := valid_lookup h name d lookup

/-- Equivalent maps validate exactly the same term typings. -/
public theorem TermTyping.environmentEquiv {E F Ξ Γ t k} (eq : E = F) :
    TermTyping E Ξ Γ t k ↔ TermTyping F Ξ Γ t k := by
  cases eq
  rfl

/-- Equivalent maps validate exactly the same full-signature predicate typings. -/
public theorem PredicateTyping.environmentEquiv {E F Ξ Γ P σ} (eq : E = F) :
    PredicateTyping E Ξ Γ P σ ↔ PredicateTyping F Ξ Γ P σ := by
  cases eq
  rfl

/-- Equivalent maps validate exactly the same typed computational equalities. -/
public theorem TermEq.environmentEquiv {E F Ξ Γ t u k} (eq : E = F) :
    TermEq E Ξ Γ t u k ↔ TermEq F Ξ Γ t u k := by
  cases eq
  rfl

/-- Equivalent maps validate exactly the same full-signature predicate equalities. -/
public theorem PredicateEq.environmentEquiv {E F Ξ Γ P Q σ} (eq : E = F) :
    PredicateEq E Ξ Γ P Q σ ↔ PredicateEq F Ξ Γ P Q σ := by
  cases eq
  rfl

/-- Equivalent maps validate exactly the same explicit proof typings. -/
public theorem ProofTyping.environmentEquiv {E F Ξ Γ H p A} (eq : E = F) :
    ProofTyping E Ξ Γ H p A ↔ ProofTyping F Ξ Γ H p A := by
  cases eq
  rfl

/-- Equivalent maps validate the same complete function actual lists. -/
public theorem FunctionArguments.environmentEquiv {E F Ξ Γ fs ks} (eq : E = F) :
    FunctionArguments E Ξ Γ fs ks ↔ FunctionArguments F Ξ Γ fs ks := by
  cases eq
  rfl

/-- Equivalent maps validate the same complete predicate actual lists. -/
public theorem PredicateArguments.environmentEquiv {E F Ξ Γ ps signatures}
    (eq : E = F) :
    PredicateArguments E Ξ Γ ps signatures ↔ PredicateArguments F Ξ Γ ps signatures := by
  cases eq
  rfl

/-- Equivalent maps validate the same function-actual equalities. -/
public theorem FunctionArgumentEq.environmentEquiv {E F Ξ Γ fs gs ks} (eq : E = F) :
    FunctionArgumentEq E Ξ Γ fs gs ks ↔ FunctionArgumentEq F Ξ Γ fs gs ks := by
  cases eq
  rfl

/-- Equivalent maps validate the same predicate-actual equalities. -/
public theorem PredicateArgumentEq.environmentEquiv {E F Ξ Γ ps qs signatures}
    (eq : E = F) :
    PredicateArgumentEq E Ξ Γ ps qs signatures ↔ PredicateArgumentEq F Ξ Γ ps qs signatures := by
  cases eq
  rfl

/-- Formation of proof assumptions is invariant under equality of global lookups. -/
public theorem ContextWF.environmentEquiv {E F Ξ Γ H} (eq : E = F) :
    ContextWF E Ξ Γ H ↔ ContextWF F Ξ Γ H := by
  cases eq
  rfl

/-- Equality of proof assumptions is invariant under equality of global lookups. -/
public theorem ProofContextEq.environmentEquiv {E F Ξ Γ H K} (eq : E = F) :
    ProofContextEq E Ξ Γ H K ↔ ProofContextEq F Ξ Γ H K := by
  cases eq
  rfl

/-- A declaration's well-formedness depends only on the preceding map's lookups. -/
public theorem DeclarationWF.environmentEquiv {E F d} (eq : E = F) :
    DeclarationWF E d ↔ DeclarationWF F d := by
  cases eq
  rfl

/-- Equal global lookups preserve validity by extensional map equality. -/
public theorem EnvironmentWF.of_lookup_eq {E F : Environment} (valid : EnvironmentWF E)
    (lookups : ∀ name : Lean.Name, E[name]? = F[name]?) : EnvironmentWF F := by
  have equality : E = F := Std.ExtHashMap.ext_getElem? lookups
  cases equality
  exact valid

/-- Equal environments satisfy the same validity judgement. -/
public theorem EnvironmentWF.environmentEquiv {E F} (eq : E = F) :
    EnvironmentWF E ↔ EnvironmentWF F := by
  cases eq
  rfl

/-- A valid starting map and an ordered valid declaration list have a valid final map. -/
public theorem DeclarationsWF.valid {E ds F} (h : DeclarationsWF E ds F)
    (valid : EnvironmentWF E) : EnvironmentWF F := by
  induction h with
  | nil => exact valid
  | cons fresh formed tail ih => exact ih (.insert valid fresh formed)

end LeanPRA.Core.Theory
