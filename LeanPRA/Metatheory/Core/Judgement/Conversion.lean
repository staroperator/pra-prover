module

public import LeanPRA.Metatheory.Core.Judgement.Substitution

/-!
# Typed conversion and conversion of assumptions

- `TermEq.regularity` gives term typing for both endpoints of computational conversion.
- `PredicateEq.regularity` gives predicate typing at the displayed full signature.
- `ProofContextEq.regularity` forms both lists of definitionally equal assumptions.
- `ProofTyping.context_conversion` replaces assumptions by definitionally equal formulas.

Predicate regularity requires a valid environment because transparent global bodies must be
locally closed.
-/

namespace LeanPRA.Core.Theory

private theorem subtype_trans {σ τ υ} (h : PredicateSubtyping σ τ)
    (g : PredicateSubtyping τ υ) : PredicateSubtyping σ υ := by
  cases h with
  | refl => exact g
  | lift => cases g with
    | refl => exact .lift

private theorem term_regular {E Ξ Γ t u k} (h : TermEq E Ξ Γ t u k) :
    TermTyping E Ξ Γ t k ∧ TermTyping E Ξ Γ u k := by
  induction h using TermEq.rec
    (motive_2 := fun Γ fs gs ks _ =>
      FunctionArguments E Ξ Γ fs ks ∧ FunctionArguments E Ξ Γ gs ks) with
  | refl typing => exact ⟨typing, typing⟩
  | symm h ih => exact ih.symm
  | trans h g ihh ihg => exact ⟨ihh.1, ihg.2⟩
  | beta body argument => exact ⟨.app (.lam body) argument, TermTyping.subst0 body argument⟩
  | eta function => exact ⟨.lam (.app (TermTyping.shift function 0) (.bvar rfl)), function⟩
  | zeta value body => exact ⟨.letE value body, TermTyping.subst0 body value⟩
  | delta lookup args body => exact ⟨.definition lookup args, body⟩
  | primrecZero base step => exact ⟨.app (.primrec base step) .zero, base⟩
  | primrecSucc base step argument =>
      exact ⟨.app (.primrec base step) (.app .succ argument),
        .app (.app step argument) (.app (.primrec base step) argument)⟩
  | lam body ih => exact ⟨.lam ih.1, .lam ih.2⟩
  | app f a ihf iha => exact ⟨.app ihf.1 iha.1, .app ihf.2 iha.2⟩
  | letE a body iha ihb => exact ⟨.letE iha.1 ihb.1, .letE iha.2 ihb.2⟩
  | primrec b s ihb ihs =>
      exact ⟨.primrec ihb.1 ihs.1, .primrec ihb.2 ihs.2⟩
  | definition lookup args ih => exact ⟨.definition lookup ih.1, .definition lookup ih.2⟩
  | nil => exact ⟨.nil, .nil⟩
  | cons head tail ihh iht => exact ⟨.cons ihh.1 iht.1, .cons ihh.2 iht.2⟩

private theorem predicate_regular {E Ξ Γ P Q σ} (valid : EnvironmentWF E)
    (h : PredicateEq E Ξ Γ P Q σ) : PredicateTyping E Ξ Γ P σ ∧ PredicateTyping E Ξ Γ Q σ := by
  induction h using PredicateEq.rec
    (motive_2 := fun Γ ps qs signatures _ =>
      PredicateArguments E Ξ Γ ps signatures ∧ PredicateArguments E Ξ Γ qs signatures) with
  | refl typing => exact ⟨typing, typing⟩
  | symm h ih => exact ih.symm
  | trans h g ihh ihg => exact ⟨ihh.1, ihg.2⟩
  | subsumption h sub ih => exact ⟨.subsumption ih.1 sub, .subsumption ih.2 sub⟩
  | beta body argument =>
      exact ⟨.app (.lam body) argument, PredicateTyping.subst0 valid body argument⟩
  | eta function =>
      exact ⟨.lam (.app (PredicateTyping.shift valid function 0) (.bvar rfl)), function⟩
  | zetaTerm value body => exact ⟨.letTerm value body, body⟩
  | zetaPredicate value body => exact ⟨.letPredicate value body, body⟩
  | delta lookup functions predicates body bound =>
      exact ⟨.subsumption (.definition lookup functions predicates) bound, body⟩
  | equal a b =>
      exact ⟨.equal (term_regular a).1 (term_regular b).1,
        .equal (term_regular a).2 (term_regular b).2⟩
  | imp A B ihA ihB => exact ⟨.imp ihA.1 ihB.1, .imp ihA.2 ihB.2⟩
  | and A B ihA ihB => exact ⟨.and ihA.1 ihB.1, .and ihA.2 ihB.2⟩
  | or A B ihA ihB => exact ⟨.or ihA.1 ihB.1, .or ihA.2 ihB.2⟩
  | all P ih => exact ⟨.all ih.1, .all ih.2⟩
  | ex P ih => exact ⟨.ex ih.1, .ex ih.2⟩
  | lam P ih => exact ⟨.lam ih.1, .lam ih.2⟩
  | app P a ih => exact ⟨.app ih.1 (term_regular a).1, .app ih.2 (term_regular a).2⟩
  | definition lookup fs ps left right ih => exact ⟨left, right⟩
  | nil => exact ⟨.nil, .nil⟩
  | cons head tail ihh iht => exact ⟨.cons ihh.1 iht.1, .cons ihh.2 iht.2⟩

private theorem arguments_regular {E Ξ Γ fs gs ks} (h : FunctionArgumentEq E Ξ Γ fs gs ks) :
    FunctionArguments E Ξ Γ fs ks ∧ FunctionArguments E Ξ Γ gs ks := by
  induction h using FunctionArgumentEq.rec (motive_1 := fun _ _ _ _ _ => True)
  case nil => exact ⟨.nil, .nil⟩
  case cons head tail ihh iht =>
      exact ⟨.cons (term_regular head).1 iht.1, .cons (term_regular head).2 iht.2⟩
  all_goals trivial

private theorem predicates_regular {E Ξ Γ ps qs signatures} (valid : EnvironmentWF E)
    (h : PredicateArgumentEq E Ξ Γ ps qs signatures) :
    PredicateArguments E Ξ Γ ps signatures ∧ PredicateArguments E Ξ Γ qs signatures := by
  induction h using PredicateArgumentEq.rec (motive_1 := fun _ _ _ _ _ => True)
  case nil => exact ⟨.nil, .nil⟩
  case cons head tail ihh iht =>
      exact ⟨.cons (predicate_regular valid head).1 iht.1,
        .cons (predicate_regular valid head).2 iht.2⟩
  all_goals trivial

private theorem context_lookup {E Ξ Γ H K} (h : ProofContextEq E Ξ Γ H K)
    {i : Nat} {A : Predicate} (lookup : H[i]? = some A) :
    ∃ B, K[i]? = some B ∧ PredicateEq E Ξ Γ A B ⟨0, .prop⟩ := by
  induction h generalizing i with
  | nil => simp at lookup
  | @cons A B H K head tail ih =>
      cases i with
      | zero =>
          have hA := Option.some.inj lookup
          subst hA
          exact ⟨B, rfl, head⟩
      | succ i => exact ih lookup

private abbrev HypothesisConversion (E : Environment) (Ξ : ParameterContext) (Γ : LocalContext)
    (H K : ProofContext) : Prop :=
  ∀ (i : Nat) A, H[i]? = some A →
    ∃ B, K[i]? = some B ∧ (A = B ∨ PredicateEq E Ξ Γ A B ⟨0, .prop⟩)

private theorem hypotheses_cons {E Ξ Γ H K} (h : HypothesisConversion E Ξ Γ H K)
    (A : Predicate) : HypothesisConversion E Ξ Γ (A :: H) (A :: K) := by
  intro i B lookup
  cases i with
  | zero => exact ⟨A, rfl, Or.inl (Option.some.inj lookup).symm⟩
  | succ i => exact h i B lookup

private theorem hypotheses_shift {E Ξ Γ H K} (valid : EnvironmentWF E)
    (h : HypothesisConversion E Ξ Γ H K) :
    HypothesisConversion E Ξ (0 :: Γ) (H.map Predicate.shift) (K.map Predicate.shift) := by
  intro i A lookup
  rw [List.getElem?_map] at lookup
  cases hi : H[i]? with
  | none => simp [hi] at lookup
  | some P =>
      have hA : P.shift = A := Option.some.inj (by simpa [hi] using lookup)
      subst A
      obtain ⟨Q, hQ, heq⟩ := h i P hi
      refine ⟨Q.shift, ?_, ?_⟩
      · simp [List.getElem?_map, hQ]
      · rcases heq with rfl | heq
        · exact Or.inl rfl
        · exact Or.inr (PredicateEq.shift valid heq 0)

private theorem proof_context_conversion {E Ξ Γ H p A} (valid : EnvironmentWF E)
    (h : ProofTyping E Ξ Γ H p A) {K} (hc : HypothesisConversion E Ξ Γ H K) :
    ProofTyping E Ξ Γ K p A := by
  induction h generalizing K with
  | hyp lookup =>
      obtain ⟨B, hB, heq⟩ := hc _ _ lookup
      rcases heq with rfl | heq
      · exact .hyp hB
      · exact .conversion (.hyp hB) (.symm heq)
  | trueIntro => exact .trueIntro
  | theoremE lookup functions predicates => exact .theoremE lookup functions predicates
  | impIntro antecedent body ih => exact .impIntro antecedent (ih (hypotheses_cons hc _))
  | impElim f a ihf iha => exact .impElim (ihf hc) (iha hc)
  | andIntro a b iha ihb => exact .andIntro (iha hc) (ihb hc)
  | andLeft a b => exact .andLeft a b
  | andRight a b => exact .andRight a b
  | orLeft a b => exact .orLeft a b
  | orRight a b => exact .orRight a b
  | orElim a b c => exact .orElim a b c
  | falseElim a => exact .falseElim a
  | forallIntro motive body ih => exact .forallIntro motive (ih (hypotheses_shift valid hc))
  | forallElim proof argument ih => exact .forallElim (ih hc) argument
  | existsIntro motive witness proof ih => exact .existsIntro motive witness (ih hc)
  | existsElim a b => exact .existsElim a b
  | letE type value body ihv ihb => exact .letE type (ihv hc) (ihb (hypotheses_cons hc _))
  | letTerm value body ih => exact .letTerm value (ih hc)
  | letPredicate value body ih => exact .letPredicate value (ih hc)
  | ascribe type proof ih => exact .ascribe type (ih hc)
  | eqRefl => exact .eqRefl
  | eqSubst a => exact .eqSubst a
  | succNeZero => exact .succNeZero
  | succInj => exact .succInj
  | lem formula => exact .lem formula
  | induction a => exact .induction a
  | conversion proof type ih => exact .conversion (ih hc) type

/-- Typed computational equality forms both endpoints. -/
public theorem TermEq.regularity {E Ξ Γ t u k} (h : TermEq E Ξ Γ t u k) :
    TermTyping E Ξ Γ t k ∧ TermTyping E Ξ Γ u k := term_regular h

/-- Typed predicate equality forms both endpoints at the stated arity and sort. -/
public theorem PredicateEq.regularity {E Ξ Γ P Q σ} (valid : EnvironmentWF E)
    (h : PredicateEq E Ξ Γ P Q σ) : PredicateTyping E Ξ Γ P σ ∧ PredicateTyping E Ξ Γ Q σ :=
  predicate_regular valid h

/-- Predicate subtyping preserves the numerical arity. -/
public theorem PredicateSubtyping.arity_eq {σ τ} (h : PredicateSubtyping σ τ) :
    σ.arity = τ.arity := by cases h <;> rfl

/-- Consecutive predicate inclusions compose at the same arity. -/
public theorem PredicateSubtyping.trans {σ τ υ} (h : PredicateSubtyping σ τ)
    (g : PredicateSubtyping τ υ) : PredicateSubtyping σ υ := subtype_trans h g

/-- Both lists of computationally equal function actuals have the declared arities. -/
public theorem FunctionArgumentEq.regularity {E Ξ Γ fs gs ks}
    (h : FunctionArgumentEq E Ξ Γ fs gs ks) :
    FunctionArguments E Ξ Γ fs ks ∧ FunctionArguments E Ξ Γ gs ks := arguments_regular h

/-- Both lists of definitionally equal predicate actuals have their declared full signatures. -/
public theorem PredicateArgumentEq.regularity {E Ξ Γ ps qs signatures} (valid : EnvironmentWF E)
    (h : PredicateArgumentEq E Ξ Γ ps qs signatures) :
    PredicateArguments E Ξ Γ ps signatures ∧ PredicateArguments E Ξ Γ qs signatures :=
  predicates_regular valid h

/-- Both contexts compared by typed equality consist of well-formed formulas. -/
public theorem ProofContextEq.regularity {E Ξ Γ H K} (valid : EnvironmentWF E)
    (h : ProofContextEq E Ξ Γ H K) : ContextWF E Ξ Γ H ∧ ContextWF E Ξ Γ K := by
  induction h with
  | nil => exact ⟨.nil, .nil⟩
  | cons head tail ih =>
      exact ⟨.cons (predicate_regular valid head).1 ih.1,
        .cons (predicate_regular valid head).2 ih.2⟩

/-- A well-formed proof context is pointwise definitionally equal to itself. -/
public theorem ProofContextEq.refl {E Ξ Γ H} (h : ContextWF E Ξ Γ H) :
    ProofContextEq E Ξ Γ H H := by
  induction h with
  | nil => exact .nil
  | cons head tail ih => exact .cons (.refl head) ih

/-- Conversion of proof assumptions is symmetric. -/
public theorem ProofContextEq.symm {E Ξ Γ H K} (h : ProofContextEq E Ξ Γ H K) :
    ProofContextEq E Ξ Γ K H := by
  induction h with
  | nil => exact .nil
  | cons head tail ih => exact .cons (.symm head) ih

/-- Conversion of proof assumptions is transitive and preserves their indices. -/
public theorem ProofContextEq.trans {E Ξ Γ H K L} (h : ProofContextEq E Ξ Γ H K)
    (g : ProofContextEq E Ξ Γ K L) : ProofContextEq E Ξ Γ H L := by
  induction h generalizing L with
  | nil => cases g; exact .nil
  | cons head tail ih =>
      cases g with
      | cons head' tail' => exact .cons (.trans head head') (ih tail')

/-- Pointwise conversion compares contexts with exactly the same number of assumptions. -/
public theorem ProofContextEq.length_eq {E Ξ Γ H K} (h : ProofContextEq E Ξ Γ H K) :
    H.length = K.length := by
  induction h with
  | nil => rfl
  | cons head tail ih => simp only [List.length_cons, ih]

/-- Conversion of assumptions is preserved when a numerical variable is introduced. -/
public theorem ProofContextEq.shift {E Ξ Γ H K} (valid : EnvironmentWF E)
    (h : ProofContextEq E Ξ Γ H K) (j : Arity) :
    ProofContextEq E Ξ (j :: Γ) (H.map Predicate.shift) (K.map Predicate.shift) := by
  induction h with
  | nil => exact .nil
  | cons head tail ih => exact .cons (PredicateEq.shift valid head j) ih

/-- Local substitution preserves pointwise conversion of proof assumptions. -/
public theorem ProofContextEq.subst {E Ξ Γ H K} (valid : EnvironmentWF E)
    (h : ProofContextEq E Ξ Γ H K) {Δ : LocalContext} (s : Subst)
    (hs : SubstitutionTyping E Ξ Γ Δ s) :
    ProofContextEq E Ξ Δ (H.map (Predicate.subst s)) (K.map (Predicate.subst s)) := by
  induction h with
  | nil => exact .nil
  | cons head tail ih => exact .cons (PredicateEq.subst valid head s hs) ih

/-- A proof remains valid after replacing its assumptions by definitionally equal formulas.
The proof syntax and its conclusion are unchanged. -/
public theorem ProofTyping.context_conversion {E Ξ Γ H K p A} (valid : EnvironmentWF E)
    (h : ProofTyping E Ξ Γ H p A) (contexts : ProofContextEq E Ξ Γ H K) :
    ProofTyping E Ξ Γ K p A := by
  apply proof_context_conversion valid h
  intro i B lookup
  obtain ⟨C, hC, heq⟩ := context_lookup contexts lookup
  exact ⟨C, hC, Or.inr heq⟩

/-- Definitionally equal assumptions support exactly the same explicit proofs and conclusions. -/
public theorem ProofTyping.context_conversion_iff {E Ξ Γ H K p A} (valid : EnvironmentWF E)
    (contexts : ProofContextEq E Ξ Γ H K) :
    ProofTyping E Ξ Γ H p A ↔ ProofTyping E Ξ Γ K p A :=
  ⟨fun h => ProofTyping.context_conversion valid h contexts,
    fun h => ProofTyping.context_conversion valid h (ProofContextEq.symm contexts)⟩

end LeanPRA.Core.Theory
