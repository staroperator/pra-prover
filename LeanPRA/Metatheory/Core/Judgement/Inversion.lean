module

public import LeanPRA.Metatheory.Core.Judgement.Conversion

/-!
# Inversion of term and predicate formation

- The `TermTyping.inv_*` theorems recover the premises of each term constructor.
- The `PredicateTyping.inv_*` theorems recover formation premises through subsumption.
- `FunctionArguments.lookup` and `PredicateArguments.lookup` recover actuals at declared indices.

Predicate inversion gives a subtype witness that accounts for QFProp-to-Prop inclusion.
Definition inversion recovers the declared signature and its inclusion in the result signature.
-/

namespace LeanPRA.Core.Theory

private theorem function_lookup {E Ξ Γ fs ks} (h : FunctionArguments E Ξ Γ fs ks) :
    ∀ {i : Nat} {k}, ks[i]? = some k → ∃ t, fs[i]? = some t ∧ TermTyping E Ξ Γ t k := by
  induction h using FunctionArguments.rec (motive_1 := fun _ _ _ _ => True)
  case nil => intro i k hi; simp at hi
  case cons head tail ihh iht =>
      intro i k hi
      cases i with
      | zero =>
          have hk := Option.some.inj hi
          subst hk
          exact ⟨_, rfl, head⟩
      | succ i => exact iht hi
  all_goals trivial

private theorem functions_of_lookup {E Ξ Γ fs ks} (lengths : fs.length = ks.length)
    (typed : ∀ (i : Nat) k, ks[i]? = some k →
      ∃ t, fs[i]? = some t ∧ TermTyping E Ξ Γ t k) : FunctionArguments E Ξ Γ fs ks := by
  induction ks generalizing fs with
  | nil => cases fs <;> simp_all; exact .nil
  | cons k ks ih =>
      cases fs with
      | nil => simp at lengths
      | cons t ts =>
          obtain ⟨u, hu, htype⟩ := typed 0 k rfl
          have heq := Option.some.inj hu
          subst heq
          refine .cons htype (ih (by simpa using lengths) ?_)
          intro i j hi
          exact typed (i + 1) j hi

private theorem predicates_of_lookup {E Ξ Γ ps signatures}
    (lengths : ps.length = signatures.length)
    (typed : ∀ (i : Nat) σ, signatures[i]? = some σ →
      ∃ P, ps[i]? = some P ∧ PredicateTyping E Ξ Γ P σ) :
    PredicateArguments E Ξ Γ ps signatures := by
  induction signatures generalizing ps with
  | nil => cases ps <;> simp_all; exact .nil
  | cons σ signatures ih =>
      cases ps with
      | nil => simp at lengths
      | cons P ps =>
          obtain ⟨Q, hQ, htype⟩ := typed 0 σ rfl
          have heq := Option.some.inj hQ
          subst heq
          refine .cons htype (ih (by simpa using lengths) ?_)
          intro i τ hi
          exact typed (i + 1) τ hi

private theorem predicate_lookup {E Ξ Γ ps signatures}
    (h : PredicateArguments E Ξ Γ ps signatures) :
    ∀ {i : Nat} {σ}, signatures[i]? = some σ →
      ∃ P, ps[i]? = some P ∧ PredicateTyping E Ξ Γ P σ := by
  induction h using PredicateArguments.rec (motive_1 := fun _ _ _ _ => True)
  case nil => intro i σ hi; simp at hi
  case cons head tail ihh iht =>
      intro i σ hi
      cases i with
      | zero =>
          have hσ := Option.some.inj hi
          subst hσ
          exact ⟨_, rfl, head⟩
      | succ i => exact iht hi
  all_goals trivial

/-- A typed variable occurs at its displayed arity in the local context. -/
public theorem TermTyping.inv_bvar {E Ξ Γ i k} (h : TermTyping E Ξ Γ (.bvar i) k) :
    Γ[i]? = some k := by cases h with | bvar lookup => exact lookup

/-- A typed function parameter occurs in its separate parameter index space. -/
public theorem TermTyping.inv_parameter {E Ξ Γ i k} (h : TermTyping E Ξ Γ (.parameter i) k) :
    Ξ.functions[i]? = some k := by cases h with | parameter lookup => exact lookup

/-- Zero has numerical arity zero. -/
public theorem TermTyping.inv_zero {E Ξ Γ k} (h : TermTyping E Ξ Γ .zero k) : k = 0 := by
  cases h
  rfl

/-- Successor has one numerical argument. -/
public theorem TermTyping.inv_succ {E Ξ Γ k} (h : TermTyping E Ξ Γ .succ k) : k = 1 := by
  cases h
  rfl

/-- A lambda introduces exactly one numerical local. -/
public theorem TermTyping.inv_lam {E Ξ Γ t k} (h : TermTyping E Ξ Γ (.lam binderName t) k) :
    ∃ j, k = j + 1 ∧ TermTyping E Ξ (0 :: Γ) t j := by
  cases h with | lam body => exact ⟨_, rfl, body⟩

/-- Application consumes one numerical argument. -/
public theorem TermTyping.inv_app {E Ξ Γ f a k} (h : TermTyping E Ξ Γ (.app f a) k) :
    TermTyping E Ξ Γ f (k + 1) ∧ TermTyping E Ξ Γ a 0 := by
  cases h with | app function argument => exact ⟨function, argument⟩

/-- A let binds a local at the value's arity, including function-valued locals. -/
public theorem TermTyping.inv_let {E Ξ Γ a t k} (h : TermTyping E Ξ Γ (.letE binderName a t) k) :
    ∃ j, TermTyping E Ξ Γ a j ∧ TermTyping E Ξ (j :: Γ) t k := by
  cases h with | letE value body => exact ⟨_, value, body⟩

/-- Primitive recursion has unary arity, a numerical base, and a binary numerical step. -/
public theorem TermTyping.inv_primrec {E Ξ Γ b s k}
    (h : TermTyping E Ξ Γ (.primrec b s) k) :
    k = 1 ∧ TermTyping E Ξ Γ b 0 ∧ TermTyping E Ξ Γ s 2 := by
  cases h with | primrec base step => exact ⟨rfl, base, step⟩

/-- A function reference supplies all declared function actuals. -/
public theorem TermTyping.inv_definition {E Ξ Γ name fs k}
    (h : TermTyping E Ξ Γ (.definition name fs) k) :
    ∃ d, E[name]? = some (.function d) ∧ FunctionArguments E Ξ Γ fs d.functions ∧ k = d.arity := by
  cases h with | definition lookup arguments => exact ⟨_, lookup, arguments, rfl⟩

/-- A function actual at a declared index exists and has that index's declared arity. -/
public theorem FunctionArguments.lookup {E Ξ Γ fs ks} (h : FunctionArguments E Ξ Γ fs ks)
    {i : Nat} {k} (hi : ks[i]? = some k) :
    ∃ t, fs[i]? = some t ∧ TermTyping E Ξ Γ t k := function_lookup h hi

/-- A predicate actual at a declared index exists at its declared full signature. -/
public theorem PredicateArguments.lookup {E Ξ Γ ps signatures}
    (h : PredicateArguments E Ξ Γ ps signatures) {i : Nat} {σ}
    (hi : signatures[i]? = some σ) :
    ∃ P, ps[i]? = some P ∧ PredicateTyping E Ξ Γ P σ := predicate_lookup h hi

/-- Function actual lists have exactly the declared length. -/
public theorem FunctionArguments.length_eq {E Ξ Γ fs ks} (h : FunctionArguments E Ξ Γ fs ks) :
    fs.length = ks.length := by
  induction h using FunctionArguments.rec (motive_1 := fun _ _ _ _ => True)
  case nil => rfl
  case cons head tail ihh iht => simp only [List.length_cons, iht]
  all_goals trivial

/-- Predicate actual lists have exactly the declared length. -/
public theorem PredicateArguments.length_eq {E Ξ Γ ps signatures}
    (h : PredicateArguments E Ξ Γ ps signatures) : ps.length = signatures.length := by
  induction h using PredicateArguments.rec (motive_1 := fun _ _ _ _ => True)
  case nil => rfl
  case cons head tail ihh iht => simp only [List.length_cons, iht]
  all_goals trivial

/-- Exact length and typed lookups suffice to form a complete function-actual list. -/
public theorem FunctionArguments.of_lookup {E Ξ Γ fs ks} (lengths : fs.length = ks.length)
    (typed : ∀ (i : Nat) k, ks[i]? = some k →
      ∃ t, fs[i]? = some t ∧ TermTyping E Ξ Γ t k) : FunctionArguments E Ξ Γ fs ks :=
  functions_of_lookup lengths typed

/-- Exact length and full-signature lookups suffice to form a predicate-actual list. -/
public theorem PredicateArguments.of_lookup {E Ξ Γ ps signatures}
    (lengths : ps.length = signatures.length)
    (typed : ∀ (i : Nat) σ, signatures[i]? = some σ →
      ∃ P, ps[i]? = some P ∧ PredicateTyping E Ξ Γ P σ) :
    PredicateArguments E Ξ Γ ps signatures := predicates_of_lookup lengths typed

/-- Falsity is formed at QFProp or its inclusion into Prop. -/
public theorem PredicateTyping.inv_false {E Ξ Γ σ} (h : PredicateTyping E Ξ Γ .false σ) :
    PredicateSubtyping ⟨0, .qf⟩ σ := by
  generalize heq : Predicate.false = P at h
  induction h using PredicateTyping.rec (motive_2 := fun _ _ _ _ => True) with
  | false => exact .refl
  | subsumption h sub ih => exact .trans (ih heq) sub
  | nil => trivial
  | cons => trivial
  | _ => cases heq

/-- Truth is formed at QFProp or its inclusion into Prop. -/
public theorem PredicateTyping.inv_true {E Ξ Γ σ} (h : PredicateTyping E Ξ Γ .true σ) :
    PredicateSubtyping ⟨0, .qf⟩ σ := by
  generalize heq : Predicate.true = P at h
  induction h using PredicateTyping.rec (motive_2 := fun _ _ _ _ => True) with
  | true => exact .refl
  | subsumption h sub ih => exact .trans (ih heq) sub
  | nil => trivial
  | cons => trivial
  | _ => cases heq

/-- Numerical equality compares two numerical terms, with a possibly lifted QF result. -/
public theorem PredicateTyping.inv_equal {E Ξ Γ a b σ}
    (h : PredicateTyping E Ξ Γ (.equal a b) σ) :
    TermTyping E Ξ Γ a 0 ∧ TermTyping E Ξ Γ b 0 ∧ PredicateSubtyping ⟨0, .qf⟩ σ := by
  generalize heq : Predicate.equal a b = P at h
  induction h using PredicateTyping.rec (motive_2 := fun _ _ _ _ => True) with
  | equal left right => cases heq; exact ⟨left, right, .refl⟩
  | subsumption h sub ih =>
      obtain ⟨ha, hb, hs⟩ := ih heq
      exact ⟨ha, hb, .trans hs sub⟩
  | nil => trivial
  | cons => trivial
  | _ => cases heq

/-- Implication operands share a sort before any outer subsumption. -/
public theorem PredicateTyping.inv_imp {E Ξ Γ A B σ} (h : PredicateTyping E Ξ Γ (.imp A B) σ) :
    ∃ s, PredicateTyping E Ξ Γ A ⟨0, s⟩ ∧ PredicateTyping E Ξ Γ B ⟨0, s⟩ ∧
      PredicateSubtyping ⟨0, s⟩ σ := by
  generalize heq : Predicate.imp A B = P at h
  induction h using PredicateTyping.rec (motive_2 := fun _ _ _ _ => True) with
  | imp left right ihl ihr => cases heq; exact ⟨_, left, right, .refl⟩
  | subsumption h sub ih =>
      obtain ⟨s, ha, hb, hs⟩ := ih heq
      exact ⟨s, ha, hb, .trans hs sub⟩
  | nil => trivial
  | cons => trivial
  | _ => cases heq

/-- Conjunction operands share a sort before any outer subsumption. -/
public theorem PredicateTyping.inv_and {E Ξ Γ A B σ} (h : PredicateTyping E Ξ Γ (.and A B) σ) :
    ∃ s, PredicateTyping E Ξ Γ A ⟨0, s⟩ ∧ PredicateTyping E Ξ Γ B ⟨0, s⟩ ∧
      PredicateSubtyping ⟨0, s⟩ σ := by
  generalize heq : Predicate.and A B = P at h
  induction h using PredicateTyping.rec (motive_2 := fun _ _ _ _ => True) with
  | and left right ihl ihr => cases heq; exact ⟨_, left, right, .refl⟩
  | subsumption h sub ih =>
      obtain ⟨s, ha, hb, hs⟩ := ih heq
      exact ⟨s, ha, hb, .trans hs sub⟩
  | nil => trivial
  | cons => trivial
  | _ => cases heq

/-- Disjunction operands share a sort before any outer subsumption. -/
public theorem PredicateTyping.inv_or {E Ξ Γ A B σ} (h : PredicateTyping E Ξ Γ (.or A B) σ) :
    ∃ s, PredicateTyping E Ξ Γ A ⟨0, s⟩ ∧ PredicateTyping E Ξ Γ B ⟨0, s⟩ ∧
      PredicateSubtyping ⟨0, s⟩ σ := by
  generalize heq : Predicate.or A B = P at h
  induction h using PredicateTyping.rec (motive_2 := fun _ _ _ _ => True) with
  | or left right ihl ihr => cases heq; exact ⟨_, left, right, .refl⟩
  | subsumption h sub ih =>
      obtain ⟨s, ha, hb, hs⟩ := ih heq
      exact ⟨s, ha, hb, .trans hs sub⟩
  | nil => trivial
  | cons => trivial
  | _ => cases heq

/-- Universal quantification has result Prop and consumes a unary predicate. -/
public theorem PredicateTyping.inv_all {E Ξ Γ P σ} (h : PredicateTyping E Ξ Γ (.all P) σ) :
    σ = ⟨0, .prop⟩ ∧ PredicateTyping E Ξ Γ P ⟨1, .prop⟩ := by
  generalize heq : Predicate.all P = Q at h
  induction h using PredicateTyping.rec (motive_2 := fun _ _ _ _ => True) with
  | all body ih => cases heq; exact ⟨rfl, body⟩
  | subsumption h sub ih =>
      obtain ⟨rfl, body⟩ := ih heq
      cases sub
      exact ⟨rfl, body⟩
  | nil => trivial
  | cons => trivial
  | _ => cases heq

/-- Existential quantification has result Prop and consumes a unary predicate. -/
public theorem PredicateTyping.inv_ex {E Ξ Γ P σ} (h : PredicateTyping E Ξ Γ (.ex P) σ) :
    σ = ⟨0, .prop⟩ ∧ PredicateTyping E Ξ Γ P ⟨1, .prop⟩ := by
  generalize heq : Predicate.ex P = Q at h
  induction h using PredicateTyping.rec (motive_2 := fun _ _ _ _ => True) with
  | ex body ih => cases heq; exact ⟨rfl, body⟩
  | subsumption h sub ih =>
      obtain ⟨rfl, body⟩ := ih heq
      cases sub
      exact ⟨rfl, body⟩
  | nil => trivial
  | cons => trivial
  | _ => cases heq

/-- A predicate parameter has its declared signature or an upward inclusion of it. -/
public theorem PredicateTyping.inv_parameter {E Ξ Γ i σ}
    (h : PredicateTyping E Ξ Γ (.parameter i) σ) :
    ∃ τ, Ξ.predicates[i]? = some τ ∧ PredicateSubtyping τ σ := by
  generalize heq : Predicate.parameter i = P at h
  induction h using PredicateTyping.rec (motive_2 := fun _ _ _ _ => True) with
  | parameter lookup => cases heq; exact ⟨_, lookup, .refl⟩
  | subsumption h sub ih =>
      obtain ⟨τ, lookup, hs⟩ := ih heq
      exact ⟨τ, lookup, .trans hs sub⟩
  | nil => trivial
  | cons => trivial
  | _ => cases heq

/-- A predicate lambda binds one number and preserves its body's result sort. -/
public theorem PredicateTyping.inv_lam {E Ξ Γ P σ}
    (h : PredicateTyping E Ξ Γ (.lam binderName P) σ) :
    ∃ k s, PredicateTyping E Ξ (0 :: Γ) P ⟨k, s⟩ ∧ PredicateSubtyping ⟨k + 1, s⟩ σ := by
  generalize heq : Predicate.lam binderName P = Q at h
  induction h using PredicateTyping.rec (motive_2 := fun _ _ _ _ => True) with
  | lam body ih => cases heq; exact ⟨_, _, body, .refl⟩
  | subsumption h sub ih =>
      obtain ⟨k, s, body, hs⟩ := ih heq
      exact ⟨k, s, body, .trans hs sub⟩
  | nil => trivial
  | cons => trivial
  | _ => cases heq

/-- Predicate application consumes a number, with a subtype witness for its result. -/
public theorem PredicateTyping.inv_app {E Ξ Γ P a σ} (h : PredicateTyping E Ξ Γ (.app P a) σ) :
    ∃ k s, PredicateTyping E Ξ Γ P ⟨k + 1, s⟩ ∧ TermTyping E Ξ Γ a 0 ∧
      PredicateSubtyping ⟨k, s⟩ σ := by
  generalize heq : Predicate.app P a = Q at h
  induction h using PredicateTyping.rec (motive_2 := fun _ _ _ _ => True) with
  | app function argument ih => cases heq; exact ⟨_, _, function, argument, .refl⟩
  | subsumption h sub ih =>
      obtain ⟨k, s, function, argument, hs⟩ := ih heq
      exact ⟨k, s, function, argument, .trans hs sub⟩
  | nil => trivial
  | cons => trivial
  | _ => cases heq

/-- A numerical local definition contains a checked value and an already expanded body. -/
public theorem PredicateTyping.inv_letTerm {E Ξ Γ a P σ}
    (h : PredicateTyping E Ξ Γ (.letTerm binderName a P) σ) :
    (∃ j, TermTyping E Ξ Γ a j) ∧ PredicateTyping E Ξ Γ P σ := by
  generalize heq : Predicate.letTerm binderName a P = Q at h
  induction h using PredicateTyping.rec (motive_2 := fun _ _ _ _ => True) with
  | letTerm value body ih => cases heq; exact ⟨⟨_, value⟩, body⟩
  | subsumption h sub ih =>
      obtain ⟨value, body⟩ := ih heq
      exact ⟨value, .subsumption body sub⟩
  | nil => trivial
  | cons => trivial
  | _ => cases heq

/-- A predicate local definition contains a checked predicate and an already expanded body. -/
public theorem PredicateTyping.inv_letPredicate {E Ξ Γ Q P σ}
    (h : PredicateTyping E Ξ Γ (.letPredicate binderName Q P) σ) :
    (∃ τ, PredicateTyping E Ξ Γ Q τ) ∧ PredicateTyping E Ξ Γ P σ := by
  generalize heq : Predicate.letPredicate binderName Q P = R at h
  induction h using PredicateTyping.rec (motive_2 := fun _ _ _ _ => True) with
  | letPredicate value body ihv ihb => cases heq; exact ⟨⟨_, value⟩, body⟩
  | subsumption h sub ih =>
      obtain ⟨value, body⟩ := ih heq
      exact ⟨value, .subsumption body sub⟩
  | nil => trivial
  | cons => trivial
  | _ => cases heq

/-- A predicate reference has its declared signature, possibly raised from QFProp to Prop. -/
public theorem PredicateTyping.inv_definition {E Ξ Γ name fs ps σ}
    (h : PredicateTyping E Ξ Γ (.definition name fs ps) σ) :
    ∃ d, E[name]? = some (.predicate d) ∧ FunctionArguments E Ξ Γ fs d.functions ∧
      PredicateArguments E Ξ Γ ps d.predicates ∧ PredicateSubtyping d.signature σ := by
  generalize heq : Predicate.definition name fs ps = P at h
  induction h using PredicateTyping.rec (motive_2 := fun _ _ _ _ => True) with
  | definition lookup functions predicates ihp =>
      cases heq
      exact ⟨_, lookup, functions, predicates, .refl⟩
  | subsumption h sub ih =>
      obtain ⟨d, lookup, functions, predicates, hs⟩ := ih heq
      exact ⟨d, lookup, functions, predicates, .trans hs sub⟩
  | nil => trivial
  | cons => trivial
  | _ => cases heq

end LeanPRA.Core.Theory
