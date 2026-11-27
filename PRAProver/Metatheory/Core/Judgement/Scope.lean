module

public import PRAProver.Metatheory.Core.Judgement.Environment

/-!
# Scope of local variables and declaration parameters

- `TermScope` bounds the separate local-variable and function-parameter index spaces.
- `PredicateScope` additionally bounds predicate-parameter indices.
- `TermTyping.scope` and `PredicateTyping.scope` establish these bounds from formation.
- The `EnvironmentWF.*_scope` results specialize them to globally stored bodies and statements.

Scopes describe syntax only. In a declaration body the local depth starts at zero; explicit
lambdas and lets increase it.
-/

namespace PRAProver.Core.Theory

/-- Every local and function-parameter occurrence lies in its own index range. -/
@[expose] public def TermScope (functions : Nat) : Nat → Term → Prop
  | locals, .bvar i => i < locals
  | _, .parameter i => i < functions
  | _, .zero | _, .succ => True
  | locals, .lam _ t => TermScope functions (locals + 1) t
  | locals, .app f a => TermScope functions locals f ∧ TermScope functions locals a
  | locals, .letE _ a t => TermScope functions locals a ∧ TermScope functions (locals + 1) t
  | locals, .primrec b s => TermScope functions locals b ∧ TermScope functions locals s
  | locals, .definition _ fs => ∀ t ∈ fs, TermScope functions locals t

/-- Every local, function-parameter, and predicate-parameter occurrence lies in its index range. -/
@[expose] public def PredicateScope (functions predicates : Nat) : Nat → Predicate → Prop
  | _, .false | _, .true => True
  | _, .parameter i => i < predicates
  | locals, .equal a b => TermScope functions locals a ∧ TermScope functions locals b
  | locals, .imp A B | locals, .and A B | locals, .or A B =>
      PredicateScope functions predicates locals A ∧ PredicateScope functions predicates locals B
  | locals, .all P | locals, .ex P => PredicateScope functions predicates locals P
  | locals, .lam _ P => PredicateScope functions predicates (locals + 1) P
  | locals, .app P a => PredicateScope functions predicates locals P ∧ TermScope functions locals a
  | locals, .letTerm _ a P =>
      TermScope functions locals a ∧ PredicateScope functions predicates locals P
  | locals, .letPredicate _ Q P =>
      PredicateScope functions predicates locals Q ∧ PredicateScope functions predicates locals P
  | locals, .definition _ fs ps =>
      (∀ t ∈ fs, TermScope functions locals t) ∧
        (∀ P ∈ ps, PredicateScope functions predicates locals P)

private theorem term_scope {E Ξ Γ t k} (h : TermTyping E Ξ Γ t k) :
    TermScope Ξ.functions.length Γ.length t := by
  induction h using TermTyping.rec
    (motive_2 := fun Γ fs _ _ => ∀ t ∈ fs, TermScope Ξ.functions.length Γ.length t) <;>
    try simp only [TermScope, List.length_cons] at *
  case bvar lookup => exact (List.getElem?_eq_some_iff.mp lookup).choose
  case parameter lookup => exact (List.getElem?_eq_some_iff.mp lookup).choose
  case lam body ih => exact ih
  case app f a ihf iha => exact ⟨ihf, iha⟩
  case letE a t iha iht => exact ⟨iha, iht⟩
  case primrec b s ihb ihs => exact ⟨ihb, ihs⟩
  case definition lookup args ih => exact ih
  case nil => contradiction
  case cons ihh iht t ht =>
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ihh
      · exact iht _ ht

private theorem functions_scope {E Ξ Γ fs ks} (h : FunctionArguments E Ξ Γ fs ks) :
    ∀ t ∈ fs, TermScope Ξ.functions.length Γ.length t := by
  induction h using FunctionArguments.rec (motive_1 := fun _ _ _ _ => True)
  case nil => intro t ht; contradiction
  case cons head tail ihh iht =>
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact term_scope head
      · exact iht t ht
  all_goals trivial

private theorem predicate_scope {E Ξ Γ P σ} (h : PredicateTyping E Ξ Γ P σ) :
    PredicateScope Ξ.functions.length Ξ.predicates.length Γ.length P := by
  induction h using PredicateTyping.rec
    (motive_2 := fun Γ ps _ _ =>
      ∀ P ∈ ps, PredicateScope Ξ.functions.length Ξ.predicates.length Γ.length P) <;>
    try simp only [PredicateScope, List.length_cons] at *
  case parameter lookup => exact (List.getElem?_eq_some_iff.mp lookup).choose
  case equal a b => exact ⟨term_scope a, term_scope b⟩
  case imp A B ihA ihB => exact ⟨ihA, ihB⟩
  case and A B ihA ihB => exact ⟨ihA, ihB⟩
  case or A B ihA ihB => exact ⟨ihA, ihB⟩
  case all P ih => exact ih
  case ex P ih => exact ih
  case lam P ih => exact ih
  case app P a ih => exact ⟨ih, term_scope a⟩
  case letTerm a P ih => exact ⟨term_scope a, ih⟩
  case letPredicate Q P ihQ ihP => exact ⟨ihQ, ihP⟩
  case definition lookup functions predicates ihp =>
      exact ⟨functions_scope functions, ihp⟩
  case subsumption h sub ih => exact ih
  case nil => contradiction
  case cons ihh iht P hP =>
      rcases List.mem_cons.mp hP with rfl | hP
      · exact ihh
      · exact iht _ hP

/-- Term formation bounds both of its independent index spaces. -/
public theorem TermTyping.scope {E Ξ Γ t k} (h : TermTyping E Ξ Γ t k) :
    TermScope Ξ.functions.length Γ.length t := term_scope h

/-- Predicate formation bounds all three index spaces, independently of its result sort. -/
public theorem PredicateTyping.scope {E Ξ Γ P σ} (h : PredicateTyping E Ξ Γ P σ) :
    PredicateScope Ξ.functions.length Ξ.predicates.length Γ.length P := predicate_scope h

/-- A stored function body has only its declared parameters and internally bound locals. -/
public theorem EnvironmentWF.function_scope {E} (valid : EnvironmentWF E) {name : Lean.Name} {d}
    (lookup : E[name]? = some (.function d)) : TermScope d.functions.length 0 d.body := by
  obtain ⟨_, wf⟩ := EnvironmentWF.lookup valid lookup
  cases wf with | function body => exact term_scope body

/-- A stored predicate body uses only its declared parameters and internally bound locals. -/
public theorem EnvironmentWF.predicate_scope {E} (valid : EnvironmentWF E) {name : Lean.Name} {d}
    (lookup : E[name]? = some (.predicate d)) :
    PredicateScope d.functions.length d.predicates.length 0 d.body := by
  obtain ⟨_, wf⟩ := EnvironmentWF.lookup valid lookup
  cases wf with | predicate body => exact PredicateTyping.scope body

/-- A stored theorem statement uses only its declared parameters and internally bound locals. -/
public theorem EnvironmentWF.theorem_scope {E} (valid : EnvironmentWF E) {name : Lean.Name} {d}
    (lookup : E[name]? = some (.theoremE d)) :
    PredicateScope d.functions.length d.predicates.length 0 d.type := by
  obtain ⟨_, wf⟩ := EnvironmentWF.lookup valid lookup
  cases wf with | theoremE type body => exact PredicateTyping.scope type

end PRAProver.Core.Theory
