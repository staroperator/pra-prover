module

public import PRAProver.Metatheory.Core.Judgement.Instantiation

/-!
# Changing declaration-parameter contexts

- `ParameterContextExtends` preserves the two separate parameter index spaces by lookup.
- The `weakenParameters` theorems preserve expressions when those parameter lookups are preserved.
- `ParameterRenamingTyping` describes separate function and predicate index renamings.
- The `renameParameters` theorems realize those renamings by simultaneous parameter instantiation.

A parameter renaming supplies explicit parameter references at the declaration interface.
-/

namespace PRAProver.Core.Theory

/-- Every existing function and predicate parameter keeps its exact signature and index. -/
public structure ParameterContextExtends (source target : ParameterContext) : Prop where
  functions : ∀ (i : Nat) k, source.functions[i]? = some k → target.functions[i]? = some k
  predicates : ∀ (i : Nat) σ, source.predicates[i]? = some σ → target.predicates[i]? = some σ

/-- Two independent index maps preserve the respective parameter signatures. -/
public structure ParameterRenamingTyping (source target : ParameterContext)
    (functions predicates : Renaming) : Prop where
  functions : ∀ (i : Nat) k, source.functions[i]? = some k → target.functions[functions i]? = some k
  predicates : ∀ (i : Nat) σ,
    source.predicates[i]? = some σ → target.predicates[predicates i]? = some σ

/-- Function-parameter references supplying a renamed declaration interface. -/
@[expose] public def functionParameters (source : ParameterContext) (r : Renaming) : List Term :=
  (List.range source.functions.length).map (fun i => .parameter (r i))

/-- Predicate-parameter references supplying the separate renamed predicate interface. -/
@[expose] public def predicateParameters (source : ParameterContext) (r : Renaming) :
    List Predicate :=
  (List.range source.predicates.length).map (fun i => .parameter (r i))

private theorem term_weaken {E Ξ Γ t k} (h : TermTyping E Ξ Γ t k)
    {Ω} (ext : ParameterContextExtends Ξ Ω) : TermTyping E Ω Γ t k := by
  induction h using TermTyping.rec
    (motive_2 := fun Γ fs ks _ => FunctionArguments E Ω Γ fs ks) with
  | bvar lookup => exact .bvar lookup
  | parameter lookup => exact .parameter (ext.functions _ _ lookup)
  | zero => exact .zero
  | succ => exact .succ
  | lam body ih => exact .lam ih
  | app f a ihf iha => exact .app ihf iha
  | letE a t iha iht => exact .letE iha iht
  | primrec b s ihb ihs => exact .primrec ihb ihs
  | definition lookup args ih => exact .definition lookup ih
  | nil => exact .nil
  | cons head tail ihh iht => exact .cons ihh iht

private theorem functions_weaken {E Ξ Γ fs ks} (h : FunctionArguments E Ξ Γ fs ks)
    {Ω} (ext : ParameterContextExtends Ξ Ω) : FunctionArguments E Ω Γ fs ks := by
  induction h using FunctionArguments.rec (motive_1 := fun _ _ _ _ => True)
  case nil => exact .nil
  case cons head tail ihh iht => exact .cons (term_weaken head ext) iht
  all_goals trivial

private theorem predicate_weaken {E Ξ Γ P σ} (h : PredicateTyping E Ξ Γ P σ)
    {Ω} (ext : ParameterContextExtends Ξ Ω) : PredicateTyping E Ω Γ P σ := by
  induction h using PredicateTyping.rec
    (motive_2 := fun Γ ps signatures _ => PredicateArguments E Ω Γ ps signatures) with
  | false => exact .false
  | true => exact .true
  | equal a b => exact .equal (term_weaken a ext) (term_weaken b ext)
  | imp A B ihA ihB => exact .imp ihA ihB
  | and A B ihA ihB => exact .and ihA ihB
  | or A B ihA ihB => exact .or ihA ihB
  | all P ih => exact .all ih
  | ex P ih => exact .ex ih
  | parameter lookup => exact .parameter (ext.predicates _ _ lookup)
  | lam P ih => exact .lam ih
  | app P a ih => exact .app ih (term_weaken a ext)
  | letTerm a P ih => exact .letTerm (term_weaken a ext) ih
  | letPredicate Q P ihQ ihP => exact .letPredicate ihQ ihP
  | definition lookup functions predicates ihp =>
      exact .definition lookup (functions_weaken functions ext) ihp
  | subsumption h sub ih => exact .subsumption ih sub
  | nil => exact .nil
  | cons head tail ihh iht => exact .cons ihh iht

private theorem predicates_weaken {E Ξ Γ ps signatures}
    (h : PredicateArguments E Ξ Γ ps signatures) {Ω} (ext : ParameterContextExtends Ξ Ω) :
    PredicateArguments E Ω Γ ps signatures := by
  induction h using PredicateArguments.rec (motive_1 := fun _ _ _ _ => True)
  case nil => exact .nil
  case cons head tail ihh iht => exact .cons (predicate_weaken head ext) iht
  all_goals trivial

private theorem term_eq_weaken {E Ξ Γ t u k} (h : TermEq E Ξ Γ t u k)
    {Ω} (ext : ParameterContextExtends Ξ Ω) : TermEq E Ω Γ t u k := by
  induction h using TermEq.rec
    (motive_2 := fun Γ fs gs ks _ => FunctionArgumentEq E Ω Γ fs gs ks) with
  | refl typing => exact .refl (term_weaken typing ext)
  | symm h ih => exact .symm ih
  | trans h g ihh ihg => exact .trans ihh ihg
  | beta body arg => exact .beta (term_weaken body ext) (term_weaken arg ext)
  | eta function => exact .eta (term_weaken function ext)
  | zeta value body => exact .zeta (term_weaken value ext) (term_weaken body ext)
  | delta lookup args body =>
      exact .delta lookup (functions_weaken args ext) (term_weaken body ext)
  | primrecZero base step => exact .primrecZero (term_weaken base ext) (term_weaken step ext)
  | primrecSucc base step arg =>
      exact .primrecSucc (term_weaken base ext) (term_weaken step ext) (term_weaken arg ext)
  | lam body ih => exact .lam ih
  | app f a ihf iha => exact .app ihf iha
  | letE a body iha ihb => exact .letE iha ihb
  | primrec b s ihb ihs => exact .primrec ihb ihs
  | definition lookup args ih => exact .definition lookup ih
  | nil => exact .nil
  | cons head tail ihh iht => exact .cons ihh iht

private theorem function_eq_weaken {E Ξ Γ fs gs ks} (h : FunctionArgumentEq E Ξ Γ fs gs ks)
    {Ω} (ext : ParameterContextExtends Ξ Ω) : FunctionArgumentEq E Ω Γ fs gs ks := by
  induction h using FunctionArgumentEq.rec (motive_1 := fun _ _ _ _ _ => True)
  case nil => exact .nil
  case cons head tail ihh iht => exact .cons (term_eq_weaken head ext) iht
  all_goals trivial

private theorem predicate_eq_weaken {E Ξ Γ P Q σ} (h : PredicateEq E Ξ Γ P Q σ)
    {Ω} (ext : ParameterContextExtends Ξ Ω) : PredicateEq E Ω Γ P Q σ := by
  induction h using PredicateEq.rec
    (motive_2 := fun Γ ps qs signatures _ => PredicateArgumentEq E Ω Γ ps qs signatures) with
  | refl typing => exact .refl (predicate_weaken typing ext)
  | symm h ih => exact .symm ih
  | trans h g ihh ihg => exact .trans ihh ihg
  | subsumption h sub ih => exact .subsumption ih sub
  | beta body arg => exact .beta (predicate_weaken body ext) (term_weaken arg ext)
  | eta function => exact .eta (predicate_weaken function ext)
  | zetaTerm a P => exact .zetaTerm (term_weaken a ext) (predicate_weaken P ext)
  | zetaPredicate Q P => exact .zetaPredicate (predicate_weaken Q ext) (predicate_weaken P ext)
  | delta lookup functions predicates body bound =>
      exact .delta lookup (functions_weaken functions ext)
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
      exact .definition lookup (function_eq_weaken functions ext) ih
        (predicate_weaken left ext) (predicate_weaken right ext)
  | nil => exact .nil
  | cons head tail ihh iht => exact .cons ihh iht

private theorem proof_weaken {E Ξ Γ H p A} (h : ProofTyping E Ξ Γ H p A)
    {Ω} (ext : ParameterContextExtends Ξ Ω) : ProofTyping E Ω Γ H p A := by
  induction h with
  | hyp lookup => exact .hyp lookup
  | trueIntro => exact .trueIntro
  | theoremE lookup functions predicates =>
      exact .theoremE lookup (functions_weaken functions ext)
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

private theorem renamed_actuals {E : Environment} {Ξ Ω : ParameterContext} {r s : Renaming}
    (h : ParameterRenamingTyping Ξ Ω r s) :
    InstantiationTyping E Ξ Ω [] (functionParameters Ξ r) (predicateParameters Ξ s) := by
  constructor
  · apply FunctionArguments.of_lookup (by simp [functionParameters])
    intro i k hi
    have bound := (List.getElem?_eq_some_iff.mp hi).choose
    refine ⟨.parameter (r i), ?_, .parameter (h.functions i k hi)⟩
    simp only [functionParameters, List.getElem?_map, List.getElem?_range bound, Option.map_some]
  · apply PredicateArguments.of_lookup (by simp [predicateParameters])
    intro i σ hi
    have bound := (List.getElem?_eq_some_iff.mp hi).choose
    refine ⟨.parameter (s i), ?_, .parameter (h.predicates i σ hi)⟩
    simp only [predicateParameters, List.getElem?_map, List.getElem?_range bound, Option.map_some]

private theorem predicate_list_eq_weaken {E Ξ Γ ps qs signatures}
    (h : PredicateArgumentEq E Ξ Γ ps qs signatures) {Ω} (ext : ParameterContextExtends Ξ Ω) :
    PredicateArgumentEq E Ω Γ ps qs signatures := by
  induction h using PredicateArgumentEq.rec (motive_1 := fun _ _ _ _ _ => True)
  case nil => exact .nil
  case cons head tail ihh iht => exact .cons (predicate_eq_weaken head ext) iht
  all_goals trivial

/-- Parameter-context extension is reflexive. -/
public theorem ParameterContextExtends.refl (Ξ : ParameterContext) : ParameterContextExtends Ξ Ξ :=
  ⟨fun _ _ h => h, fun _ _ h => h⟩

/-- Parameter-context extensions compose independently in both index spaces. -/
public theorem ParameterContextExtends.trans {Ξ Ω Θ} (h : ParameterContextExtends Ξ Ω)
    (g : ParameterContextExtends Ω Θ) : ParameterContextExtends Ξ Θ :=
  ⟨fun i k hi => g.functions i k (h.functions i k hi),
    fun i σ hi => g.predicates i σ (h.predicates i σ hi)⟩

/-- Appending parameter signatures preserves every existing index and signature. -/
public theorem ParameterContextExtends.append (Ξ : ParameterContext) (fs : List Arity)
    (ps : List PredicateSignature) :
    ParameterContextExtends Ξ
      { functions := Ξ.functions ++ fs, predicates := Ξ.predicates ++ ps } := by
  constructor <;> intro i σ hi
  · exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp hi).choose).trans hi
  · exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp hi).choose).trans hi

/-- Term typing preserves its original syntax under parameter-context extension. -/
public theorem TermTyping.weakenParameters {E Ξ Γ t k} (h : TermTyping E Ξ Γ t k)
    {Ω} (ext : ParameterContextExtends Ξ Ω) : TermTyping E Ω Γ t k := term_weaken h ext

/-- Predicate typing preserves its full signature under parameter-context extension. -/
public theorem PredicateTyping.weakenParameters {E Ξ Γ P σ} (h : PredicateTyping E Ξ Γ P σ)
    {Ω} (ext : ParameterContextExtends Ξ Ω) : PredicateTyping E Ω Γ P σ := predicate_weaken h ext

/-- Typed term equality is preserved under parameter-context extension. -/
public theorem TermEq.weakenParameters {E Ξ Γ t u k} (h : TermEq E Ξ Γ t u k)
    {Ω} (ext : ParameterContextExtends Ξ Ω) : TermEq E Ω Γ t u k := term_eq_weaken h ext

/-- Typed predicate equality is preserved under parameter-context extension. -/
public theorem PredicateEq.weakenParameters {E Ξ Γ P Q σ} (h : PredicateEq E Ξ Γ P Q σ)
    {Ω} (ext : ParameterContextExtends Ξ Ω) : PredicateEq E Ω Γ P Q σ := predicate_eq_weaken h ext

/-- Explicit proof data and its conclusion are unchanged by parameter-context extension. -/
public theorem ProofTyping.weakenParameters {E Ξ Γ H p A} (h : ProofTyping E Ξ Γ H p A)
    {Ω} (ext : ParameterContextExtends Ξ Ω) : ProofTyping E Ω Γ H p A := proof_weaken h ext

/-- Complete function actual lists remain typed when parameters are extended. -/
public theorem FunctionArguments.weakenParameters {E Ξ Γ fs ks}
    (h : FunctionArguments E Ξ Γ fs ks) {Ω} (ext : ParameterContextExtends Ξ Ω) :
    FunctionArguments E Ω Γ fs ks := functions_weaken h ext

/-- Complete predicate actual lists remain typed when parameters are extended. -/
public theorem PredicateArguments.weakenParameters {E Ξ Γ ps signatures}
    (h : PredicateArguments E Ξ Γ ps signatures) {Ω} (ext : ParameterContextExtends Ξ Ω) :
    PredicateArguments E Ω Γ ps signatures := predicates_weaken h ext

/-- Function-actual equality remains valid when parameter signatures are extended. -/
public theorem FunctionArgumentEq.weakenParameters {E Ξ Γ fs gs ks}
    (h : FunctionArgumentEq E Ξ Γ fs gs ks) {Ω} (ext : ParameterContextExtends Ξ Ω) :
    FunctionArgumentEq E Ω Γ fs gs ks := function_eq_weaken h ext

/-- Predicate-actual equality remains valid when parameter signatures are extended. -/
public theorem PredicateArgumentEq.weakenParameters {E Ξ Γ ps qs signatures}
    (h : PredicateArgumentEq E Ξ Γ ps qs signatures) {Ω} (ext : ParameterContextExtends Ξ Ω) :
    PredicateArgumentEq E Ω Γ ps qs signatures := predicate_list_eq_weaken h ext

/-- Assumptions remain formed when their parameter contexts extend. -/
public theorem ContextWF.weakenParameters {E Ξ Γ H} (h : ContextWF E Ξ Γ H)
    {Ω} (ext : ParameterContextExtends Ξ Ω) : ContextWF E Ω Γ H := by
  induction h with
  | nil => exact .nil
  | cons head tail ih => exact .cons (predicate_weaken head ext) ih

/-- Conversion of assumptions is preserved when parameter contexts extend. -/
public theorem ProofContextEq.weakenParameters {E Ξ Γ H K} (h : ProofContextEq E Ξ Γ H K)
    {Ω} (ext : ParameterContextExtends Ξ Ω) : ProofContextEq E Ω Γ H K := by
  induction h with
  | nil => exact .nil
  | cons head tail ih => exact .cons (predicate_eq_weaken head ext) ih

/-- Independent function/predicate index maps give a checked simultaneous instantiation. -/
public theorem ParameterRenamingTyping.actuals {E : Environment} {Ξ Ω : ParameterContext}
    {r s : Renaming} (h : ParameterRenamingTyping Ξ Ω r s) :
    InstantiationTyping E Ξ Ω [] (functionParameters Ξ r) (predicateParameters Ξ s) :=
  renamed_actuals h

/-- Rename function parameters through their declaration interface, preserving all local indices. -/
public theorem TermTyping.renameParameters {E Ξ Γ t k} (h : TermTyping E Ξ Γ t k)
    {Ω r s} (hr : ParameterRenamingTyping Ξ Ω r s) :
    TermTyping E Ω Γ (t.instantiate (functionParameters Ξ r) Γ.length) k := by
  simpa only [List.append_nil] using TermTyping.instantiate h (renamed_actuals hr).functions

/-- Rename the two independent predicate/function parameter spaces without changing the sort. -/
public theorem PredicateTyping.renameParameters {E Ξ Γ P σ} (valid : EnvironmentWF E)
    (h : PredicateTyping E Ξ Γ P σ) {Ω r s} (hr : ParameterRenamingTyping Ξ Ω r s) :
    PredicateTyping E Ω Γ
      (P.instantiate (functionParameters Ξ r) (predicateParameters Ξ s) Γ.length) σ := by
  simpa only [List.append_nil] using PredicateTyping.instantiate valid h (renamed_actuals hr)

/-- Typed term conversion respects independent parameter renaming. -/
public theorem TermEq.renameParameters {E Ξ Γ t u k} (valid : EnvironmentWF E)
    (h : TermEq E Ξ Γ t u k) {Ω r s} (hr : ParameterRenamingTyping Ξ Ω r s) :
    TermEq E Ω Γ (t.instantiate (functionParameters Ξ r) Γ.length)
      (u.instantiate (functionParameters Ξ r) Γ.length) k := by
  simpa only [List.append_nil] using TermEq.instantiate valid h (renamed_actuals hr).functions

/-- Typed predicate conversion respects independent parameter renaming at the same signature. -/
public theorem PredicateEq.renameParameters {E Ξ Γ P Q σ} (valid : EnvironmentWF E)
    (h : PredicateEq E Ξ Γ P Q σ) {Ω r s} (hr : ParameterRenamingTyping Ξ Ω r s) :
    PredicateEq E Ω Γ
      (P.instantiate (functionParameters Ξ r) (predicateParameters Ξ s) Γ.length)
      (Q.instantiate (functionParameters Ξ r) (predicateParameters Ξ s) Γ.length) σ := by
  simpa only [List.append_nil] using PredicateEq.instantiate valid h (renamed_actuals hr)

/-- Rename parameters throughout proof data, its hypotheses, and its conclusion. -/
public theorem ProofTyping.renameParameters {E Ξ Γ H p A} (valid : EnvironmentWF E)
    (h : ProofTyping E Ξ Γ H p A) {Ω r s} (hr : ParameterRenamingTyping Ξ Ω r s) :
    ProofTyping E Ω Γ
      (H.map (Predicate.instantiate (functionParameters Ξ r) (predicateParameters Ξ s) Γ.length))
      (p.instantiate (functionParameters Ξ r) (predicateParameters Ξ s) Γ.length)
      (A.instantiate (functionParameters Ξ r) (predicateParameters Ξ s) Γ.length) := by
  simpa only [List.append_nil] using ProofTyping.instantiate valid h (renamed_actuals hr)

/-- Parameter renaming transforms every formed hypothesis at the same formula signature. -/
public theorem ContextWF.renameParameters {E Ξ Γ H} (valid : EnvironmentWF E)
    (h : ContextWF E Ξ Γ H) {Ω r s} (hr : ParameterRenamingTyping Ξ Ω r s) :
    ContextWF E Ω Γ
      (H.map (Predicate.instantiate (functionParameters Ξ r)
        (predicateParameters Ξ s) Γ.length)) := by
  simpa only [List.append_nil] using ContextWF.instantiate valid h (renamed_actuals hr)

/-- Parameter renaming preserves pointwise conversion of proof assumptions. -/
public theorem ProofContextEq.renameParameters {E Ξ Γ H K} (valid : EnvironmentWF E)
    (h : ProofContextEq E Ξ Γ H K) {Ω r s} (hr : ParameterRenamingTyping Ξ Ω r s) :
    ProofContextEq E Ω Γ
      (H.map (Predicate.instantiate (functionParameters Ξ r) (predicateParameters Ξ s) Γ.length))
      (K.map (Predicate.instantiate (functionParameters Ξ r)
        (predicateParameters Ξ s) Γ.length)) := by
  simpa only [List.append_nil] using ProofContextEq.instantiate valid h (renamed_actuals hr)

end PRAProver.Core.Theory
