module

public import PRAProver.Metatheory.Core.Checker.Typing.ProofCompleteness

/-!
# Soundness and completeness of declaration and proof checking

- `checkDeclarationBody_sound` and `checkDeclarationBody_complete` relate body checking to
  freshness and declarative validity.
- `checkDeclaration_sound` and `checkDeclaration_complete` cover fresh declaration admission.
- `checkDeclarations_sound` and `checkDeclarations_complete` cover ordered declaration lists.
- `checkDeclarations_checkProof_sound` and `checkDeclarations_checkProof_complete` compose
  admission from the empty environment with checking explicit proof data.

Soundness establishes derivability from successful checking in a valid environment and formed
context. Completeness supplies success at every sufficiently large depth. Each declaration is
checked against its predecessors, and fresh insertion preserves earlier lookups.
-/

namespace PRAProver.Core

open Theory

private theorem body_correct {n E d} (valid : EnvironmentWF E)
    (run : checkDeclarationBody n E d = .ok ()) : E[d.name]? = none ∧ DeclarationWF E d := by
  unfold checkDeclarationBody at run
  split at run
  next => simp [fail] at run
  next fresh =>
    have absent : E[d.name]? = none := by
      cases h : E[d.name]? with
      | none => rfl
      | some e => simp [Environment.lookup, h] at fresh
    refine ⟨absent, ?_⟩
    cases d with
    | function d => exact .function (checkTerm_sound run)
    | predicate d => exact .predicate (checkPredicate_sound run)
    | theoremE d =>
        simp only [CheckResult.bind_eq_ok] at run
        obtain ⟨s, ht, hp⟩ := run
        have tt := (inferFormula_sound ht).toProp
        exact .theoremE tt (checkProof_sound valid .nil tt hp)

/-- Successful body checking establishes freshness and validity against the preceding map. -/
public theorem checkDeclarationBody_sound {n E d} (valid : EnvironmentWF E)
    (run : checkDeclarationBody n E d = .ok ()) : E[d.name]? = none ∧ DeclarationWF E d :=
  body_correct valid run

private theorem declaration_correct {n E d F} (valid : EnvironmentWF E)
    (run : checkDeclaration n E d = .ok F) :
    E[d.name]? = none ∧ DeclarationWF E d ∧ F = E.insert d.name d ∧
      EnvironmentWF F ∧ EnvironmentExtends E F := by
  simp only [checkDeclaration, CheckResult.bind_eq_ok, CheckResult.inDeclaration_eq_ok,
    pure, Except.pure, Except.ok.injEq] at run
  obtain ⟨⟨⟩, body, rfl⟩ := run
  obtain ⟨fresh, wellformed⟩ := checkDeclarationBody_sound valid body
  exact ⟨fresh, wellformed, rfl, .insert valid fresh wellformed, .insert fresh⟩

private theorem environment_correct {n} {ds : List Declaration} {E F} (valid : EnvironmentWF E)
    (run : ds.foldlM (checkDeclaration n) E = .ok F) :
    EnvironmentWF F ∧ EnvironmentExtends E F := by
  induction ds generalizing E with
  | nil =>
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at run
      subst F
      exact ⟨valid, .refl E⟩
  | cons d ds ih =>
      simp only [List.foldlM_cons, CheckResult.bind_eq_ok] at run
      obtain ⟨G, hd, hds⟩ := run
      obtain ⟨_, _, _, vg, ext⟩ := declaration_correct valid hd
      obtain ⟨vf, exf⟩ := ih vg hds
      exact ⟨vf, ext.trans exf⟩

/-- **Soundness theorem of declaration checking**: starting from a well-formed environment,
accepting a function, predicate, or theorem establishes that its name is fresh and its body is
legal against the preceding environment. The returned environment is the insertion, is well
formed, and preserves every earlier declaration. -/
public theorem checkDeclaration_sound {n E d F} (valid : EnvironmentWF E)
    (run : checkDeclaration n E d = .ok F) :
    E[d.name]? = none ∧ DeclarationWF E d ∧ F = E.insert d.name d ∧
      EnvironmentWF F ∧ EnvironmentExtends E F :=
  declaration_correct valid run

/-- Checking an ordered declaration list preserves validity and every earlier lookup. -/
public theorem checkDeclarations_sound {n} {ds : List Declaration} {E F} (valid : EnvironmentWF E)
    (run : ds.foldlM (checkDeclaration n) E = .ok F) :
    EnvironmentWF F ∧ EnvironmentExtends E F := environment_correct valid run

/-- Ordered admission followed by proof checking derives the expected formula in a formed
context. -/
public theorem checkDeclarations_checkProof_sound {n m} {ds : List Declaration} {E c p A}
    (environment : ds.foldlM (checkDeclaration n) ∅ = .ok E)
    (ctx : ContextWF E c.parameters c.locals c.proofs)
    (type : PredicateTyping E c.parameters c.locals A ⟨0, .prop⟩)
    (proof : checkProof m E c p A = .ok ()) :
    EnvironmentWF E ∧ ProofTyping E c.parameters c.locals c.proofs p A := by
  have valid := (checkDeclarations_sound .empty environment).1
  exact ⟨valid, checkProof_sound valid ctx type proof⟩

end PRAProver.Core

namespace PRAProver.Core

open Theory

/-- A fresh well-formed declaration body eventually passes the internal admission check. -/
public theorem checkDeclarationBody_complete {E d} (valid : EnvironmentWF E)
    (fresh : E[d.name]? = none) (formed : DeclarationWF E d) :
    ∃ n, ∀ m ≥ n, checkDeclarationBody m E d = .ok () := by
  cases formed with
  | function body =>
      obtain ⟨n, hn⟩ := checkTerm_complete body
      refine ⟨n, ?_⟩
      intro m le
      simp only [checkDeclarationBody, Environment.lookup, fresh, Option.isSome_none,
        Bool.false_eq_true, ↓reduceIte]
      exact hn m le _ rfl rfl
  | predicate body =>
      obtain ⟨n, hn⟩ := checkPredicate_complete body
      refine ⟨n, ?_⟩
      intro m le
      simp only [checkDeclarationBody, Environment.lookup, fresh, Option.isSome_none,
        Bool.false_eq_true, ↓reduceIte]
      exact hn m le _ rfl rfl
  | @theoremE d type body =>
      obtain ⟨s, below, i, hi⟩ := inferFormula_complete type
      obtain ⟨j, hj⟩ := checkProof_complete
        (c := { functions := d.functions, predicates := d.predicates }) valid .nil body
      refine ⟨max i j, ?_⟩
      intro m le
      simp only [checkDeclarationBody, Environment.lookup, fresh, Option.isSome_none,
        Bool.false_eq_true, ↓reduceIte, CheckResult.bind_eq_ok]
      exact ⟨s, hi m (by omega) _ rfl rfl, hj m (by omega)⟩

/-- **Completeness theorem of declaration checking**: starting from a well-formed environment,
every fresh function, predicate, or theorem with a legal body is accepted at some finite depth.
Every larger depth also succeeds and returns the specified insertion. -/
public theorem checkDeclaration_complete {E d} (valid : EnvironmentWF E)
    (fresh : E[d.name]? = none) (formed : DeclarationWF E d) :
    ∃ n, ∀ m ≥ n, checkDeclaration m E d = .ok (E.insert d.name d) := by
  obtain ⟨n, hn⟩ := checkDeclarationBody_complete valid fresh formed
  refine ⟨n, ?_⟩
  intro m le
  simp only [checkDeclaration, CheckResult.bind_eq_ok, CheckResult.inDeclaration_eq_ok]
  exact ⟨(), hn m le, rfl⟩

/-- Checking any specified valid declaration order succeeds at every sufficiently large depth. -/
public theorem checkDeclarations_complete {E ds F} (valid : EnvironmentWF E)
    (formed : DeclarationsWF E ds F) :
    ∃ n, ∀ m ≥ n, ds.foldlM (checkDeclaration m) E = .ok F := by
  induction formed with
  | nil => exact ⟨0, by intros; rfl⟩
  | cons fresh head tail ih =>
      obtain ⟨i, hi⟩ := checkDeclaration_complete valid fresh head
      obtain ⟨j, hj⟩ := ih (.insert valid fresh head)
      refine ⟨max i j, ?_⟩
      intro m le
      simp only [List.foldlM_cons, CheckResult.bind_eq_ok]
      exact ⟨_, hi m (by omega), hj m (by omega)⟩

/-- A valid ordered environment and an explicit derivable proof eventually pass admission and
proof checking at the same depth, with success at every larger depth. -/
public theorem checkDeclarations_checkProof_complete {ds E} {c : Context} {p A}
    (ordered : DeclarationsWF ∅ ds E)
    (ctx : ContextWF E c.parameters c.locals c.proofs)
    (typed : ProofTyping E c.parameters c.locals c.proofs p A) :
    ∃ n, ∀ m ≥ n, ds.foldlM (checkDeclaration m) ∅ = .ok E ∧ checkProof m E c p A = .ok () := by
  obtain ⟨i, hi⟩ := checkDeclarations_complete .empty ordered
  obtain ⟨j, hj⟩ := checkProof_complete (ordered.valid .empty) ctx typed
  exact ⟨max i j, fun m le => ⟨hi m (by omega), hj m (by omega)⟩⟩

end PRAProver.Core
