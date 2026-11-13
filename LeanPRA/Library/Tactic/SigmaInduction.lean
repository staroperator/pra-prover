module

public meta import LeanPRA.Library.Tactic.Witnessing
public meta import LeanPRA.Library.Tactic.Induction

/-!
# Induction for existential PRA goals

`sigma_induction n with | zero => ... | succ k ih => ...` proves a goal of the form
`∃ w, R n w`, where `R` is quantifier-free. Each branch supplies a numerical witness and a proof
of its property. The tactic compiles the witnesses, combines them by primitive recursion, and
proves the resulting quantifier-free invariant with PRA induction.

The tactic uses the current goal and local context. It supports declaration parameters and
introduced numerical variables, including in local and nested proofs. The step hypothesis `ih`
has the original existential form. Branches must use proof forms supported by the witness compiler.
`sigma_induction n with k ih` also accepts two bulleted branches. Generated declarations and the
completed proof pass through the existing PRA checker.
-/

public meta section

namespace LeanPRA.Library.Tactic

open Lean Elab Command LeanPRA.Surface LeanPRA.Surface.Tactic
open LeanPRA.Library.Tactic.Construction

syntax (name := sigmaInductionTac) "sigma_induction " ident " with"
  ppLine "| " &"zero" "=>" ppIndent(colGt praTacticSeq)
  ppLine "| " &"succ" ident ident " =>" ppIndent(colGt praTacticSeq) : praTactic
syntax (name := sigmaInductionBulletsTac) "sigma_induction " ident " with " ident ident
  ppLine "· " ppIndent(colGt praTacticSeq)
  ppLine "· " ppIndent(colGt praTacticSeq) : praTactic

macro_rules
  | `(praTactic| sigma_induction $n:ident with $k:ident $ih:ident
      · $base:praTacticSeq
      · $step:praTacticSeq) =>
    `(praTactic| sigma_induction $n:ident with
      | zero => $base:praTacticSeq
      | succ $k:ident $ih:ident => $step:praTacticSeq)

private def complete (result : Except Metavariable.Failure α) : CommandElabM α :=
  match result with
  | .ok value => pure value
  | .error error => throwError "sigma_induction needs resolved arguments: {error}"

private def checked (result : Core.CheckResult α) : CommandElabM α :=
  match result with
  | .ok value => pure value
  | .error error => throwError "sigma_induction: {error.message}"

-- Substitute local definitions so branch tactics can match expressions beneath their binders.
private def inlineTermLets : Core.Term → Core.Term
  | .letE _ value body => (inlineTermLets body).subst0 (inlineTermLets value)
  | .lam n body => .lam n (inlineTermLets body)
  | .app f a => .app (inlineTermLets f) (inlineTermLets a)
  | .primrec b s => .primrec (inlineTermLets b) (inlineTermLets s)
  | .definition n fs => .definition n (fs.map inlineTermLets)
  | term => term

private def inlinePredicateLets : Core.Predicate → Core.Predicate
  | .letTerm _ _ body | .letPredicate _ _ body => inlinePredicateLets body
  | .lam n body => .lam n (inlinePredicateLets body)
  | .app p a => .app (inlinePredicateLets p) (inlineTermLets a)
  | .equal a b => .equal (inlineTermLets a) (inlineTermLets b)
  | .imp a b => .imp (inlinePredicateLets a) (inlinePredicateLets b)
  | .and a b => .and (inlinePredicateLets a) (inlinePredicateLets b)
  | .or a b => .or (inlinePredicateLets a) (inlinePredicateLets b)
  | .all p => .all (inlinePredicateLets p)
  | .ex p => .ex (inlinePredicateLets p)
  | .definition n fs ps => .definition n (fs.map inlineTermLets) (ps.map inlinePredicateLets)
  | predicate => predicate

private def abstractIndex (context : Core.Context) (index : Core.Term)
    (target : Core.Predicate) : CommandElabM Core.Predicate := do
  match index with
  | .bvar i => return target.rename fun j => if j == i then 0 else j + 1
  | .parameter i =>
    let functions := (List.range context.functions.length).map fun j =>
      if j == i then Core.Term.bvar 0 else .parameter j
    let predicates := (List.range context.predicates.length).map Core.Predicate.parameter
    return target.shift.instantiate functions predicates
  | _ => throwError "sigma_induction requires a numerical variable or declaration parameter"

private def existential (depth : Nat) (type : Core.Predicate) : CommandElabM Core.Predicate := do
  let env := CoreEnvironment.getState (← getEnv)
  let .ex motive ← checked (Core.whnfPredicate depth env type) |
    throwError "sigma_induction requires an existential goal with a quantifier-free body"
  return motive

/-- Compile the base and step witnesses and close the goal by quantifier-free PRA induction. -/
@[pra_tactic sigmaInductionTac]
def evalSigmaInduction : Tactic := fun stx => do
  let `(praTactic| sigma_induction $n:ident with
    | zero => $base:praTacticSeq
    | succ $k:ident $ih:ident => $step:praTacticSeq) := stx | throwUnsupportedSyntax
  let index ← complete (Metavariable.Frontend.completeTerm
    (← Tactic.elaborateTerm (← `(praExpr| $n:ident))))
  let goal ← getGoal
  let target := inlinePredicateLets
    (← complete (Metavariable.Frontend.completePredicate goal.target))
  let context : Core.Context := {
    locals := goal.context.locals
    functions := goal.context.functions.take goal.projection.functions
    predicates := goal.context.predicates.take goal.projection.predicates
    proofs := ← goal.context.proofs.mapM fun p =>
      complete (Metavariable.Frontend.completePredicate p) }
  let family := Core.Predicate.lam n.getId (← abstractIndex context index target)
  let atIndex (value : Core.Term) := Core.betaReducePredicate goal.maxDepth (.app family value)
  let motive ← existential goal.maxDepth (.app family.shift (.bvar 0))
  let signature ← checked (Core.inferPredicate goal.maxDepth goal.environment
    (context.pushLocal 0) motive)
  unless signature == ⟨1, .qf⟩ do
    throwError "sigma_induction requires an existential goal with a quantifier-free body"
  let root := (← getEnv).mainModule ++ `SigmaInduction ++ (← liftCoreM (mkFreshUserName `proof))
  let used := goal.names.used ++ [n.getId, k.getId, ih.getId]
  let fresh (stem : String) := Id.run do
    let mut name := Name.mkSimple stem
    while used.contains name do name := name.appendAfter "_"
    return mkIdent name
  -- Preserve references to outer values when branch names shadow them.
  let visible := goal.names.locals ++ goal.names.functions ++ goal.names.predicates ++
    goal.names.termAliases.map (·.1) ++ goal.names.predicateAliases.map (·.1)
  let shadowed := ([n.getId, k.getId, ih.getId].map Name.eraseMacroScopes).eraseDups.filter
    visible.contains
  let protect : TacticM Unit := do
    for (name, i) in shadowed.zipIdx do
      let alias := fresh s!"_sigmaOriginal{i}"
      Tactic.refine (← `(praExpr| let $alias:ident := $(mkIdent name):ident; ?_))
  let view := goal.projection
  let predecessor := fresh "_sigmaIndex"
  let witness := fresh "_sigmaWitness"
  let property := fresh "_sigmaProperty"
  let baseType := atIndex .zero
  let baseProof ← Tactic.prove (view.decodePredicate baseType) base do
    protect
    Tactic.refine (← `(praExpr| let $n:ident := 0; ?_))
    Tactic.evalTacticSeq base
  let baseProof ← complete (Metavariable.Frontend.completeProof baseProof)
  let (baseCode, _, baseChecked) ← Witnessing.compileProof
    (root ++ `base) context baseType baseProof
  let previous := Core.betaReducePredicate goal.maxDepth (.app family.shift.shift (.bvar 1))
  let previousMotive ← existential goal.maxDepth previous
  let premise := Core.Predicate.app previousMotive (.bvar 0)
  let next := Core.Predicate.app family.shift.shift (.app .succ (.bvar 1))
  let stepType := Core.Predicate.all (.lam predecessor.getId
    (.all (.lam witness.getId (.imp premise next))))
  let stepProof ← Tactic.prove (view.decodePredicate stepType) step do
    protect
    Tactic.refine (← `(praExpr|
      fun $predecessor:ident $witness:ident $property:ident => ?_))
    -- The induction hypothesis pairs the previous witness with its property.
    Tactic.assert ih.getId.eraseMacroScopes (view.decodePredicate previous)
      (.existsIntro (view.decodePredicate previousMotive) (.bvar 0) (.hyp 0)) ih
    Tactic.refine (← `(praExpr|
      let $n:ident := S $predecessor:ident; let $k:ident := $predecessor:ident; ?_))
    Tactic.evalTacticSeq step
  let stepProof ← complete (Metavariable.Frontend.completeProof stepProof)
  let (stepCode, _, stepChecked) ← Witnessing.compileProof
    (root ++ `step) context stepType stepProof
  let code := Core.Term.app (.primrec baseCode stepCode) index
  let previousCode := Core.Term.app (.primrec baseCode.shift stepCode.shift) (.bvar 0)
  let invariant := Core.Predicate.lam k.getId (.app motive previousCode)
  let stepCheck := Core.Proof.impElim
    (.forallElim (.forallElim (shiftProof stepChecked 1 1) (.bvar 0)) previousCode) (.hyp 0)
  let premise := Core.Predicate.app invariant.shift (.bvar 0)
  let conclusion := Core.Predicate.app invariant.shift (.app .succ (.bvar 0))
  let branch := Core.Proof.forallIntro k.getId (.lam k.getId (.imp premise conclusion))
    (.impIntro property.getId premise stepCheck)
  let proof := Core.Proof.forallElim
    (.impElim (.impElim (.induction invariant) baseChecked) branch) index
  let goalMotive ← existential goal.maxDepth target
  Tactic.close (goal.projection.decodeProof (.existsIntro goalMotive code proof))

end LeanPRA.Library.Tactic
