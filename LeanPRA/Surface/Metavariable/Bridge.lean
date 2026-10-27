module

public meta import LeanPRA.Surface.Metavariable.Substitution
public meta import LeanPRA.Core.Checker

/-!
# Reusing Core operations during elaboration

Temporary encoding of metavariables as Core parameters for typing, reduction, and display:

- `Projection.encodeTerm` and `Projection.encodePredicate` map metavariables to Core parameters.
- `Projection.decodeTerm` and `Projection.decodePredicate` map those Core parameters back to
  metavariables.
- `Bridge` runs Core typing, conversion, and reduction on encoded expressions.
- `Projection.substTerm` and `Projection.substPredicate` run Core's numerical substitution on
  encoded expressions.

In a `Projection`, parameter indices below `functions` and `predicates` belong to the declaration
being elaborated; indices at or above those counts represent the session's metavariables. Callers
extend the Core context with the metavariables' types before calling Core operations. Final
declaration checking runs after all metavariables are resolved and uses only the declaration's own
parameters.
-/

public meta section
namespace LeanPRA.Surface.Metavariable
open Core hiding Term Predicate Proof Context

/-- Counts of declaration function and predicate parameters, where indices at or above these counts
encode the session's metavariables in Core syntax. -/
structure Projection where
  functions : Nat
  predicates : Nat

/-- Encode a term as a `Core.Term`, mapping `.mvar i` to `.parameter (view.functions + i)`. -/
def Projection.encodeTerm (view : Projection) : Term → Core.Term
  | .mvar i => .parameter (view.functions + i)
  | .bvar i => .bvar i
  | .parameter i => .parameter i
  | .zero => .zero
  | .succ => .succ
  | .lam n b => .lam n (view.encodeTerm b)
  | .app f a => .app (view.encodeTerm f) (view.encodeTerm a)
  | .letE n a b => .letE n (view.encodeTerm a) (view.encodeTerm b)
  | .primrec b s n => .primrec (view.encodeTerm b) (view.encodeTerm s) (view.encodeTerm n)
  | .definition n fs => .definition n (fs.map (view.encodeTerm))

/-- Encode a predicate as a `Core.Predicate`, mapping `.mvar i` to
`.parameter (view.predicates + i)`. -/
def Projection.encodePredicate (view : Projection) : Predicate → Core.Predicate
  | .mvar i => .parameter (view.predicates + i)
  | .false => .false
  | .true => .true
  | .equal a b => .equal (view.encodeTerm a) (view.encodeTerm b)
  | .imp a b => .imp (view.encodePredicate a) (view.encodePredicate b)
  | .and a b => .and (view.encodePredicate a) (view.encodePredicate b)
  | .or a b => .or (view.encodePredicate a) (view.encodePredicate b)
  | .all p => .all (view.encodePredicate p)
  | .ex p => .ex (view.encodePredicate p)
  | .parameter i => .parameter i
  | .lam n p => .lam n (view.encodePredicate p)
  | .app p a => .app (view.encodePredicate p) (view.encodeTerm a)
  | .letTerm n a p => .letTerm n (view.encodeTerm a) (view.encodePredicate p)
  | .letPredicate n p q => .letPredicate n (view.encodePredicate p) (view.encodePredicate q)
  | .definition n fs ps => .definition n (fs.map (view.encodeTerm)) (ps.map (view.encodePredicate))

/-- Decode a `Core.Term`, mapping parameter indices at or above `view.functions` back to `.mvar`. -/
def Projection.decodeTerm (view : Projection) : Core.Term → Term
  | .bvar i => .bvar i
  | .parameter i => if i < view.functions then .parameter i else .mvar (i - view.functions)
  | .zero => .zero
  | .succ => .succ
  | .lam n b => .lam n (view.decodeTerm b)
  | .app f a => .app (view.decodeTerm f) (view.decodeTerm a)
  | .letE n a b => .letE n (view.decodeTerm a) (view.decodeTerm b)
  | .primrec b s n => .primrec (view.decodeTerm b) (view.decodeTerm s) (view.decodeTerm n)
  | .definition n fs => .definition n (fs.map (view.decodeTerm))

/-- Decode a `Core.Predicate`, mapping parameter indices at or above `view.predicates` back to
`.mvar`. -/
def Projection.decodePredicate (view : Projection) : Core.Predicate → Predicate
  | .false => .false
  | .true => .true
  | .equal a b => .equal (view.decodeTerm a) (view.decodeTerm b)
  | .imp a b => .imp (view.decodePredicate a) (view.decodePredicate b)
  | .and a b => .and (view.decodePredicate a) (view.decodePredicate b)
  | .or a b => .or (view.decodePredicate a) (view.decodePredicate b)
  | .all p => .all (view.decodePredicate p)
  | .ex p => .ex (view.decodePredicate p)
  | .parameter i => if i < view.predicates then .parameter i else .mvar (i - view.predicates)
  | .lam n p => .lam n (view.decodePredicate p)
  | .app p a => .app (view.decodePredicate p) (view.decodeTerm a)
  | .letTerm n a p => .letTerm n (view.decodeTerm a) (view.decodePredicate p)
  | .letPredicate n p q => .letPredicate n (view.decodePredicate p) (view.decodePredicate q)
  | .definition n fs ps => .definition n (fs.map (view.decodeTerm)) (ps.map (view.decodePredicate))

/-- Encode a proof as a `Core.Proof`, rejecting unresolved proof metavariables.
-/
def Projection.encodeProof (view : Projection) : Proof → Except String Core.Proof
  | .mvar id _ _ => throw s!"unresolved proof metavariable ?p{id}"
  | .hyp index => do
    return .hyp index
  | .trueIntro => do
    return .trueIntro
  | .theoremE name functions predicates => do
    return .theoremE name (functions.map view.encodeTerm)
        (predicates.map view.encodePredicate)
  | .impIntro binderName antecedent body => do
    return .impIntro binderName (view.encodePredicate antecedent)
        (← view.encodeProof body)
  | .impElim function argument => do
    return .impElim (← view.encodeProof function) (← view.encodeProof argument)
  | .andIntro left right => do
    return .andIntro (← view.encodeProof left) (← view.encodeProof right)
  | .andLeft pair => do
    return .andLeft (← view.encodeProof pair)
  | .andRight pair => do
    return .andRight (← view.encodeProof pair)
  | .orLeft other proof => do
    return .orLeft (view.encodePredicate other) (← view.encodeProof proof)
  | .orRight other proof => do
    return .orRight (view.encodePredicate other) (← view.encodeProof proof)
  | .orElim leftName rightName target scrutinee left right => do
    return .orElim leftName rightName
        (view.encodePredicate target) (← view.encodeProof scrutinee) (← view.encodeProof left)
        (← view.encodeProof right)
  | .falseElim target proof => do
    return .falseElim (view.encodePredicate target) (← view.encodeProof proof)
  | .forallIntro binderName motive body => do
    return .forallIntro binderName (view.encodePredicate motive)
        (← view.encodeProof body)
  | .forallElim proof argument => do
    return .forallElim (← view.encodeProof proof) (view.encodeTerm argument)
  | .existsIntro motive witness proof => do
    return .existsIntro (view.encodePredicate motive)
        (view.encodeTerm witness) (← view.encodeProof proof)
  | .existsElim variableName hypothesisName target scrutinee body => do
    return .existsElim variableName
        hypothesisName (view.encodePredicate target) (← view.encodeProof scrutinee)
        (← view.encodeProof body)
  | .letE binderName type value body => do
    return .letE binderName (view.encodePredicate type)
        (← view.encodeProof value) (← view.encodeProof body)
  | .letTerm binderName value body => do
    return .letTerm binderName (view.encodeTerm value)
        (← view.encodeProof body)
  | .letPredicate binderName value body => do
    return .letPredicate binderName (view.encodePredicate value)
        (← view.encodeProof body)
  | .ascribe type proof => do
    return .ascribe (view.encodePredicate type) (← view.encodeProof proof)
  | .eqRefl term => do
    return .eqRefl (view.encodeTerm term)
  | .eqSubst motive equality proof => do
    return .eqSubst (view.encodePredicate motive) (← view.encodeProof equality)
      (← view.encodeProof proof)
  | .succNeZero term => do
    return .succNeZero (view.encodeTerm term)
  | .succInj proof => do
    return .succInj (← view.encodeProof proof)
  | .lem formula => do
    return .lem (view.encodePredicate formula)
  | .induction variableName hypothesisName motive base step argument => do
    return .induction variableName
        hypothesisName (view.encodePredicate motive) (← view.encodeProof base)
        (← view.encodeProof step)
        (view.encodeTerm argument)

/-- Encode a typing context as a `Core.Context` by encoding its proof hypotheses. -/
def Projection.encodeContext (view : Projection) (ctx : Context) : Core.Context :=
  { locals := ctx.locals, functions := ctx.functions, predicates := ctx.predicates,
    proofs := ctx.proofs.map view.encodePredicate }

/-- Encode a diagnostic subject, rejecting unresolved proof metavariables. -/
def Projection.encodeSubject (view : Projection) : Subject → Except String Core.CheckSubject
  | .term t => return .term (view.encodeTerm t)
  | .predicate p => return .predicate (view.encodePredicate p)
  | .proof p => return .proof (← view.encodeProof p)

/-- Convert a `Core.Term` to a Surface `Term`, keeping all declaration parameters as `.parameter`.
-/
def Term.ofCore : Core.Term → Term
  | .bvar i => .bvar i
  | .parameter i => .parameter i
  | .zero => .zero
  | .succ => .succ
  | .lam n b => .lam n (Term.ofCore b)
  | .app f a => .app (Term.ofCore f) (Term.ofCore a)
  | .letE n a b => .letE n (Term.ofCore a) (Term.ofCore b)
  | .primrec b s n => .primrec (Term.ofCore b) (Term.ofCore s) (Term.ofCore n)
  | .definition n fs => .definition n (fs.map (Term.ofCore))

/-- Convert a `Core.Predicate` to a Surface `Predicate`, keeping all declaration parameters as
`.parameter`. -/
def Predicate.ofCore : Core.Predicate → Predicate
  | .false => .false
  | .true => .true
  | .equal a b => .equal (Term.ofCore a) (Term.ofCore b)
  | .imp a b => .imp (Predicate.ofCore a) (Predicate.ofCore b)
  | .and a b => .and (Predicate.ofCore a) (Predicate.ofCore b)
  | .or a b => .or (Predicate.ofCore a) (Predicate.ofCore b)
  | .all p => .all (Predicate.ofCore p)
  | .ex p => .ex (Predicate.ofCore p)
  | .parameter i => .parameter i
  | .lam n p => .lam n (Predicate.ofCore p)
  | .app p a => .app (Predicate.ofCore p) (Term.ofCore a)
  | .letTerm n a p => .letTerm n (Term.ofCore a) (Predicate.ofCore p)
  | .letPredicate n p q => .letPredicate n (Predicate.ofCore p) (Predicate.ofCore q)
  | .definition n fs ps => .definition n (fs.map (Term.ofCore)) (ps.map (Predicate.ofCore))

namespace Bridge
/-- Check that `t` has arity `k` in the encoded context. -/
def checkTerm (view : Projection) (depth : Nat) (env : Environment) (ctx : Context)
    (t : Term) (k : Nat) :=
  Core.checkTerm depth env (view.encodeContext ctx) (view.encodeTerm t) k

/-- Check that `t` has signature `k` in the encoded context. -/
def checkPredicate (view : Projection) (depth : Nat) (env : Environment) (ctx : Context)
    (t : Predicate) (k : PredicateSignature) :=
  Core.checkPredicate depth env (view.encodeContext ctx) (view.encodePredicate t) k

-- Unfold one head definition or contract one head beta/let redex so the solver can compare
-- intermediate definitions before unfolding further; `primrec` delegates to `Core.whnfTerm`.
private def termHeadStep : Nat → Core.Environment → Core.Term → Core.CheckResult Core.Term
  | 0, _, _ => Core.exhausted
  | depth + 1, env, t => match t with
    | .definition name fs =>
      match env.lookup name with
      | some (.function d) => pure (d.body.instantiate fs)
      | _ => Core.whnfTerm (depth + 1) env t
    | .app (.lam _ body) argument => pure (body.subst0 argument)
    | .app f a => return .app (← termHeadStep depth env f) a
    | .letE _ value body => pure (body.subst0 value)
    | .primrec .. => Core.whnfTerm (depth + 1) env t
    | _ => pure t

/-- Unfold one head definition or reduce one head step in `t`, leaving other subterms unchanged. -/
def exposeTerm (view : Projection) (depth : Nat) (env : Environment) (t : Term) :=
  (termHeadStep depth env (view.encodeTerm t)).map view.decodeTerm

/-- Check whether `a` and `b` are definitionally equal at arity `k`. -/
def equalTerms (view : Projection) (depth : Nat) (env : Environment) (k : Nat) (a b : Term) :=
  Core.equalTerms depth env k (view.encodeTerm a) (view.encodeTerm b)

/-- Check whether `a` and `b` are definitionally equal at arity `k`. -/
def equalPredicates (view : Projection) (depth : Nat) (env : Environment) (k : Nat)
    (a b : Predicate) :=
  Core.equalPredicates depth env k (view.encodePredicate a) (view.encodePredicate b)

private def predicateHeadStep : Nat → Core.Environment → Core.Predicate →
    Core.CheckResult Core.Predicate
  | 0, _, _ => Core.exhausted
  | depth + 1, env, p => match p with
    | .definition name fs ps =>
      match env.lookup name with
      | some (.predicate d) => pure (d.body.instantiate fs ps)
      | _ => Core.whnfPredicate (depth + 1) env p
    | .app (.lam _ body) argument => pure (body.subst0 argument)
    | .app f a => return .app (← predicateHeadStep depth env f) a
    | .letTerm _ _ body | .letPredicate _ _ body => pure body
    | _ => pure p

/-- Unfold one head predicate definition or reduce one head step in `p`. -/
def exposePredicate (view : Projection) (depth : Nat) (env : Environment) (p : Predicate) :=
  (predicateHeadStep depth env (view.encodePredicate p)).map view.decodePredicate

/-- Infer the arity of `value` in the encoded context. -/
def termType (view : Projection) (depth : Nat) (env : Environment) (ctx : Context)
    (value : Term) : CheckResult Arity :=
  (Core.inferTerm depth env (view.encodeContext ctx) (view.encodeTerm value))

/-- Infer the signature of `value` in the encoded context. -/
def predicateType (view : Projection) (depth : Nat) (env : Environment) (ctx : Context)
    (value : Predicate) : CheckResult PredicateSignature :=
  (Core.inferPredicate depth env (view.encodeContext ctx) (view.encodePredicate value))

/-- Check that `value` has arity `0` and return its formula sort. -/
def formulaSort (view : Projection) (depth : Nat) (env : Environment) (ctx : Context)
    (value : Predicate) : CheckResult FormulaSort :=
  (Core.inferFormula depth env (view.encodeContext ctx) (view.encodePredicate value))

/-- Infer the formula proved by `value` and decode argument metavariables in the result. The outer
error reports an unresolved proof metavariable; the inner result preserves Core diagnostics. -/
def proofType (view : Projection) (depth : Nat) (env : Environment) (ctx : Context)
    (value : Proof) : Except String (CheckResult Predicate) := do
  let value ← view.encodeProof value
  return (Core.inferProof depth env (view.encodeContext ctx) value).map view.decodePredicate

/-- Normalize a formula `value` and decode any metavariables in the result. -/
def reduceFormula (view : Projection) (depth : Nat) (env : Environment) (value : Predicate) :
    CheckResult Predicate :=
  (Core.reduceFormula depth env (view.encodePredicate value)).map view.decodePredicate

/-- Reduce `value` to weak head normal form and decode any metavariables in the result. -/
def whnfPredicate (view : Projection) (depth : Nat) (env : Environment) (value : Predicate) :
    CheckResult Predicate :=
  (Core.whnfPredicate depth env (view.encodePredicate value)).map view.decodePredicate

/-- Normalize `value` at `arity` and decode any metavariables in the result. -/
def reduceTerm (view : Projection) (depth : Nat) (env : Environment) (arity : Nat) (value : Term)
    : CheckResult Term :=
  (Core.reduceTerm depth env arity (view.encodeTerm value)).map view.decodeTerm

/-- Contract beta redexes in `value` for display, preserving metavariable indices. -/
def betaReduceTerm (view : Projection) (depth : Nat) (value : Term) : Term :=
  view.decodeTerm (Core.betaReduceTerm depth (view.encodeTerm value))

/-- Contract beta redexes in `value` for display, preserving metavariable indices. -/
def betaReducePredicate (view : Projection) (depth : Nat) (value : Predicate) : Predicate :=
  view.decodePredicate (Core.betaReducePredicate depth (view.encodePredicate value))

end Bridge

/-- Substitute local variables in `t` using `Core.Term.subst`, preserving metavariables. -/
def Projection.substTerm (view : Projection) (t : Term) (s : Nat → Term) : Term :=
  view.decodeTerm ((view.encodeTerm t).subst (fun i => view.encodeTerm (s i)))

/-- Substitute local variables in `t` using `Core.Predicate.subst`, preserving metavariables. -/
def Projection.substPredicate (view : Projection) (t : Predicate) (s : Nat → Term) : Predicate :=
  view.decodePredicate ((view.encodePredicate t).subst (fun i => view.encodeTerm (s i)))

/-- Shift free local variable indices in `t` by `1` for comparison under a binder. -/
def Projection.shiftTerm (view : Projection) (t : Term) : Term :=
  view.decodeTerm (view.encodeTerm t).shift

/-- Shift free local variable indices in `p` by `1` for comparison under a binder. -/
def Projection.shiftPredicate (view : Projection) (p : Predicate) : Predicate :=
  view.decodePredicate (view.encodePredicate p).shift

end LeanPRA.Surface.Metavariable
