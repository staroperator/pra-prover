module

public meta import LeanPRA.Surface.Metavariable.Syntax

/-!
# Variable shifting and substitution

Variable shifting, substitution, and parameter instantiation for expressions with metavariables:

- `Term.transform` and `Predicate.transform` map local variables and declaration parameters while
  tracking the number of enclosing binders.
- `shift`, `subst0`, and `instantiate` shift free variables, substitute for `bvar 0`, and replace
  declaration parameters with arguments.
- `Proof.transform`, `Proof.shift`, and `Proof.subst` transform proofs and their context arguments.
- `termMetas`, `predicateMetas`, and the `isComplete` functions inspect unresolved expressions.
- `Context.pushLocal` and `Context.pushProof` extend a typing context with a local variable or
  proof hypothesis.

Numerical and predicate transformations leave their `mvar` nodes unchanged. Proof transformations
traverse the explicit context arguments of proof metavariables. Metavariable assignment resolution
adjusts local variable indices separately against each metavariable's recorded scope.
-/

public meta section
namespace LeanPRA.Surface.Metavariable
open Core hiding Term Predicate Proof Context

/-- Replace local variables and declaration parameters in a term, passing `depth` (the number of
enclosing binders) to `onLocal` and `parameter`. -/
def Term.transform (onLocal parameter : Nat → Nat → Term) (depth : Nat := 0) : Term → Term
  | .bvar i => onLocal depth i
  | .parameter i => parameter depth i
  | .mvar i => .mvar i
  | .zero => .zero
  | .succ => .succ
  | .lam n t => .lam n (t.transform onLocal parameter (depth + 1))
  | .app f a => .app (f.transform onLocal parameter depth) (a.transform onLocal parameter depth)
  | .letE n a b => .letE n (a.transform onLocal parameter depth)
      (b.transform onLocal parameter (depth + 1))
  | .primrec b s => .primrec (b.transform onLocal parameter depth)
      (s.transform onLocal parameter depth)
  | .definition n fs => .definition n (fs.map (Term.transform onLocal parameter depth))

/-- Add `count` to free variable indices at or above `cutoff`. -/
def Term.shift (t : Term) (count : Nat := 1) (cutoff : Nat := 0) : Term :=
  t.transform (fun depth i => .bvar (if i < depth + cutoff then i else i + count))
    (fun _ i => .parameter i)

/-- Replace `bvar 0` with `argument` and decrement higher free variable indices. -/
def Term.subst0 (t argument : Term) : Term :=
  t.transform (fun depth i => if i < depth then .bvar i
    else if i == depth then argument.shift depth else .bvar (i - 1)) (fun _ i => .parameter i)

/-- Replace function parameters with `actuals`, shifting them beneath enclosing binders. -/
def Term.instantiate (actuals : List Term) (depth : Nat := 0) (t : Term) : Term :=
  t.transform (fun _ i => .bvar i)
    (fun depth i => (actuals[i]?.getD (.parameter i)).shift depth) depth

/-- Replace local variables, function parameters, and predicate parameters in a predicate, passing
`depth` (the number of enclosing binders) to each callback. -/
def Predicate.transform (onLocal function : Nat → Nat → Term)
    (predicate : Nat → Nat → Predicate) (depth : Nat := 0) : Predicate → Predicate
  | .false => .false
  | .true => .true
  | .equal a b => .equal (a.transform onLocal function depth) (b.transform onLocal function depth)
  | .imp a b => .imp (a.transform onLocal function predicate depth)
      (b.transform onLocal function predicate depth)
  | .and a b => .and (a.transform onLocal function predicate depth)
      (b.transform onLocal function predicate depth)
  | .or a b => .or (a.transform onLocal function predicate depth)
      (b.transform onLocal function predicate depth)
  | .all p => .all (p.transform onLocal function predicate depth)
  | .ex p => .ex (p.transform onLocal function predicate depth)
  | .parameter i => predicate depth i
  | .mvar i => .mvar i
  | .lam n p => .lam n (p.transform onLocal function predicate (depth + 1))
  | .app p a => .app (p.transform onLocal function predicate depth) (a.transform onLocal function
      depth)
  | .letTerm n a p => .letTerm n (a.transform onLocal function depth)
      (p.transform onLocal function predicate depth)
  | .letPredicate n p q => .letPredicate n (p.transform onLocal function predicate depth)
      (q.transform onLocal function predicate depth)
  | .definition n fs ps => .definition n (fs.map (Term.transform onLocal function depth))
      (ps.map (Predicate.transform onLocal function predicate depth))

/-- Add `count` to free variable indices at or above `cutoff` in a predicate. -/
def Predicate.shift (p : Predicate) (count : Nat := 1) (cutoff : Nat := 0) : Predicate :=
  p.transform (fun depth i => .bvar (if i < depth + cutoff then i else i + count))
    (fun _ i => .parameter i) (fun _ i => .parameter i)

/-- Replace `bvar 0` with `argument` and decrement higher free variable indices in a predicate. -/
def Predicate.subst0 (p : Predicate) (argument : Term) : Predicate :=
  p.transform (fun depth i => if i < depth then .bvar i
    else if i == depth then argument.shift depth else .bvar (i - 1))
    (fun _ i => .parameter i) (fun _ i => .parameter i)

/-- Replace function and predicate parameters with `functions` and `predicates`, shifting them
beneath enclosing binders. -/
def Predicate.instantiate (functions : List Term) (predicates : List Predicate)
    (depth : Nat := 0) (p : Predicate) : Predicate :=
  p.transform (fun _ i => .bvar i)
    (fun depth i => (functions[i]?.getD (.parameter i)).shift depth)
    (fun depth i => (predicates[i]?.getD (.parameter i)).shift depth) depth

/-- Transform numerical variables and proof hypotheses, tracking their separate binder depths. -/
def Proof.transform (onLocal : Nat → Nat → Term) (onHyp : Nat → Nat → Nat → Proof)
    (localDepth proofDepth : Nat := 0) : Proof → Proof := fun p =>
    let term := Term.transform onLocal (fun _ i => .parameter i) localDepth
    let pred := Predicate.transform onLocal (fun _ i => .parameter i)
      (fun _ i => .parameter i) localDepth
    match p with
    | .theoremE n fs ps => .theoremE n (fs.map term) (ps.map pred)
    | .impIntro n a p =>
      .impIntro n (pred a) (Proof.transform onLocal onHyp localDepth (proofDepth + 1) p)
    | .impElim p q =>
      .impElim (Proof.transform onLocal onHyp localDepth proofDepth p)
        (Proof.transform onLocal onHyp localDepth proofDepth q)
    | .andIntro p q =>
      .andIntro (Proof.transform onLocal onHyp localDepth proofDepth p)
        (Proof.transform onLocal onHyp localDepth proofDepth q)
    | .andLeft a b => .andLeft (pred a) (pred b)
    | .andRight a b => .andRight (pred a) (pred b)
    | .orLeft a b => .orLeft (pred a) (pred b)
    | .orRight a b => .orRight (pred a) (pred b)
    | .orElim a b c => .orElim (pred a) (pred b) (pred c)
    | .falseElim a => .falseElim (pred a)
    | .forallIntro n a p =>
      .forallIntro n (pred a) (Proof.transform onLocal onHyp (localDepth + 1) proofDepth p)
    | .forallElim p a =>
      .forallElim (Proof.transform onLocal onHyp localDepth proofDepth p) (term a)
    | .existsIntro a t p =>
      .existsIntro (pred a) (term t)
        (Proof.transform onLocal onHyp localDepth proofDepth p)
    | .existsElim a b => .existsElim (pred a) (pred b)
    | .letE n a p q =>
      .letE n (pred a) (Proof.transform onLocal onHyp localDepth proofDepth p)
        (Proof.transform onLocal onHyp localDepth (proofDepth + 1) q)
    | .letTerm n a p =>
      .letTerm n (term a) (Proof.transform onLocal onHyp localDepth proofDepth p)
    | .letPredicate n a p =>
      .letPredicate n (pred a) (Proof.transform onLocal onHyp localDepth proofDepth p)
    | .ascribe a p =>
      .ascribe (pred a) (Proof.transform onLocal onHyp localDepth proofDepth p)
    | .eqRefl => .eqRefl
    | .eqSubst a => .eqSubst (pred a)
    | .succNeZero => .succNeZero
    | .succInj => .succInj
    | .lem a => .lem (pred a)
    | .induction a => .induction (pred a)
    | .hyp i => onHyp localDepth proofDepth i
    | .mvar id ts ps => .mvar id (ts.map term)
      (ps.map (Proof.transform onLocal onHyp localDepth proofDepth))
    | .trueIntro => .trueIntro

/-- Weaken a proof by adding numerical locals and hypotheses outside its own binders. Context
arguments of metavariables are weakened along with ordinary variables. -/
def Proof.shift (p : Proof) (locals hypotheses : Nat) : Proof :=
  p.transform (fun depth i => .bvar (if i < depth then i else i + locals))
    (fun _ depth i => .hyp (if i < depth then i else i + hypotheses))

/-- Substitute the free numerical variables and hypotheses of a proof. Substitution lifts its
arguments when crossing binders to prevent capture. -/
def Proof.subst (p : Proof) (terms : Nat → Term) (proofs : Nat → Proof) : Proof :=
  p.transform (fun depth i => if i < depth then .bvar i else (terms (i - depth)).shift depth)
    (fun locals depth i => if i < depth then .hyp i else (proofs (i - depth)).shift locals depth)

/-- Push a local variable of `arity` and shift free variable indices in `proofs`. -/
def Context.pushLocal (context : Context) (arity : Arity) : Context :=
  { context with locals := arity :: context.locals, proofs := context.proofs.map Predicate.shift }

/-- Push a well-formed proof hypothesis. -/
def Context.pushProof (context : Context) (predicate : Predicate) : Context :=
  { context with proofs := predicate :: context.proofs }

/-- List the numerical metavariable indices occurring in a term. -/
def termMetas : Term → List Nat
  | .mvar i => [i]
  | .lam _ b => termMetas b
  | .app f a | .letE _ f a => termMetas f ++ termMetas a
  | .primrec b s => termMetas b ++ termMetas s
  | .definition _ fs => fs.flatMap termMetas
  | _ => []

/-- List the numerical and predicate metavariable indices occurring in a predicate. -/
def predicateMetas : Predicate → List Nat × List Nat
  | .mvar i => ([], [i])
  | .equal a b => (termMetas a ++ termMetas b, [])
  | .imp a b | .and a b | .or a b | .letPredicate _ a b =>
    let a := predicateMetas a; let b := predicateMetas b
    (a.1 ++ b.1, a.2 ++ b.2)
  | .all p | .ex p | .lam _ p => predicateMetas p
  | .app p a | .letTerm _ a p =>
    let p := predicateMetas p; (termMetas a ++ p.1, p.2)
  | .definition _ fs ps =>
    let ps := ps.map predicateMetas
    (fs.flatMap termMetas ++ ps.flatMap (·.1), ps.flatMap (·.2))
  | _ => ([], [])

/-- Whether `t` contains no metavariables. -/
def Term.isComplete (t : Term) : Bool :=
  (Metavariable.termMetas t).isEmpty

/-- Whether `t` contains no numerical or predicate metavariables. -/
def Predicate.isComplete (t : Predicate) : Bool :=
  let (fs, ps) := Metavariable.predicateMetas t
  fs.isEmpty && ps.isEmpty

/-- Whether a proof and all of its embedded arguments contain no metavariables. -/
def Proof.isComplete : Proof → Bool
  | .mvar .. => false
  | .hyp _ | .trueIntro | .eqRefl | .succNeZero | .succInj => true
  | .theoremE _ fs ps => fs.all Term.isComplete && ps.all Predicate.isComplete
  | .impIntro _ a p | .forallIntro _ a p | .letPredicate _ a p | .ascribe a p =>
    Predicate.isComplete a && Proof.isComplete p
  | .impElim p q | .andIntro p q => Proof.isComplete p && Proof.isComplete q
  | .andLeft a b | .andRight a b | .orLeft a b | .orRight a b | .existsElim a b =>
    Predicate.isComplete a && Predicate.isComplete b
  | .orElim a b c => Predicate.isComplete a && Predicate.isComplete b && Predicate.isComplete c
  | .forallElim p t | .letTerm _ t p => Proof.isComplete p && Term.isComplete t
  | .existsIntro a t p =>
    Predicate.isComplete a && Term.isComplete t && Proof.isComplete p
  | .letE _ a p q => Predicate.isComplete a && Proof.isComplete p && Proof.isComplete q
  | .falseElim a | .eqSubst a | .lem a | .induction a => Predicate.isComplete a

end LeanPRA.Surface.Metavariable
