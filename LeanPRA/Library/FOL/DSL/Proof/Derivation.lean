module

public meta import LeanPRA.Library.FOL.DSL.Theory

/-!
# Construction of Hilbert derivations

Frontend proof operations expand deduction, generalization, equality reasoning, and universal
instantiation into logical axioms, modus ponens, and primitive generalization. The resulting graph
is translated to numerical proof trees and checked by the common PRA theorems.

- `Derivation` stores formulas, their justifications, and shared proof transformations.
- `deduct` discharges a hypothesis by constructing an implication proof.
- `generalize` and `instantiate` construct universal quantification and its instances.
-/

public meta section

namespace LeanPRA.Library.FOL.DSL

open Lean hiding Term

open Lean.Elab.Command

private partial def sameTerm (env : List (Name × Name)) : TermView → TermView → Bool
  | .var x, .var y => match env.lookup x with
    | some z => z == y
    | none => x == y && !(env.any (fun (_, z) => z == y))
  | .constant i, .constant j => i == j
  | .code L a xs, .code M b ys => L == M && a == b && xs.length == ys.length &&
      (xs.zip ys).all (fun (a, b) => sameTerm env a b)
  | .app i xs, .app j ys => i == j && xs.length == ys.length &&
    (xs.zip ys).all (fun (a, b) => sameTerm env a b)
  | _, _ => false

def FormulaView.equiv : FormulaView → FormulaView → Bool := go [] where
  go env a b := match a, b with
    | .falsum, .falsum => true
    | .code L a xs, .code M b ys => L == M && a == b && xs.length == ys.length &&
        (xs.zip ys).all (fun (a, b) => sameTerm env a b)
    | .equal a b, .equal c d => sameTerm env a c && sameTerm env b d
    | .relation i xs, .relation j ys
    | .parameter i xs, .parameter j ys => i == j && xs.length == ys.length &&
      (xs.zip ys).all (fun (a, b) => sameTerm env a b)
    | .imp a b, .imp c d => go env a c && go env b d
    | .all x a, .all y b => go ((x, y) :: env) a b
    | _, _ => false

inductive SchemaArg where
  | formula (body : FormulaView) (binders : List Name := [])
  | term (value : TermView)
  | tuple (values : List TermView)
  | number (value : Nat)
  deriving BEq, Hashable, Repr, Inhabited

inductive Reason where
  | logical (tag : Nat) (args : List SchemaArg)
  | theory (index : Nat) (actuals : Array FormulaActual) (parameters : List Name)
  | hypothesis (name : Name)
  | proven (proof : Core.Proof)
  | localProof (proof : Core.Proof)
  | lemma (name : Name) (arguments : List FormulaView)
  | mp (implication antecedent : Nat)
  | generalization (binder : Name) (premise : Nat)
  deriving BEq, Hashable, Repr, Inhabited

/-- A question about a derivation step whose answer `Derivation.transforms` stores. -/
inductive Transform where
  | dependency (step : Nat) (hypothesis : Name)
  | variable (step : Nat) (name : Name)
  | deduction (hypothesis : Name) (step : Nat)
  deriving BEq, Hashable

structure Node where
  formula : FormulaView
  reason : Reason
  deriving Repr, Inhabited

structure Derivation where
  nodes : Array Node := #[]
  cache : Std.HashMap (FormulaView × Reason) Nat := {}
  transforms : Std.HashMap Transform Nat := {}
  deriving Inhabited

abbrev DeriveM := StateRefT Derivation CommandElabM

def addNode (a : FormulaView) (r : Reason) : DeriveM Nat := do
  if let some i := (← get).cache[(a, r)]? then return i
  let i := (← get).nodes.size
  modify fun s => { s with nodes := s.nodes.push ⟨a, r⟩, cache := s.cache.insert (a, r) i }
  return i

def conclusion (i : Nat) : DeriveM FormulaView := return (← get).nodes[i]!.formula

def logical (a : FormulaView) (tag : Nat) (args : List SchemaArg) : DeriveM Nat :=
  addNode a (.logical tag args)

def mp (i j : Nat) : DeriveM Nat := do
  let .imp a b ← conclusion i | throwError "modus ponens requires an implication"
  unless a.equiv (← conclusion j) do throwError "modus ponens antecedents disagree"
  addNode b (.mp i j)

def axK (a b : FormulaView) : DeriveM Nat :=
  logical (.imp a (.imp b a)) 0 [.formula a, .formula b, .number 0]

def axS (a b c : FormulaView) : DeriveM Nat :=
  logical (.imp (.imp a (.imp b c)) (.imp (.imp a b) (.imp a c))) 1
    [.formula a, .formula b, .formula c]

def identity (a : FormulaView) : DeriveM Nat := do
  mp (← mp (← axS a (.imp a a) a) (← axK a (.imp a a))) (← axK a a)

partial def dependsOn (i : Nat) (h : Name) : DeriveM Bool := do
  let key := Transform.dependency i h
  if let some result := (← get).transforms[key]? then return result == 1
  let result ← match (← get).nodes[i]!.reason with
  | .hypothesis k => return h == k
  | .mp p q => return (← dependsOn p h) || (← dependsOn q h)
  | .generalization _ p => dependsOn p h
  | _ => return false
  modify fun s => { s with transforms := s.transforms.insert key (if result then 1 else 0) }
  return result

private partial def hypothesisUses (i : Nat) (x : Name) : DeriveM Bool := do
  let key := Transform.variable i x
  if let some result := (← get).transforms[key]? then return result == 1
  let node := (← get).nodes[i]!
  let result ← match node.reason with
  | .hypothesis _ => return node.formula.variables.contains x
  | .mp p q => return (← hypothesisUses p x) || (← hypothesisUses q x)
  | .generalization _ p => hypothesisUses p x
  | _ => return false
  modify fun s => { s with transforms := s.transforms.insert key (if result then 1 else 0) }
  return result

def generalize (x : Name) (i : Nat) : DeriveM Nat := do
  if ← hypothesisUses i x then
    throwError "cannot generalize a position occurring in an active hypothesis"
  addNode (.all x (← conclusion i)) (.generalization x i)

partial def deduct (h : Name) (a : FormulaView) (i : Nat) : DeriveM Nat := do
  let key := Transform.deduction h i
  if let some j := (← get).transforms[key]? then return j
  let b ← conclusion i
  let result ← if !(← dependsOn i h) then mp (← axK b a) i else do
    match (← get).nodes[i]!.reason with
    | .hypothesis _ => identity a
    | .mp p q =>
      let c ← conclusion q
      mp (← mp (← axS a c b) (← deduct h a p)) (← deduct h a q)
    | .generalization x p =>
      if a.variables.contains x then
        throwError "cannot discharge a hypothesis depending on the generalized position"
      let c ← conclusion p
      let q ← generalize x (← deduct h a p)
      let quantifierAxiom ← logical (.imp (.all x (.imp a c)) (.imp a (.all x c))) 4
        [.formula a, .formula c [x], .number 0]
      mp quantifierAxiom q
    | _ => throwError "invalid deduction dependency"
  modify fun s => { s with transforms := s.transforms.insert key result }
  return result

/-- Instantiate the next universal quantifier, preserving any preceding implication premises. -/
partial def instantiate (i : Nat) (t : TermView) : DeriveM Nat := do
  match ← conclusion i with
  | .all x a =>
    let result := a.replace x t
    mp (← logical (.imp (.all x a) result) 3 [.formula a [x],
      if a.variables.contains x then .term t else .number 0, .number 0]) i
  | .imp a _ =>
    let name ← liftCoreM (mkFreshUserName `_folPremise)
    let premise ← addNode a (.hypothesis name)
    deduct name a (← instantiate (← mp i premise) t)
  | _ => throwError "universal instantiation requires a quantifier"

def eqRefl (t : TermView) : DeriveM Nat :=
  logical (.equal t t) 6 [.term t, .number 0, .number 0]

def eqSymm (i : Nat) : DeriveM Nat := do
  let .equal a b ← conclusion i | throwError "equality symmetry requires an equation"
  if a == b then return i
  mp (← logical (.imp (.equal a b) (.equal b a)) 7 [.term a, .term b, .number 0]) i

def eqTrans (i j : Nat) : DeriveM Nat := do
  let .equal a b ← conclusion i | throwError "equality transitivity requires an equation"
  let .equal c d ← conclusion j | throwError "equality transitivity requires an equation"
  unless b == c do throwError "equality transitivity endpoints disagree"
  if a == b then return j
  if c == d then return i
  mp (← mp (← logical (.imp (.equal a b) (.imp (.equal b d) (.equal a d))) 8
    [.term a, .term b, .term d]) i) j

def eqCongr (index : Nat) (proofs : List Nat) : DeriveM Nat := do
  let pairs ← proofs.mapM fun p => do
    let .equal a b ← conclusion p | throwError "function congruence requires equations"
    pure (a, b)
  let xs := pairs.map (·.1)
  let ys := pairs.map (·.2)
  if xs == ys then return ← eqRefl (.app index xs)
  let result := FormulaView.equal (.app index xs) (.app index ys)
  let schema := pairs.foldr (fun (a, b) r => .imp (.equal a b) r) result
  let mut p ← logical schema 9 [.number index, .tuple xs, .tuple ys]
  for q in proofs do p ← mp p q
  return p

end LeanPRA.Library.FOL.DSL
