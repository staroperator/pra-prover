module

public import LeanPRA.Library.FOL.Arithmetic.PA

/-!
# Polynomial equalities in PA

`pring` proves equalities of arithmetic terms in `PA` by expanding successors as `1 + a`,
distributing products over sums, and sorting sums and products into a canonical order. Each
normalization step instantiates a theorem of `Q` or `PA` and combines the resulting equality
derivations by congruence, transitivity, and symmetry.
-/

public meta section

namespace LeanPRA.Library.FOL.ArithmeticTactic

open Lean Elab Command LeanPRA.Surface LeanPRA.Surface.Tactic

open LeanPRA.Library.FOL.DSL LeanPRA.Library.FOL.DSL.TacticSupport

private def zero : TermView := .constant 0

private def one : TermView := .app 0 [zero]

private abbrev Laws := List (Name × Nat)

private def law (laws : Laws) (name : Name) (args : List TermView) : DeriveM Nat := do
  let some p := laws.lookup name | throwError "missing arithmetic law {name}"
  args.foldlM instantiate p

private def rhs (p : Nat) : DeriveM TermView := do
  let .equal _ b ← conclusion p | throwError "expected an arithmetic equality"
  return b

private def lexicographic {α : Type} (order : α → α → Ordering) : List α → List α → Ordering
  | [], [] => .eq
  | [], _ => .lt
  | _, [] => .gt
  | a :: as, b :: bs => (order a b).then (lexicographic order as bs)

/-- A total order on numerical terms: by constructor, then by the arguments from left to right. -/
private partial def codeOrder (a b : Core.Term) : Ordering :=
  let rank : Core.Term → Nat
    | .bvar _ => 0 | .parameter _ => 1 | .zero => 2 | .succ => 3 | .lam .. => 4 | .app .. => 5
    | .letE .. => 6 | .primrec .. => 7 | .definition .. => 8
  match a, b with
  | .bvar i, .bvar j | .parameter i, .parameter j => compare i j
  | .lam n a, .lam m b => (n.cmp m).then (codeOrder a b)
  | .app f a, .app g b => (codeOrder f g).then (codeOrder a b)
  | .letE n a b, .letE m c d => (n.cmp m).then ((codeOrder a c).then (codeOrder b d))
  | .primrec a b, .primrec c d => (codeOrder a c).then (codeOrder b d)
  | .definition n fs, .definition m gs => (n.cmp m).then (lexicographic codeOrder fs gs)
  | a, b => compare (rank a) (rank b)

/-- A total order on object terms, used to sort the arguments of sums and products. -/
private partial def termOrder (a b : TermView) : Ordering :=
  let rank : TermView → Nat
    | .app .. => 0 | .code .. => 1 | .constant _ => 2 | .var _ => 3 | .parameter .. => 4
    | .indexedApp .. => 5 | .indexedConst .. => 6
  match a, b with
  | .app i xs, .app j ys | .parameter i xs, .parameter j ys =>
    (compare i j).then (lexicographic termOrder xs ys)
  | .indexedApp i k xs, .indexedApp j l ys =>
    (compare i j).then ((codeOrder k l).then (lexicographic termOrder xs ys))
  | .code l v xs, .code m w ys =>
    (codeOrder l m).then ((codeOrder v w).then (lexicographic termOrder xs ys))
  | .constant i, .constant j => compare i j
  | .indexedConst i k, .indexedConst j l => (compare i j).then (codeOrder k l)
  | .var x, .var y => x.cmp y
  | a, b => compare (rank a) (rank b)

private def ordered (a b : TermView) : Bool := termOrder a b != .gt

private partial def insert (laws : Laws) (op : Nat) (a b : TermView) : DeriveM Nat := do
  let unit := if op == 1 then zero else one
  let ident := if op == 1 then `FOL.Q.add_zero else `FOL.PA.mul_one
  let leftIdent := if op == 1 then `FOL.PA.zero_add else `FOL.PA.one_mul
  let assoc := if op == 1 then `FOL.PA.add_assoc else `FOL.PA.mul_assoc
  let comm := if op == 1 then `FOL.PA.add_comm else `FOL.PA.mul_comm
  let node := fun a b => TermView.app op [a, b]
  if a == unit then return ← law laws leftIdent [b]
  if b == unit then return ← law laws ident [a]
  if let .app j [b₀, b₁] := b then
    if j == op then
      if ordered a b₀ then return ← eqRefl (node a b)
      let p ← eqSymm (← law laws assoc [a, b₀, b₁])
      let q ← eqCongr op [← law laws comm [a, b₀], ← eqRefl b₁]
      let r ← law laws assoc [b₀, a, b₁]
      let s ← eqCongr op [← eqRefl b₀, ← insert laws op a b₁]
      return ← eqTrans p (← eqTrans q (← eqTrans r s))
  if ordered a b then eqRefl (node a b) else law laws comm [a, b]

private partial def merge (laws : Laws) (op : Nat) (a b : TermView) : DeriveM Nat := do
  if let .app j [a₀, a₁] := a then
    if j == op then
      let assoc := if op == 1 then `FOL.PA.add_assoc else `FOL.PA.mul_assoc
      let p ← law laws assoc [a₀, a₁, b]
      let q ← merge laws op a₁ b
      let r ← eqCongr op [← eqRefl a₀, q]
      let s ← insert laws op a₀ (← rhs q)
      return ← eqTrans p (← eqTrans r s)
  insert laws op a b

private partial def product (laws : Laws) (a b : TermView) : DeriveM Nat := do
  if a == zero then return ← law laws `FOL.PA.zero_mul [b]
  if b == zero then return ← law laws `FOL.Q.mul_zero [a]
  if let .app 1 [a₀, a₁] := a then
    let p ← law laws `FOL.PA.right_distrib [a₀, a₁, b]
    let q ← product laws a₀ b
    let r ← product laws a₁ b
    return ← eqTrans p (← eqTrans (← eqCongr 1 [q, r])
      (← merge laws 1 (← rhs q) (← rhs r)))
  if let .app 1 [b₀, b₁] := b then
    let p ← law laws `FOL.PA.left_distrib [a, b₀, b₁]
    let q ← product laws a b₀
    let r ← product laws a b₁
    return ← eqTrans p (← eqTrans (← eqCongr 1 [q, r])
      (← merge laws 1 (← rhs q) (← rhs r)))
  merge laws 2 a b

private partial def normalize (laws : Laws) (t : TermView) : DeriveM Nat := do
  if t == one then return ← eqRefl t
  match t with
  | .app 0 [a] =>
    let p ← eqSymm (← law laws `FOL.PA.one_add [a])
    let q ← normalize laws a
    eqTrans p (← eqTrans (← eqCongr 1 [← eqRefl one, q])
      (← merge laws 1 one (← rhs q)))
  | .app 1 [a, b] =>
    let p ← normalize laws a
    let q ← normalize laws b
    eqTrans (← eqCongr 1 [p, q]) (← merge laws 1 (← rhs p) (← rhs q))
  | .app 2 [a, b] =>
    let p ← normalize laws a
    let q ← normalize laws b
    eqTrans (← eqCongr 2 [p, q]) (← product laws (← rhs p) (← rhs q))
  | _ => eqRefl t

syntax (name := pringTac) "pring" : praTactic

/-- Prove an arithmetic polynomial equality in `PA` by normalizing both sides. -/
@[pra_tactic pringTac]
def evalRing : Tactic := closedFirst fun _ => do
  let g ← currentGoal
  unless g.theory.name == `FOL.PA do throwError "pring requires PA"
  let .equal a b := g.formula | throwError "pring expects an equality"
  let names := [`FOL.Q.add_zero, `FOL.PA.zero_add, `FOL.PA.add_assoc, `FOL.PA.add_comm,
    `FOL.Q.mul_zero, `FOL.PA.zero_mul, `FOL.PA.mul_one, `FOL.PA.one_mul,
    `FOL.PA.mul_assoc, `FOL.PA.mul_comm,
    `FOL.PA.left_distrib, `FOL.PA.right_distrib, `FOL.PA.one_add]
  let laws ← names.mapM fun name => do
    let p ← rule g (← `(folRef| $(mkIdent (`_root_ ++ name)):ident))
    return (name, p)
  finish g do
    let laws ← laws.mapM fun (name, p) => return (name, ← p)
    let p ← normalize laws a
    let q ← normalize laws b
    unless (← rhs p) == (← rhs q) do throwError "polynomial normal forms differ"
    eqTrans p (← eqSymm q)

end LeanPRA.Library.FOL.ArithmeticTactic
