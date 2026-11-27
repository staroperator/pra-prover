module

public import PRAProver.Library.FOL.PRA.Numeral
public import PRAProver.Library.FOL.PRA.Derive.Congruence
public meta import PRAProver.Library.FOL.PRA.Derive.Substitution
meta import PRAProver.Library.FOL.DSL.Tactic

/-!
# Symbolic evaluation for the PRA deriver

- `FOL.PRA.Evaluation` supplies first-order proofs for equality, congruence, and constant
  programs.
- `proveTermEquality` uses program equations to prove equalities of quoted terms, including terms
  with free variables.
- `unfoldEquation` proves the first-order equation for a recorded source definition unfold.
- `sourceEdge` looks for a short first-order equality proof for a single step of source
  computation.
-/

@[expose] public section

pra

namespace FOL.PRA

namespace Evaluation

open FOL

theorem refl : ∀ a, (PRA ⊢ ${a} = a) := fun a => FOL.Provable.reflexivity language isAxiom a

theorem num_zero : (PRA ⊢ ${num 0} = zero) := by
  rw [_root_.FOL.PRA.num_zero]
  exact refl _

theorem num_succ : ∀ n, (PRA ⊢ ${num (S n)} = succ(${num n})) := by
  intro n
  rw [_root_.FOL.PRA.num_succ]
  exact refl _

theorem symm : ∀ a b, (PRA ⊢ ${a} = b) → (PRA ⊢ ${b} = a) := by
  intro a b h
  exact FOL.Provable.mp language isAxiom _ _ (FOL.Provable.symmetry language isAxiom a b) h

theorem trans : ∀ a b c,
    (PRA ⊢ ${a} = b) → (PRA ⊢ ${b} = c) → (PRA ⊢ ${a} = c) := by
  intro a b c h₁ h₂
  have p := FOL.Provable.transitivity language isAxiom a b c
  exact FOL.Provable.mp language isAxiom _ _ (FOL.Provable.mp language isAxiom _ _ p h₁) h₂

theorem congr_succ : ∀ x y, (PRA ⊢ ${x} = y) →
    (PRA ⊢ succ(${x}) = succ(${y})) := by
  intro x y h
  have p := FOL.Provable.functionCongruence language isAxiom 0 x y FOL.PRA.isFunction_succ
  rw [FOL.PRA.succ_arity, Formula.equalPremises_one] at p
  exact FOL.Provable.mp language isAxiom _ _ p h

theorem congr_pair : ∀ x y u v, (PRA ⊢ ${x} = u) → (PRA ⊢ ${y} = v) →
    (PRA ⊢ pair(${x}, ${y}) = pair(${u}, ${v})) := by
  intro x y u v h₁ h₂
  have p := FOL.Provable.functionCongruence language isAxiom 1 (pair x y) (pair u v)
    FOL.PRA.isFunction_pair
  rw [FOL.PRA.pair_arity, Formula.equalPremises_two] at p
  exact FOL.Provable.mp language isAxiom _ _ (FOL.Provable.mp language isAxiom _ _ p h₁) h₂

theorem congr_eval : ∀ e x y, (PRA ⊢ ${x} = y) →
    (PRA ⊢ eval[e](${x}) = eval[e](${y})) := by
  intro e x y h
  have p := FOL.Provable.functionCongruence language isAxiom
    (Language.functionFamilyMember language 0 e) x y (FOL.PRA.isFunction_eval e)
  rw [FOL.PRA.eval_arity, Formula.equalPremises_one] at p
  exact FOL.Provable.mp language isAxiom _ _ p h

theorem eval_comp_of_values (f g x y z : Nat) :
    (PRA ⊢ eval[g](${x}) = y) → (PRA ⊢ eval[f](${y}) = z) →
    (PRA ⊢ eval[Primrec.Code.comp f g](${x}) = z) := by
  intro inner outer
  exact trans _ _ _ (FOL.PRA.eval_comp' f g x)
    (trans _ _ _ (congr_eval f _ _ inner) outer)

theorem eval_pair_of_values (f g x y z : Nat) :
    (PRA ⊢ eval[f](${x}) = y) → (PRA ⊢ eval[g](${x}) = z) →
    (PRA ⊢ eval[Primrec.Code.pair f g](${x}) = pair(${y}, ${z})) := by
  intro left right
  exact trans _ _ _ (FOL.PRA.eval_pair' f g x) (congr_pair _ _ _ _ left right)

theorem constant_value_zero : ∀ x,
    (PRA ⊢ eval[Primrec.Code.const 0](${x}) = ${num 0}) := by
  intro x
  rw [_root_.FOL.PRA.num_zero]
  exact FOL.PRA.eval_zero' x

theorem constant_value_step : ∀ n x,
    (PRA ⊢ eval[Primrec.Code.const n](${x}) = ${num n}) →
      (PRA ⊢ eval[Primrec.Code.const (S n)](${x}) = ${num (S n)}) := by
  intro n x h
  have succValue : (PRA ⊢ eval[Primrec.Code.const (S n)](${x}) =
      succ(eval[Primrec.Code.const n](${x}))) :=
    trans _ _ _
      (FOL.PRA.eval_comp' Primrec.Code.succ (Primrec.Code.const n) x)
      (FOL.PRA.eval_succ' fol_term[PRA | eval[Primrec.Code.const n](${x})])
  rw [_root_.FOL.PRA.num_succ]
  exact trans _ fol_term[PRA | succ(eval[Primrec.Code.const n](${x}))] _
    succValue (congr_succ _ _ h)

extract_witness constant_value_zero constant_value_step

/-- Construct a proof that the constant program returns `num n` for its value `n`. -/
theorem constant_value : ∀ n x,
    (PRA ⊢ eval[Primrec.Code.const n](${x}) = ${num n}) := by
  intro n x
  let proof := fun i =>
    primrec (constant_value_zero.witness x) (fun k p => constant_value_step.witness k x p) i
  have checked : IsProofOf language isAxiom
      (Formula.equal language fol_term[PRA | eval[Primrec.Code.const n](${x})] (num n))
      (proof n) := by
    induction n with k ih
    · exact constant_value_zero.witness_correct x
    · exact constant_value_step.witness_correct k x (proof k) ih
  exists proof n
  exact checked

/-- Evaluate a program with its left input fixed to `num a`. -/
theorem eval_fixLeft (f a x : Nat) :
    (PRA ⊢ eval[Primrec.Code.fixLeft f a](${x}) = eval[f](pair(${num a}, ${x}))) := by
  let c := Primrec.Code.const a
  let i := Primrec.Code.id
  have args := FOL.PRA.eval_pair' c i x
  have id := Evaluation.trans _ _ _ (FOL.PRA.eval_pair' Primrec.Code.left Primrec.Code.right x)
    (FOL.PRA.pair_eval_left_right' x)
  have inputs := Evaluation.congr_pair _ _ _ _ (Evaluation.constant_value a x) id
  have computed := Evaluation.trans _ _ _ args inputs
  exact Evaluation.trans _ _ _ (FOL.PRA.eval_comp' f (Primrec.Code.pair c i) x)
    (Evaluation.congr_eval f _ _ computed)

end Evaluation

open FOL

/-! ## Pairing `num` terms -/

theorem pair_num_zero :
    (PRA ⊢ pair(${num 0}, ${num 0}) = ${num (pair 0 0)}) := by
  have h : pair 0 0 = 0 := rfl
  rw [h, num_zero]
  exact FOL.PRA.pair_zero_zero

theorem pair_num_zero_succ : ∀ a,
    (PRA ⊢ pair(${num a}, ${num 0}) = ${num (pair a 0)}) →
    (PRA ⊢ pair(${num 0}, ${num (S a)}) = ${num (pair 0 (S a))}) := by
  intro a h
  rw [num_zero] at h
  rw [num_zero, num_succ a, pair_zero_succ_eq, num_succ]
  exact Evaluation.trans _ fol_term[PRA | succ(pair(${num a}, zero))] _
    (FOL.PRA.pair_zero_succ' (num a)) (Evaluation.congr_succ _ _ h)

theorem pair_num_succ : ∀ a b,
    (PRA ⊢ pair(${num a}, ${num (S b)}) = ${num (pair a (S b))}) →
    (PRA ⊢ pair(${num (S a)}, ${num b}) = ${num (pair (S a) b)}) := by
  intro a b h
  rw [num_succ b] at h
  rw [num_succ a, pair_succ_eq, num_succ]
  exact Evaluation.trans _ fol_term[PRA | succ(pair(${num a}, succ(${num b})))] _
    (FOL.PRA.pair_succ' (num a) (num b)) (Evaluation.congr_succ _ _ h)

extract_witness pair_num_zero pair_num_zero_succ pair_num_succ

/-- The proof code `p` shows that pairing `num (unpairLeft i)` and `num (unpairRight i)` gives
`num i`. -/
def PairNumProofOf : Nat → Nat → QFProp := fun i p =>
  IsProofOf language isAxiom
    (Formula.equal language
      fol_term[PRA | pair(${num (unpairLeft i)}, ${num (unpairRight i)})] (num i)) p

/-- Extend the pairing proof at index `i` by advancing one step or starting the next diagonal. -/
def pairNumProofStep : Nat → Nat → Nat := fun i p =>
  ite (eqb (unpairRight i) 0) (pair_num_zero_succ.witness (unpairLeft i) p)
    (pair_num_succ.witness (unpairLeft i) (pred (unpairRight i)) p)

theorem pairNumProofStep_correct : ∀ i p,
    PairNumProofOf i p → PairNumProofOf (S i) (pairNumProofStep i p) := by
  intro i p h
  let a := unpairLeft i
  let b := unpairRight i
  have code : pair a b = i := pair_unpair i
  rw [PairNumProofOf] at h
  rcases zero_or_succ_pred b with hb | hb
  · rw [hb] at h
    rw [hb] at code
    have prev := eq_subst (fun n => IsProofOf language isAxiom
      (Formula.equal language fol_term[PRA | pair(${num a}, ${num 0})]
        (num n)) p) (eq_symm code) h
    have next : pair 0 (S a) = S i := by rw [pair_zero_succ_eq, code]
    rw [PairNumProofOf, ← next, unpairLeft_pair, unpairRight_pair, pairNumProofStep]
    rw [hb, eqb_self]
    exact pair_num_zero_succ.witness_correct a p prev
  · let c := pred b
    rw [hb] at h
    rw [hb] at code
    have prev := eq_subst (fun n => IsProofOf language isAxiom
      (Formula.equal language fol_term[PRA | pair(${num a}, ${num (S c)})]
        (num n)) p) (eq_symm code) h
    have next : pair (S a) c = S i := by rw [pair_succ_eq, code]
    rw [PairNumProofOf, ← next, unpairLeft_pair, unpairRight_pair, pairNumProofStep]
    rw [hb, and_right (eqb_eq_zero (S c) 0) (_root_.succ_ne_zero c)]
    rw [pred_succ]
    exact pair_num_succ.witness_correct a c p prev

/-- Pairing `num a` and `num b` gives `num (pair a b)`. -/
theorem pair_num : ∀ a b,
    (PRA ⊢ pair(${num a}, ${num b}) = ${num (pair a b)}) := by
  intro a b
  let proof := primrec pair_num_zero.witness pairNumProofStep
  have valid : ∀ i, PairNumProofOf i (proof i) := by
    intro i
    induction i with i ih
    · exact pair_num_zero.witness_correct
    · change PairNumProofOf (S i) (primrec pair_num_zero.witness pairNumProofStep (S i))
      rw [primrec_succ pairNumProofStep]
      exact pairNumProofStep_correct i (proof i) ih
  have h := valid (pair a b)
  rw [PairNumProofOf, unpairLeft_pair, unpairRight_pair] at h
  exists proof (pair a b)
  exact h

end FOL.PRA

end

end

public meta section

namespace PRAProver.Library.FOL.PRA.Derive.Evaluation

open Lean hiding Term
open Lean.Elab.Command PRAProver.Core PRAProver.Surface
open PRAProver.Library.Tactic.Construction
open PRAProver.Library.FOL.DSL (calculateClosedEquality provable)

private def language : Term := applyDefinition `FOL.PRA.language

private def appTerm (symbol args : Term) : Term :=
  applyDefinition `FOL.Term.app [language, symbol, args]

def zeroTerm : Term := applyDefinition `FOL.Term.const [language, numeral 0]

def succTerm (a : Term) : Term := appTerm (numeral 0) a

def mkPair (a b : Term) : Term := appTerm (numeral 1) (applyDefinition `pair [a, b])

/-- Build the expression for the quoted first-order term `eval[e](x)`. -/
def evalTerm (e x : Term) : Term :=
  appTerm (applyDefinition `FOL.Language.functionFamilyMember [language, numeral 0, e]) x

/-- An equality of quoted terms. When the endpoints are definitionally equal, the proof can
be supplied by reflexivity. -/
structure Equation where
  lhs : Term
  rhs : Term
  proof? : Option Proof := none
  deriving Inhabited

def unchanged (a : Term) : Equation := ⟨a, a, none⟩

def Equation.proof (e : Equation) : Proof :=
  e.proof?.getD (applyTheorem `FOL.PRA.Evaluation.refl [e.lhs])

def Equation.thenEq (a b : Equation) : Equation :=
  let proof := match a.proof?, b.proof? with
    | some p, some q =>
      some (applyTheorem `FOL.PRA.Evaluation.trans [a.lhs, a.rhs, b.rhs] [] [p, q])
    | p, none => p
    | none, q => q
  ⟨a.lhs, b.rhs, proof⟩

private def pairEq (a b : Equation) : Equation :=
  let lhs := mkPair a.lhs b.lhs
  let rhs := mkPair a.rhs b.rhs
  if a.proof?.isNone && b.proof?.isNone then ⟨lhs, rhs, none⟩ else
    ⟨lhs, rhs, some (applyTheorem `FOL.PRA.Evaluation.congr_pair
      [a.lhs, b.lhs, a.rhs, b.rhs] [] [a.proof, b.proof])⟩

private def programEq (e : Term) (a : Equation) : Equation :=
  ⟨evalTerm e a.lhs, evalTerm e a.rhs, a.proof?.map fun p =>
    applyTheorem `FOL.PRA.Evaluation.congr_eval [e, a.lhs, a.rhs] [] [p]⟩

private def succEq (a : Equation) : Equation :=
  ⟨succTerm a.lhs, succTerm a.rhs,
   a.proof?.map fun p => applyTheorem `FOL.PRA.Evaluation.congr_succ [a.lhs, a.rhs] [] [p]⟩

/-- The equation that the theorem `FOL.PRA.name'`, the instance of the quantified axiom `name`,
states at the codes `args`. -/
private def equation (name : Name) (args : List Term) (lhs rhs : Term) : Equation :=
  ⟨lhs, rhs, some (applyTheorem (`FOL.PRA ++ name.appendAfter "'") [] args)⟩

private def projectionAtZero (code : Term) (law : Name) : Equation :=
  let packed := mkPair zeroTerm zeroTerm
  let collapse := applyTheorem `FOL.PRA.pair_zero_zero
  let expand := applyTheorem `FOL.PRA.Evaluation.symm [packed, zeroTerm] [] [collapse]
  let h := programEq code ⟨zeroTerm, packed, some expand⟩
  h.thenEq (equation law [zeroTerm, zeroTerm] h.rhs zeroTerm)

private def ast (a : Term) : Name × List Term :=
  match getAppFnArgs a with
  | (.definition n [], args) => (n, args)
  | _ => (.anonymous, [])

-- Open code aliases such as the certificates produced by derive_primrec. Stop at constructors
-- so even large program indices remain symbolic throughout the proof.
private def codeView (env : Core.Environment) (a : Term) : Name × List Term := Id.run do
  let mut t := a
  repeat
    let (.definition n parameters, args) := getAppFnArgs t | return (.anonymous, [])
    if n.getPrefix == `Primrec.Code then
      match n with
      | `Primrec.Code.zero | `Primrec.Code.succ | `Primrec.Code.left | `Primrec.Code.right
      | `Primrec.Code.pair | `Primrec.Code.comp | `Primrec.Code.rec | `Primrec.Code.const
      | `Primrec.Code.id => return (n, args)
      | _ => pure ()
    let some (.function d) := env.lookup n | return (.anonymous, [])
    unless d.arity == args.length do return (.anonymous, [])
    let body := args.foldl .app (d.body.instantiate parameters)
    t := ((exposeTerm 192 false body).toOption.join).getD body
  return (.anonymous, [])

private partial def sameCode (env : Core.Environment) (a b : Term) : Bool :=
  if a == b then true else
    let (f, xs) := codeView env a
    let (g, ys) := codeView env b
    if f.isAnonymous || f != g then false
    else if f == `Primrec.Code.comp || f == `Primrec.Code.pair || f == `Primrec.Code.rec then
      xs.length == ys.length && (xs.zip ys).all (fun (p, q) => sameCode env p q)
    else xs == ys

private def pairArgs (t : Term) : Option (Term × Term) := do
  let (`FOL.Term.app, [L, symbol, args]) := ast t | none
  unless L == language && symbol == numeral 1 do none
  let (`pair, [a, b]) := ast args | none
  some (a, b)

private def programArgs (t : Term) : Option (Term × Term) := do
  let (`FOL.Term.app, [L, symbol, x]) := ast t | none
  let (`FOL.Language.functionFamilyMember, [l, family, e]) := ast symbol | none
  guard (L == language && l == L && family == numeral 0)
  return (e, x)

private def numTerm (n : Term) : Term := applyDefinition `FOL.PRA.num [n]

private def numEquation (name : Name) (args : List Term) (lhs rhs : Term) : Equation :=
  ⟨lhs, rhs, some (applyTheorem name args)⟩

-- Recover a fixed value together with the proof of its `num` term.
private partial def fixedNum (t : Term) :
    Option (Term × Equation) := do
  if t == zeroTerm then
    let h := numEquation `FOL.PRA.Evaluation.num_zero [] (numTerm .zero) t
    return (.zero, ⟨t, h.lhs,
      some (applyTheorem `FOL.PRA.Evaluation.symm [h.lhs, t] [] [h.proof])⟩)
  if let (`FOL.Term.app, [L, .zero, x]) := ast t then
    guard (L == language)
    let (value, inner) ← fixedNum x
    let h := succEq inner
    let result := Term.app .succ value
    let rhs := numTerm result
    let expand := applyTheorem `FOL.PRA.Evaluation.num_succ [value]
    let fold := applyTheorem `FOL.PRA.Evaluation.symm [rhs, h.rhs] [] [expand]
    return (result, h.thenEq ⟨h.rhs, rhs, some fold⟩)
  if let some (x, y) := pairArgs t then
    let (a, hx) ← fixedNum x
    let (b, hy) ← fixedNum y
    let value := applyDefinition `pair [a, b]
    let h := pairEq hx hy
    return (value, h.thenEq (numEquation `FOL.PRA.pair_num [a, b]
      h.rhs (numTerm value)))
  let (code, arg) ← programArgs t
  let (`Primrec.Code.const, [value]) := ast code | none
  return (value, numEquation `FOL.PRA.Evaluation.constant_value [value, arg]
    t (numTerm value))

private def unpackEnvironment (n : Nat) (t : Term) : Option (List Term) :=
  match n with
  | 0 => none
  | 1 => some [t]
  | n + 2 => do
    let (x, y) ← pairArgs t
    return x :: (← unpackEnvironment (n + 1) y)

private def publicCallback (code : Term) : Option Term :=
  match ast code with
  | (`Primrec.Code.onRight, [f]) => some f
  | (`Primrec.Code.comp, [f, .definition `Primrec.Code.right []]) => some f
  | _ => none

private def specializeCall (env : Core.Environment) (code arg : Term) : Option Equation := do
  let .definition packed callbacks := code | none
  let .str (.str name "internal") "code" := packed | none
  let some (.function source) := env.lookup name | none
  let some (.function _) := env.lookup (name ++ `code) | none
  let (fixed, input) ← pairArgs arg
  let fields ← unpackEnvironment source.functions.length fixed
  let count := source.functions.countP (· == 0)
  let zeros := fields.drop count
  guard (zeros.all (fun t => t == zeroTerm))
  let numeric ← (fields.take count).mapM (fun t => (fixedNum t).map Prod.fst)
  let programs ← callbacks.mapM publicCallback
  let mut numbers := numeric
  let mut codes := programs
  let mut actuals := #[]
  for arity in source.functions do
    if arity == 0 then
      let value :: rest := numbers | none
      numbers := rest
      actuals := actuals.push value
    else
      let value :: rest := codes | none
      codes := rest
      actuals := actuals.push value
  let (value, h) ← fixedNum fixed
  let rhs := evalTerm (.definition (name ++ `code) actuals.toList) input
  let align := programEq code (pairEq h (unchanged input))
  let unpack := applyTheorem `FOL.PRA.Evaluation.eval_fixLeft [] [code, value, input]
  let reverse := applyTheorem `FOL.PRA.Evaluation.symm [rhs, align.rhs] [] [unpack]
  return align.thenEq ⟨align.rhs, rhs, some reverse⟩

/-- Rewrite the fixed calls in a quoted term to their public program codes. -/
partial def specializeTerm (env : Core.Environment) (t : Term) : Equation :=
  if let some (code, x) := programArgs t then
    let input := specializeTerm env x
    let h := programEq code input
    h.thenEq ((specializeCall env code input.rhs).getD (unchanged h.rhs))
  else if let some (a, b) := pairArgs t then
    pairEq (specializeTerm env a) (specializeTerm env b)
  else if let (`FOL.Term.app, [L, .zero, a]) := ast t then
    if L == language then succEq (specializeTerm env a) else unchanged t
  else unchanged t

-- The two inverse projections reconstruct a tuple. A pair of zeros is also a
-- representation of the empty environment, by the first-order pairing axiom.
private def tupleEquation (env : Core.Environment) (t : Term) : Option Equation := do
  let (a, b) ← pairArgs t
  if a == zeroTerm && b == zeroTerm then
    return equation `pair_zero_zero [] t zeroTerm
  let (l, x) ← programArgs a
  let (r, y) ← programArgs b
  guard (x == y && (codeView env l).1 == `Primrec.Code.left &&
    (codeView env r).1 == `Primrec.Code.right)
  return equation `pair_eval_left_right [x] t x

-- A closed tuple of `zero`, `succ`, and `pair` can decide a guard, such as the rule tag at an MP
-- node.
private partial def closedTuple (t : Term) : Bool := Id.run do
  if t == zeroTerm then return true
  if let some (a, b) := pairArgs t then return closedTuple a && closedTuple b
  if let (`FOL.Term.app, [_, symbol, x]) := ast t then
    return symbol == numeral 0 && closedTuple x
  return false

-- A step receives the fixed input on the left, and the index and preceding
-- value on the right. These cases select an input that omits the preceding value.
private partial def usesAccumulator (env : Core.Environment) (code : Term) : Bool :=
  match codeView env code with
  | (`Primrec.Code.zero, _) | (`Primrec.Code.const, _) | (`Primrec.Code.left, _) => false
  | (`Primrec.Code.comp, [f, g]) =>
    let outer := (codeView env f).1
    if outer == `Primrec.Code.zero || outer == `Primrec.Code.const then false
    else if outer == `Primrec.Code.left && (codeView env g).1 == `Primrec.Code.right then false
    else usesAccumulator env g
  | _ => true

private partial def compute (env : Core.Environment) (keep : Term → Term → Bool)
    (code x : Term) : CommandElabM Equation := do
  let lhs := evalTerm code x
  let (head, args) := codeView env code
  let compound := [`Primrec.Code.comp, `Primrec.Code.pair, `Primrec.Code.rec].contains head
  if compound && keep code x then return unchanged lhs
  match (head, args) with
  | (`Primrec.Code.zero, []) => return equation `eval_zero [x] lhs zeroTerm
  | (`Primrec.Code.succ, []) => return equation `eval_succ [x] lhs (succTerm x)
  | (`Primrec.Code.left, []) =>
    if let some (a, b) := pairArgs x then return equation `eval_left [a, b] lhs a
    if x == zeroTerm then return projectionAtZero code `eval_left
    return unchanged lhs
  | (`Primrec.Code.right, []) =>
    if let some (a, b) := pairArgs x then return equation `eval_right [a, b] lhs b
    if x == zeroTerm then return projectionAtZero code `eval_right
    return unchanged lhs
  | (`Primrec.Code.id, []) =>
    let a := applyDefinition `Primrec.Code.left []
    let b := applyDefinition `Primrec.Code.right []
    let p := equation `eval_pair [a, b, x] lhs (mkPair (evalTerm a x) (evalTerm b x))
    if let some _ := pairArgs x then
      return p.thenEq (pairEq (← compute env keep a x) (← compute env keep b x))
    return p.thenEq (equation `pair_eval_left_right [x] p.rhs x)
  | (`Primrec.Code.comp, [f, g]) =>
    let p := equation `eval_comp [f, g, x] lhs (evalTerm f (evalTerm g x))
    let outer := (codeView env f).1
    if outer == `Primrec.Code.zero || outer == `Primrec.Code.const then
      return p.thenEq (← compute env keep f (evalTerm g x))
    if outer == `Primrec.Code.left || outer == `Primrec.Code.right then
      if let (`Primrec.Code.pair, [a, b]) := codeView env g then
        let pair := equation `eval_pair [a, b, x] (evalTerm g x)
          (mkPair (evalTerm a x) (evalTerm b x))
        let project ← compute env keep f pair.rhs
        let chosen := if outer == `Primrec.Code.left then a else b
        return ((p.thenEq (programEq f pair)).thenEq project).thenEq (← compute env keep chosen x)
    let inner ← compute env keep g x
    let h := programEq f inner
    return (p.thenEq h).thenEq (← compute env keep f inner.rhs)
  | (`Primrec.Code.pair, [f, g]) =>
    let p := equation `eval_pair [f, g, x] lhs (mkPair (evalTerm f x) (evalTerm g x))
    return p.thenEq (pairEq (← compute env keep f x) (← compute env keep g x))
  | (`Primrec.Code.rec, [f, g]) =>
    let some (a, n) := pairArgs x | return unchanged lhs
    if n == zeroTerm then
      let h := equation `eval_rec_zero [f, g, a] lhs (evalTerm f a)
      return h.thenEq (← compute env keep f a)
    let (`FOL.Term.app, [L, symbol, i]) := ast n | return unchanged lhs
    unless L == language && symbol == numeral 0 do return unchanged lhs
    let previous ← if usesAccumulator env g then compute env keep code (mkPair a i)
      else pure (unchanged (evalTerm code (mkPair a i)))
    let stepArg := pairEq (unchanged a) (pairEq (unchanged i) previous)
    let h := equation `eval_rec_succ [f, g, a, i] lhs (evalTerm g stepArg.lhs)
    let step := programEq g stepArg
    return (h.thenEq step).thenEq (← compute env keep g stepArg.rhs)
  | (`Primrec.Code.const, [value]) =>
    let original := value
    let (head, _) := ast value
    let value := if let some (.function d) := env.lookup head then
        if d.arity == 0 then d.body else value
      else value
    match numeralValue? value with
    | some 0 => return equation `eval_zero [x] lhs zeroTerm
    | some (n+1) =>
      let c := applyDefinition `Primrec.Code.const [numeral n]
      let expanded := applyDefinition `Primrec.Code.comp [applyDefinition `Primrec.Code.succ [], c]
      let h ← compute env keep expanded x
      return { h with lhs }
    | none =>
      let rhs := applyDefinition `FOL.PRA.num [value]
      return ⟨lhs, rhs, some (applyTheorem `FOL.PRA.Evaluation.constant_value [original, x])⟩
  | _ => return unchanged lhs

private partial def normalize (env : Core.Environment) (keep : Term → Term → Bool)
    (t : Term) : CommandElabM Equation := do
  match ast t with
  | (`FOL.Term.app, [L, symbol, x]) =>
    unless L == language do return unchanged t
    if symbol == numeral 0 then return succEq (← normalize env keep x)
    if let some (a, b) := pairArgs t then
      return pairEq (← normalize env keep a) (← normalize env keep b)
    let (`FOL.Language.functionFamilyMember, [l, family, e]) := ast symbol | return unchanged t
    unless l == L && family == numeral 0 do return unchanged t
    let head := (codeView env e).1
    if head == `Primrec.Code.zero || head == `Primrec.Code.const ||
        ((head == `Primrec.Code.left || head == `Primrec.Code.right) && (pairArgs x).isSome) then
      let h ← compute env keep e x
      return h.thenEq (← normalize env keep h.rhs)
    let arg ← normalize env keep x
    let h := programEq e arg
    return h.thenEq (← compute env keep e arg.rhs)
  | _ => return unchanged t

-- The equations for a conditional only need its test and the selected branch.
-- Checking the test first keeps the unselected proof-checking expressions out of the derivation.
private partial def groundTerm (t : Term) : Bool := Id.run do
  if t == zeroTerm then return true
  if let some (a, b) := pairArgs t then return groundTerm a && groundTerm b
  if let some (_, a) := programArgs t then return groundTerm a
  if let (`FOL.Term.app, [_, symbol, a]) := ast t then return symbol == numeral 0 && groundTerm a
  return false

private partial def selectBranch (env : Core.Environment) (t : Term) : CommandElabM Equation := do
  let some (e, x) := programArgs t | return unchanged t
  unless (ast e).1 == `ite.code do return unchanged t
  let some (condition, branches) := pairArgs x | return unchanged t
  let some (yes, no) := pairArgs branches | return unchanged t
  unless groundTerm condition do return unchanged t
  let h ← normalize env (fun _ _ => false) condition
  unless h.rhs == zeroTerm || h.rhs == succTerm zeroTerm do return unchanged t
  let arg := pairEq h (unchanged branches)
  let branch ← compute env (fun _ _ => false) e arg.rhs
  unless branch.rhs == yes || branch.rhs == no do return unchanged t
  return ((programEq e arg).thenEq branch).thenEq (← selectBranch env branch.rhs)

-- The compiler represents a call that forwards its argument as composition with the identity.
-- Remove those compositions before expanding a shared program such as the proof checker.
private partial def forwardArgument (env : Core.Environment) (e x : Term) :
    CommandElabM Equation := do
  let lhs := evalTerm e x
  let (`Primrec.Code.comp, [f, g]) := codeView env e | return unchanged lhs
  unless (codeView env g).1 == `Primrec.Code.id do return unchanged lhs
  let h := equation `eval_comp [f, g, x] lhs (evalTerm f (evalTerm g x))
  let inner ← compute env (fun _ _ => false) g x
  return (h.thenEq (programEq f inner)).thenEq (← forwardArgument env f x)

private def join (a b : Equation) : Proof :=
  let reverse := b.proof?.map fun p =>
    applyTheorem `FOL.PRA.Evaluation.symm [b.lhs, b.rhs] [] [p]
  (a.thenEq ⟨b.rhs, b.lhs, reverse⟩).proof

-- In this signature a variable, zero and a function application have distinct syntax codes.
-- Looking under a common function symbol can reveal this difference without evaluating its code.
private partial def differentSyntax (a b : Term) : Bool := Id.run do
  if a == b then return false
  if let some (x, y) := pairArgs a then
    if let some (u, v) := pairArgs b then return differentSyntax x u || differentSyntax y v
  let (f, xs) := ast a
  let (g, ys) := ast b
  let known := fun t n => t == zeroTerm || n == `FOL.Term.var || n == `FOL.Term.app
  unless known a f && known b g && xs.head? == some language && ys.head? == some language do
    return false
  if f != g then return true
  match xs, ys with
  | [_, j, x], [_, k, y] => return j == k && differentSyntax x y
  | _, _ => return false

-- The arguments of a defining equation often contain calls to much larger programs.
-- Keep those calls as written on the first pass and use congruence on their arguments.
private partial def collectPrograms (t : Term) (codes : List Term) : List Term := Id.run do
  if let some (e, x) := programArgs t then
    return collectPrograms x (if codes.contains e then codes else e :: codes)
  if let some (x, y) := pairArgs t then return collectPrograms y (collectPrograms x codes)
  if let (`FOL.Term.app, [_, _, x]) := ast t then return collectPrograms x codes
  return codes

-- Composition with an input transformation leaves the outer operation visible.
private partial def wrapsProgram (env : Core.Environment) (source target : Term) : Bool :=
  match codeView env source with
  | (`Primrec.Code.comp, [f, _]) => sameCode env f target || wrapsProgram env f target
  | _ => false

-- Compositions can change how an input reaches a recursion. Open the wrappers
-- while leaving the recursion itself available for comparison.
private partial def headRecursion? (env : Core.Environment) (code : Term) : Option Term :=
  match codeView env code with
  | (`Primrec.Code.comp, [f, _]) => headRecursion? env f
  | (`Primrec.Code.rec, [_, _]) => some code
  | _ => none

private def varTerm (i : Nat) : Term :=
  applyDefinition `FOL.Term.var [language, numeral i]

private partial def shiftTerm (amount : Nat) (term : Term) : Option Term := do
  if term == zeroTerm then return term
  if let some (code, arg) := programArgs term then
    return evalTerm code (← shiftTerm amount arg)
  if let some (a, b) := pairArgs term then
    return mkPair (← shiftTerm amount a) (← shiftTerm amount b)
  match ast term with
  | (`FOL.Term.app, [L, symbol, arg]) =>
    guard (L == language && symbol == numeral 0)
    return succTerm (← shiftTerm amount arg)
  | (`FOL.Term.var, [L, index]) =>
    guard (L == language)
    return varTerm ((← numeralValue? index) + amount)
  | (`FOL.PRA.num, [_]) => return term
  | _ => none

private def formulaEqual (a b : Term) : Term :=
  applyDefinition `FOL.Formula.equal [language, a, b]

private def formulaImp (a b : Term) : Term :=
  applyDefinition `FOL.Formula.imp [a, b]

private def formulaAll (a : Term) : Term :=
  applyDefinition `FOL.Formula.all [a]

private def innerRule (name : Name) (args : List Term) (premises : List Proof := []) : Proof :=
  applyTheorem name args [language, applyDefinition `FOL.PRA.isAxiom] premises

def instanceEquality (body argument target : Term) : CommandElabM Proof := do
  let source := applyDefinition `FOL.Formula.instantiate [language, body, argument]
  let (result, h) ← PRAProver.Library.FOL.PRA.QuotedSubstitution.instantiate body argument
  if result == target then return h
  return mkEqTrans source result target h (← calculateClosedEquality result target)

private def specializeInner (body argument target : Term) (proof : Proof) : CommandElabM Proof := do
  let source := applyDefinition `FOL.Formula.instantiate [language, body, argument]
  let theory := applyDefinition `FOL.PRA.isAxiom
  let step := applyTheorem `FOL.Provable.instantiate [] [language, theory, body, argument]
  let specialized := innerRule `FOL.Provable.mp [formulaAll body, source] [step, proof]
  let motive := Predicate.lam `A (provable language theory (.bvar 0))
  let h ← instanceEquality body argument target
  let eq : Proof := .forallElim (.forallElim (.eqSubst motive) source) target
  return .impElim (.impElim eq h) specialized

-- Compare recursors with different environments at the same numerical counter.
-- The induction theorem needs the base equation and the step equation at arbitrary inputs.
private def recursionAtFrames (env : Core.Environment) (r s u v : Term)
    (compare : Nat → Term → Term → CommandElabM (Option Equation)) :
    CommandElabM (Option Equation) := do
  let (some (x, n), some (y, m)) := (pairArgs u, pairArgs v) | return none
  unless n == m do return none
  let (`Primrec.Code.rec, [base, step]) := codeView env r | return none
  let (`Primrec.Code.rec, [base', step']) := codeView env s | return none
  let some hx ← compare 0 (evalTerm base x) (evalTerm base' y) | return none
  let indices := mkPair (varTerm 1) (varTerm 0)
  let some x₂ := shiftTerm 2 x | return none
  let some y₂ := shiftTerm 2 y | return none
  let stepInput := fun t => mkPair t indices
  let some hs ← compare 2 (evalTerm step (stepInput x₂)) (evalTerm step' (stepInput y₂))
    | return none
  let some x₁ := shiftTerm 1 x | return none
  let some x₃ := shiftTerm 3 x | return none
  let some x₄ := shiftTerm 4 x | return none
  let some y₁ := shiftTerm 1 y | return none
  let some y₃ := shiftTerm 3 y | return none
  let stepFormula := fun x y =>
    formulaEqual (evalTerm step (mkPair x indices)) (evalTerm step' (mkPair y indices))
  let body := fun x y xShifted yShifted n =>
    formulaImp (formulaEqual (evalTerm base x) (evalTerm base' y))
      (formulaImp (formulaAll (formulaAll (stepFormula xShifted yShifted)))
        (formulaEqual (evalTerm r (mkPair x n)) (evalTerm s (mkPair y n))))
  let openX := formulaAll (formulaAll (body (varTerm 2) (varTerm 1)
    (varTerm 4) (varTerm 3) (varTerm 0)))
  let openY := formulaAll (body x₂ (varTerm 1) x₄ (varTerm 3) (varTerm 0))
  let openN := body x₁ y₁ x₃ y₃ (varTerm 0)
  let h := applyTheorem `FOL.PRA.Evaluation.rec_congr [] [base, step, base', step']
  let h ← specializeInner openX x (formulaAll openY) h
  let h ← specializeInner openY y (formulaAll openN) h
  let h ← specializeInner openN n (body x y x₂ y₂ n) h
  let A := formulaEqual hx.lhs hx.rhs
  let B := formulaAll (formulaAll (stepFormula x₂ y₂))
  let C := formulaEqual (evalTerm r u) (evalTerm s v)
  let h := innerRule `FOL.Provable.mp [A, formulaImp B C] [h, hx.proof]
  let steps := innerRule `FOL.Provable.gen [stepFormula x₂ y₂] [hs.proof]
  let steps := innerRule `FOL.Provable.gen [formulaAll (stepFormula x₂ y₂)] [steps]
  let h := innerRule `FOL.Provable.mp [B, C] [h, steps]
  return some ⟨evalTerm r u, evalTerm s v, h⟩

private def compareRecursions (env : Core.Environment) (a b : Term)
    (compare : Term → Term → CommandElabM (Option Equation)) :
    CommandElabM (Option Equation) := do
  let (some (f, x), some (g, y)) := (programArgs a, programArgs b) | return none
  let (some r, some s) := (headRecursion? env f, headRecursion? env g) | return none
  let codes := collectPrograms x (collectPrograms y [])
  let keep := fun e _ => e == r || e == s || codes.contains e
  let lhs ← normalize env keep a
  let rhs ← normalize env keep b
  let (some (p, u), some (q, v)) := (programArgs lhs.rhs, programArgs rhs.rhs) | return none
  unless p == r && q == s do return none
  if u == v && sameCode env r s then
    return some ⟨a, b, join lhs rhs⟩
  let some mid ← recursionAtFrames env r s u v (fun _ => compare) | return none
  return some ⟨a, b, join (lhs.thenEq mid) rhs⟩

-- Take one defining equation at the head. A projection demands an input pair, and a
-- recursion demands a pair and the head of its counter. Other arguments stay as written.
private partial def headEquation (env : Core.Environment) (t : Term) : Option Equation := do
  if let some h := tupleEquation env t then return h
  if let (`FOL.PRA.num, [n]) := ast t then
    match n with
    | .zero => return ⟨t, zeroTerm, applyTheorem `FOL.PRA.Evaluation.num_zero⟩
    | .app .succ k =>
      return ⟨t, succTerm (applyDefinition `FOL.PRA.num [k]),
        applyTheorem `FOL.PRA.Evaluation.num_succ [k]⟩
    | _ => none
  let (e, x) ← programArgs t
  let stepInput := fun h => programEq e h
  match codeView env e with
  | (`Primrec.Code.comp, [f, g]) =>
    return equation `eval_comp [f, g, x] t (evalTerm f (evalTerm g x))
  | (`Primrec.Code.pair, [f, g]) =>
    return equation `eval_pair [f, g, x] t (mkPair (evalTerm f x) (evalTerm g x))
  | (`Primrec.Code.id, []) =>
    let l := applyDefinition `Primrec.Code.left
    let r := applyDefinition `Primrec.Code.right
    let p := equation `eval_pair [l, r, x] t (mkPair (evalTerm l x) (evalTerm r x))
    return p.thenEq (equation `pair_eval_left_right [x] p.rhs x)
  | (`Primrec.Code.zero, []) => return equation `eval_zero [x] t zeroTerm
  | (`Primrec.Code.succ, []) => return equation `eval_succ [x] t (succTerm x)
  | (`Primrec.Code.const, [n]) =>
    return ⟨t, applyDefinition `FOL.PRA.num [n],
      applyTheorem `FOL.PRA.Evaluation.constant_value [n, x]⟩
  | (k, []) =>
    guard (k == `Primrec.Code.left || k == `Primrec.Code.right)
    let takeLeft := k == `Primrec.Code.left
    let law := if takeLeft then `eval_left else `eval_right
    if let some (a, b) := pairArgs x then return equation law [a, b] t (if takeLeft then a else b)
    if x == zeroTerm then return projectionAtZero e law
    return stepInput (← headEquation env x)
  | (`Primrec.Code.rec, [f, g]) =>
    let some (a, n) := pairArgs x | return stepInput (← headEquation env x)
    if n == zeroTerm then return equation `eval_rec_zero [f, g, a] t (evalTerm f a)
    if let (`FOL.Term.app, [_, .zero, i]) := ast n then
      let previous := evalTerm e (mkPair a i)
      return equation `eval_rec_succ [f, g, a, i] t (evalTerm g (mkPair a (mkPair i previous)))
    return stepInput (pairEq (unchanged a) (← headEquation env n))
  | _ => none

-- Look for a short reduction of one endpoint to the other. A common symbol only requires
-- congruence on its arguments. The budget limits this first attempt before general comparison.
private partial def reduceTo (env : Core.Environment) (a b : Term) :
    StateM Nat (Option Equation) := do
  if a == b then return some (unchanged a)
  let budget ← get
  if budget == 0 then return none
  set (budget - 1)
  let child (x y : Term) : StateM Nat (Option Equation) := do
    if let some step ← reduceTo env x y then return some step
    if let some step ← reduceTo env y x then
      return some ⟨x, y, join (unchanged x) step⟩
    return none
  if let some (x, y) := pairArgs a then
    if let some (u, v) := pairArgs b then
      let some hx ← child x u | return none
      let some hy ← child y v | return none
      return some (pairEq hx hy)
  if let (`FOL.Term.app, [_, .zero, x]) := ast a then
    if let (`FOL.Term.app, [_, .zero, y]) := ast b then
      return (← child x y).map succEq
  if let some (e, x) := programArgs a then
    if let some (f, y) := programArgs b then
      if sameCode env e f then
        if let some h ← child x y then return some { programEq e h with rhs := b }
  let some step := headEquation env a | return none
  return (← reduceTo env step.rhs b).map (step.thenEq ·)

-- Projection and constant equations select their result before any operand is evaluated.
private def projectOrConst (env : Core.Environment) (t : Term) : Equation := Id.run do
  let some (code, input) := programArgs t | return unchanged t
  let (op, _) := codeView env code
  if op == `Primrec.Code.zero || op == `Primrec.Code.const ||
      ((op == `Primrec.Code.left || op == `Primrec.Code.right) && (pairArgs input).isSome) then
    return (headEquation env t).getD (unchanged t)
  return unchanged t

-- Follow only the outer composition of a call. Each step preserves its inner argument
-- as a single term. Two calls can meet at a common operation before either argument runs.
private def compositionHeads (env : Core.Environment) (t : Term) : List Equation := Id.run do
  let mut current := unchanged t
  let mut steps := [current]
  for _ in [:12] do
    let some (e, x) := programArgs current.rhs | break
    let (`Primrec.Code.comp, [f, g]) := codeView env e | break
    current := current.thenEq
      (equation `eval_comp [f, g, x] current.rhs (evalTerm f (evalTerm g x)))
    steps := current :: steps
  return steps.reverse

private partial def meetHeads (env : Core.Environment) (a b : Term) :
    StateM Nat (Option Equation) := do
  if a == b then return some (unchanged a)
  let budget ← get
  if budget == 0 then return none
  set (budget - 1)
  let l := projectOrConst env a
  let r := projectOrConst env b
  if l.proof?.isSome || r.proof?.isSome then
    let some middle ← meetHeads env l.rhs r.rhs | return none
    return some ⟨a, b, join (l.thenEq middle) r⟩
  if let some (x, y) := pairArgs a then
    if let some (u, v) := pairArgs b then
      let some hx ← meetHeads env x u | return none
      let some hy ← meetHeads env y v | return none
      return some (pairEq hx hy)
  if let (`FOL.Term.app, [_, .zero, x]) := ast a then
    if let (`FOL.Term.app, [_, .zero, y]) := ast b then
      return (← meetHeads env x y).map succEq
  if (programArgs a).isSome && (programArgs b).isSome then
    let lhsSteps := compositionHeads env a
    let rhsSteps := compositionHeads env b
    for l in lhsSteps do
      let some (e, x) := programArgs l.rhs | continue
      for r in rhsSteps do
        let some (f, y) := programArgs r.rhs | continue
        if e == f then
          if let some h ← meetHeads env x y then
            return some ⟨a, b, join (l.thenEq (programEq e h)) r⟩
          break
    return none
  -- Pairing, projections, and recursion can expose a common head on either side.
  let l := (headEquation env a).getD (unchanged a)
  let r := (headEquation env b).getD (unchanged b)
  if l.proof?.isNone && r.proof?.isNone then return none
  let some middle ← meetHeads env l.rhs r.rhs | return none
  return some ⟨a, b, join (l.thenEq middle) r⟩

private def equivalenceBody (f g : Term) : Term :=
  formulaEqual (evalTerm f (varTerm 0)) (evalTerm g (varTerm 0))

-- Evaluate the wiring between named operations, leaving their numerical programs opaque.
-- If one operation is a wrapper around the other, open just that wrapper.
private def routedEquality (env : Core.Environment) (a b x : Term) :
    CommandElabM (Option Equation) := do
  let stop (opened : Option Term) (e : Term) (_ : Term) :=
    if opened == some e then false else
      match getAppFnArgs e with
      | (.definition n _, _) =>
        n == n.getPrefix ++ `code || n == `Primrec.Code.rec
      | _ => false
  let l ← compute env (stop none) a x
  let r ← compute env (stop none) b x
  let close (l r : Equation) : Option Equation := do
    let middle ← (meetHeads env l.rhs r.rhs).run' 128
    return ⟨l.lhs, r.lhs, join (l.thenEq middle) r⟩
  if let some h := close l r then return some h
  let (some (f, u), some (g, v)) := (programArgs l.rhs, programArgs r.rhs) | return none
  if wrapsProgram env g f then
    let h ← compute env (stop (some g)) g v
    return close l (r.thenEq h)
  if wrapsProgram env f g then
    let h ← compute env (stop (some f)) f u
    return close (l.thenEq h) r
  return none

-- Two instances of a named family can use pointwise equal callbacks with different
-- indices. Follow matching program constructors and prove the equalities at the leaves.
private partial def pointwise (env : Core.Environment) (fuel : Nat) (a b : Term) :
    StateT (Std.HashMap (Term × Term) Proof) CommandElabM (Option Proof) := do
  if let some h := (← get)[(a, b)]? then return some h
  let x := varTerm 0
  let lhs := evalTerm a x
  let rhs := evalTerm b x
  let generalize := fun p => innerRule `FOL.Provable.gen [equivalenceBody a b] [p]
  if a == b then return some (generalize (unchanged lhs).proof)
  if fuel == 0 then return none
  let short := ((reduceTo env lhs rhs).run' 32).orElse fun _ =>
    (meetHeads env lhs rhs).run' 48
  let short ← if short.isSome then pure short else routedEquality env a b x
  let proof ← if let some h := short then pure (generalize h.proof) else do
    let (k, [f, g]) := codeView env a | return none
    let (k', [u, v]) := codeView env b | return none
    unless k == k' do return none
    let law := match k with
      | `Primrec.Code.comp => `FOL.PRA.Evaluation.comp_congr
      | `Primrec.Code.pair => `FOL.PRA.Evaluation.pair_congr
      | `Primrec.Code.rec => `FOL.PRA.Evaluation.rec_congr_programs
      | _ => Name.anonymous
    if law.isAnonymous then return none
    let some hf ← pointwise env (fuel - 1) f u | return none
    let some hg ← pointwise env (fuel - 1) g v | return none
    let A := formulaAll (equivalenceBody f u)
    let B := formulaAll (equivalenceBody g v)
    let C := formulaAll (equivalenceBody a b)
    let h := applyTheorem law [] [f, g, u, v]
    let h := innerRule `FOL.Provable.mp [A, formulaImp B C] [h, hf]
    pure (innerRule `FOL.Provable.mp [B, C] [h, hg])
  modify (·.insert (a, b) proof)
  return some proof

private def compareFamilies (env : Core.Environment) (a b : Term) :
    CommandElabM (Option Equation) := do
  let lhs := compositionHeads env a
  let rhs := compositionHeads env b
  for l in lhs do
    let some (f, x) := programArgs l.rhs | continue
    let .definition name (_ :: _) := f | continue
    for r in rhs do
      let some (g, y) := programArgs r.rhs | continue
      let .definition other (_ :: _) := g | continue
      unless name == other && f != g do continue
      let hx := ((reduceTo env x y).run' 96).orElse fun _ => (meetHeads env x y).run' 96
      let some hx := hx | continue
      let some equivalent ← (pointwise env 64 f g).run' {} | continue
      let h ← specializeInner (equivalenceBody f g) y
        (formulaEqual (evalTerm f y) (evalTerm g y)) equivalent
      let middle := (programEq f hx).thenEq ⟨evalTerm f y, r.rhs, some h⟩
      return some ⟨a, b, join (l.thenEq middle) r⟩
  return none

-- Related callback environments can contain the same values in different tuples.
-- Compare the computations at those inputs, opening one named program at a time.
private partial def compareFrames (env : Core.Environment) (fuel : Nat) (a b : Term) :
    CommandElabM (Option Equation) := do
  if a == b then return some (unchanged a)
  if fuel == 0 then return none
  let compare := compareFrames env (fuel - 1)
  if let some h := (meetHeads env a b).run' 96 then return some h
  if let some h := (reduceTo env a b).run' 96 then return some h
  if let some h := (reduceTo env b a).run' 96 then return some ⟨a, b, join (unchanged a) h⟩
  if let (some (u, v), some (x, y)) := (pairArgs a, pairArgs b) then
    let some lhsEq ← compare u x | return none
    let some rhsEq ← compare v y | return none
    return some (pairEq lhsEq rhsEq)
  if let ((`FOL.Term.app, [_, .zero, u]), (`FOL.Term.app, [_, .zero, v])) := (ast a, ast b) then
    return (← compare u v).map succEq
  let (some (f, x), some (g, y)) := (programArgs a, programArgs b) | return none
  if f == g then
    return (← compare x y).map (programEq f)
  -- Use induction when both wrappers have exposed their recursion input.
  if (codeView env f).1 == `Primrec.Code.rec && (codeView env g).1 == `Primrec.Code.rec then
    return ← compareRecursions env a b compare
  let stop (opened code : Term) (_ : Term) : Bool :=
    code != opened && match getAppFnArgs code with
      | (.definition n _, _) => n == n.getPrefix ++ `code || n == `Primrec.Code.rec
      | _ => false
  let l ← normalize env (stop f) a
  let r ← normalize env (stop g) b
  if l.rhs == a && r.rhs == b then return none
  let some h ← compare l.rhs r.rhs | return none
  return some ⟨a, b, join (l.thenEq h) r⟩

-- First follow matching function symbols. A mismatch may be a defining equation at
-- just one argument of a much larger term.
private partial def compareApplications (env : Core.Environment) (a b : Term) :
    CommandElabM (Option Equation) := do
  if a == b then return some (unchanged a)
  let l := projectOrConst env a
  let r := projectOrConst env b
  if l.proof?.isSome || r.proof?.isSome then
    if l.rhs == r.rhs then return some ⟨a, b, join l r⟩
    if let some middle ← compareApplications env l.rhs r.rhs then
      return some ⟨a, b, join (l.thenEq middle) r⟩
  if let some (x, y) := pairArgs a then
    if let some (u, v) := pairArgs b then
      if let some lhsApp ← compareApplications env x u then
        if let some rhsApp ← compareApplications env y v then return some (pairEq lhsApp rhsApp)
  if let (`FOL.Term.app, [_, f, x]) := ast a then
    if let (`FOL.Term.app, [_, g, y]) := ast b then
      if f == g && f == numeral 0 then
        if let some child ← compareApplications env x y then return some (succEq child)
  let lhsApp := programArgs a
  let rhsApp := programArgs b
  if let some (f, x) := lhsApp then
    if let some (g, y) := rhsApp then
      if sameCode env f g then
        if let some child ← compareApplications env x y then
          return some { programEq f child with rhs := b }
      else if let (.definition n (_ :: _), .definition m (_ :: _)) := (f, g) then
        if n == m then
          if let some h ← compareFrames env 96 a b then return some h
          if let some h ← compareFamilies env a b then return some h
  if lhsApp.isNone && rhsApp.isNone then return none
  if let some (f, _) := lhsApp then
    if let some (g, _) := rhsApp then
      if wrapsProgram env f g then
        let codes := collectPrograms b []
        let reduced ← normalize env (fun e _ => sameCode env e g || codes.contains e) a
        if let some (e, x) := programArgs reduced.rhs then
          if let some (_, y) := rhsApp then
            if sameCode env e g then
              if let some h ← compareApplications env x y then
                return some (reduced.thenEq { programEq e h with rhs := b })
      if wrapsProgram env g f then
        let codes := collectPrograms a []
        let reduced ← normalize env (fun e _ => sameCode env e f || codes.contains e) b
        if let some (e, y) := programArgs reduced.rhs then
          if let some (_, x) := lhsApp then
            if sameCode env e f then
              if let some h ← compareApplications env x y then
                return some ⟨a, b, join (programEq e h) reduced⟩
  let codes := collectPrograms a (collectPrograms b [])
  let openLeft := lhsApp.elim codes fun (f, _) => codes.erase f
  let openRight := rhsApp.elim codes fun (g, _) => codes.erase g
  let openBoth := rhsApp.elim openLeft fun (g, _) => openLeft.erase g
  let choices := [openRight, openLeft, openBoth].eraseDups
  if let some h ← compareRecursions env a b (compareApplications env) then return some h
  for evaluateClosed in [false, true] do
    for remaining in choices do
      let keep := fun e x => remaining.contains e && !(evaluateClosed && closedTuple x)
      let lhs ← normalize env keep a
      let rhs ← normalize env keep b
      if lhs.rhs == rhs.rhs then return some ⟨a, b, join lhs rhs⟩
  return none

/-- Construct an inner Hilbert equality from program equations, keeping variable inputs symbolic. -/
def proveTermEquality (a b : Term) : CommandElabM Proof := do
  let env := CoreEnvironment.getState (← getEnv)
  if a == b then return (unchanged a).proof
  if let some (e, x) := programArgs a then
    if let some (f, y) := programArgs b then
      if x == y then
        let lhs ← forwardArgument env e x
        let rhs ← forwardArgument env f y
        if lhs.rhs == rhs.rhs then return join lhs rhs
  if let some h := (reduceTo env a b).run' 128 then return h.proof
  if let some h := (reduceTo env b a).run' 128 then
    return applyTheorem `FOL.PRA.Evaluation.symm [b, a] [] [h.proof]
  if let some h := (meetHeads env a b).run' 96 then return h.proof
  if let some h ← compareFamilies env a b then return h.proof
  let lhs ← selectBranch env a
  let rhs ← selectBranch env b
  if lhs.rhs != a || rhs.rhs != b then
    if lhs.rhs == rhs.rhs then return join lhs rhs
    if let some h ← compareApplications env lhs.rhs rhs.rhs then return join (lhs.thenEq h) rhs
  if let some h ← compareApplications env a b then return h.proof
  let lhs ← normalize env (fun _ _ => false) a
  let rhs ← normalize env (fun _ _ => false) b
  if lhs.rhs != rhs.rhs then
    if differentSyntax lhs.rhs rhs.rhs then
      throwError "the program equations leave different first-order term constructors"
    unless (defEqTerm 192 env 0 lhs.rhs rhs.rhs).toOption == some true do
      throwError "the first-order program equations leave different symbolic terms"
  return join lhs rhs

partial def sourceApplication (env : Core.Environment) (x y : Term)
    (args : List Equation) : Option Equation := do
  if x == y then return unchanged x
  if let some argument := args.find? (fun h => h.lhs == x && h.rhs == y) then
    return argument
  if let (some (p, u), some (q, v)) := (programArgs x, programArgs y) then
    guard (sameCode env p q)
    let h ← sourceApplication env u v args
    return { programEq p h with rhs := y }
  if let (some (a, b), some (c, d)) := (pairArgs x, pairArgs y) then
    return pairEq (← sourceApplication env a c args) (← sourceApplication env b d args)
  if let ((`FOL.Term.app, [_, .zero, a]), (`FOL.Term.app, [_, .zero, b])) := (ast x, ast y) then
    return succEq (← sourceApplication env a b args)
  none

-- Interpret the compiler's composition, pairing and projections around a call.
private partial def routeProgram (env : Core.Environment) (stop : Term → Term → Bool)
    (template x : Term) (actuals : List Term := []) : CommandElabM Equation := do
  let instantiate := fun t : Term => if actuals.isEmpty then t else t.instantiate actuals
  let code := instantiate template
  let lhs := evalTerm code x
  if stop code x || (ast template).1.getPrefix != `Primrec.Code then return unchanged lhs
  match codeView env template with
  | (`Primrec.Code.comp, [outerCode, innerCode]) =>
    let f := instantiate outerCode
    let g := instantiate innerCode
    let inner ← routeProgram env stop innerCode x actuals
    let outer ← routeProgram env stop outerCode inner.rhs actuals
    if inner.proof?.isNone then
      return (equation `eval_comp [f, g, x] lhs outer.lhs).thenEq outer
    return ⟨lhs, outer.rhs, applyTheorem `FOL.PRA.Evaluation.eval_comp_of_values
      [] [f, g, x, inner.rhs, outer.rhs] [inner.proof, outer.proof]⟩
  | (`Primrec.Code.pair, [l, r]) =>
    let f := instantiate l
    let g := instantiate r
    let a ← routeProgram env stop l x actuals
    let b ← routeProgram env stop r x actuals
    let rhs := mkPair a.rhs b.rhs
    if a.proof?.isNone && b.proof?.isNone then return equation `eval_pair [f, g, x] lhs rhs
    return ⟨lhs, rhs, applyTheorem `FOL.PRA.Evaluation.eval_pair_of_values
      [] [f, g, x, a.rhs, b.rhs] [a.proof, b.proof]⟩
  | (`Primrec.Code.left, []) | (`Primrec.Code.right, []) =>
    if (pairArgs x).isNone && x != zeroTerm then return unchanged lhs
    let some h := headEquation env lhs | throwError "missing target projection equation"
    return h
  | (`Primrec.Code.const, [_]) => compute env (fun _ _ => false) code x
  | (`Primrec.Code.zero, []) | (`Primrec.Code.succ, []) | (`Primrec.Code.id, []) =>
    let some h := headEquation env lhs | throwError "missing target primitive equation"
    return h
  | _ => return unchanged lhs

private partial def routeTerm (env : Core.Environment) (stop : Term → Term → Bool)
    (t : Term) : CommandElabM Equation := do
  if let some (a, b) := pairArgs t then
    return pairEq (← routeTerm env stop a) (← routeTerm env stop b)
  if let some (e, x) := programArgs t then
    let arg ← routeTerm env stop x
    let run ← routeProgram env stop e arg.rhs
    return (programEq e arg).thenEq run
  if let (`FOL.Term.app, [_, .zero, a]) := ast t then return succEq (← routeTerm env stop a)
  return unchanged t

/-- A source function comparison, interpreted at the actual captures and ordinary input. -/
structure CallbackComparison where
  left : Term
  right : Term
  leftFrame : Term
  rightFrame : Term
  atInput : Nat → Term → Term → Term → CommandElabM Equation

private def atFrame (x frame : Term) : Bool :=
  (pairArgs x).any (fun (actual, _) => actual == frame)

/-- Lift a quoted input across fresh object binders. -/
def underBinders (depth : Nat) (t : Term) : CommandElabM Term := do
  if depth == 0 then return t
  let some u := shiftTerm depth t | throwError "cannot shift a translated input"
  return u

private def shiftCallback (depth : Nat) (rule : CallbackComparison) :
    CommandElabM CallbackComparison := do
  return { rule with
    leftFrame := ← underBinders depth rule.leftFrame
    rightFrame := ← underBinders depth rule.rightFrame }

/-- Interpret the input wiring of a callback environment before comparing calls. -/
def captureFrame (t : Term) : CommandElabM Term := do
  let env := CoreEnvironment.getState (← getEnv)
  return (← routeTerm env (fun _ _ => false) t).rhs

-- Compare evaluations in their respective environments. Each recursion step adds two binders.
private partial def substitutionEquation (env : Core.Environment) (x y : Term)
    (callbacks : List CallbackComparison := []) (depth : Nat := 0)
    (arguments : List Equation := []) (unfolding : Bool := false) : CommandElabM Equation := do
  if x == y then return unchanged x
  if let some h := arguments.find? (fun h => h.lhs == x && h.rhs == y) then return h
  let compare := fun a b => substitutionEquation env a b callbacks depth arguments unfolding
  if let (some (a, b), some (c, d)) := (pairArgs x, pairArgs y) then
    return pairEq (← compare a c) (← compare b d)
  let stopLeft := fun f u => callbacks.any (fun cb => cb.left == f && atFrame u cb.leftFrame)
  let stopRight := fun g v => callbacks.any (fun cb => cb.right == g && atFrame v cb.rightFrame)
  if unfolding then
    if let (some (f, u), some (g, v)) := (programArgs x, programArgs y) then
      if f == g && (ast f).1.getPrefix != `Primrec.Code then return programEq f (← compare u v)
  let route := fun stop t => do
    if !unfolding then return ← routeTerm env stop t
    let some (p, u) := programArgs t | return unchanged t
    routeProgram env stop p u
  let l ← route stopLeft x
  let r ← route stopRight y
  if l.rhs != x || r.rhs != y then
    return ⟨x, y, some (join (l.thenEq (← compare l.rhs r.rhs)) r)⟩
  if let ((`FOL.Term.app, [_, .zero, a]), (`FOL.Term.app, [_, .zero, b])) := (ast x, ast y) then
    return succEq (← compare a b)
  let (some (f, u), some (g, v)) := (programArgs x, programArgs y) |
    throwError "different terms {repr x} and {repr y}"
  if let some rule := callbacks.find? (fun cb => cb.left == f && cb.right == g &&
      atFrame u cb.leftFrame && atFrame v cb.rightFrame) then
    let (some (lc, a), some (rc, b)) := (pairArgs u, pairArgs v) |
      throwError "expected a callback environment and ordinary input"
    let h ← compare a b
    let call ← rule.atInput depth lc rc a
    return call.thenEq (programEq g (pairEq (unchanged rc) h))
  if f == g && callbacks.isEmpty then return programEq f (← compare u v)
  let (left, _) := getAppFnArgs f
  let (right, _) := getAppFnArgs g
  if let (.definition n fs, .definition m _) := (left, right) then
    let hasCallbacks := !callbacks.isEmpty && !fs.isEmpty
    if n == m && n.getPrefix != `Primrec.Code && (f != g || hasCallbacks) then
      let openBody (t : Term) := do
        let some body ← pure (unfoldTermHead env t).toOption.join |
          throwError "missing compiled body of {n}"
        pure (betaReduceTerm 192 body)
      let proof ← compare (evalTerm (← openBody f) u) (evalTerm (← openBody g) v)
      return { proof with lhs := x, rhs := y }
  if (ast f).1 == `Primrec.Code.rec && (ast g).1 == `Primrec.Code.rec then
    let under := fun k a b => do
      let shifted ← callbacks.mapM (shiftCallback k)
      some <$> substitutionEquation env a b shifted (depth + k) (if k == 0 then arguments else [])
        unfolding
    let (some (_, n), some (frame, m)) := (pairArgs u, pairArgs v) |
      throwError "expected packed recursion arguments"
    let counter ← compare n m
    let some proof ← recursionAtFrames env f g u (mkPair frame n) under |
      throwError "cannot translate the recursion base and step at their frames"
    return proof.thenEq (programEq g (pairEq (unchanged frame) counter))
  if f == g then return programEq f (← compare u v)
  throwError "incompatible compiled heads {repr left} and {repr right}"

/-- Lift recorded comparisons through the program of the enclosing call. -/
def compareCall (x y : Term) (callbacks : List CallbackComparison := [])
    (arguments : List Equation := []) : CommandElabM Equation := do
  substitutionEquation (CoreEnvironment.getState (← getEnv)) x y callbacks 0 arguments

/-- Read ordinary arguments in the compiler's right-nested tuple. -/
def ordinaryInputs (arity : Nat) (t : Term) : CommandElabM (List Term) := do
  match arity with
  | 0 => return []
  | 1 => return [t]
  | k + 2 =>
    let some (a, b) := pairArgs t | throwError "missing ordinary callback argument"
    return a :: (← ordinaryInputs (k + 1) b)

/-- Apply recursion congruence to the recorded base, step and counter comparisons. -/
def compareRecursor (x y : Term) (base counter : Equation) (step : CommandElabM Equation) :
    CommandElabM Equation := do
  let (some (f, u), some (g, v)) := (programArgs x, programArgs y) |
    throwError "expected two compiled recursors"
  let (some (_, n), some (frame, m)) := (pairArgs u, pairArgs v) |
    throwError "expected a recursion environment and counter"
  unless n == counter.lhs && m == counter.rhs do throwError "unexpected compiled counters"
  let premises := fun k a b => do
    let h ← if k == 0 then pure base else step
    let l ← compareCall a h.lhs
    let r ← compareCall h.rhs b
    pure (some ((l.thenEq h).thenEq r))
  let env := CoreEnvironment.getState (← getEnv)
  let some result ← recursionAtFrames env f g u (mkPair frame n) premises |
    throwError "could not instantiate recursion congruence"
  return result.thenEq (programEq g (pairEq (unchanged frame) counter))

/-- Connect a recorded body equality to the two callback evaluations at this ordinary input. -/
def callbackInstance (f g left right arg : Term) (body : Equation) : CommandElabM Equation := do
  let a ← compareCall (evalTerm f (mkPair left arg)) body.lhs
  let b ← compareCall body.rhs (evalTerm g (mkPair right arg))
  return (a.thenEq body).thenEq b

/-- Interpret the compiled body at the callback programs and packed input of the source call.
At a formal callback, leave its evaluation intact until the instantiated body needs its value. -/
def unfoldEquation (code input y : Term) : CommandElabM Equation := do
  let x := evalTerm code input
  let env := CoreEnvironment.getState (← getEnv)
  let .definition name programs := code | throwError "expected a registered program"
  let some (.function d) := env.lookup name | throwError "missing compiled definition {name}"
  let run ← routeProgram env (fun _ _ => false) (betaReduceTerm 192 d.body) input programs
  let start := { run with lhs := x }
  return start.thenEq (← substitutionEquation env run.rhs y (unfolding := true))

/-- Build the object equation for the contraction recorded at the source head. -/
def recordedEquation (x y : Term) (h : HeadReduction) : CommandElabM Equation := do
  if x == y then return unchanged x
  let env := CoreEnvironment.getState (← getEnv)
  if h matches .recZero | .recSucc then
    let some step ← pure (headEquation env x) | throwError "missing recursion equation"
    return step.thenEq (← substitutionEquation env step.rhs y)
  return ← substitutionEquation env x y

/-- Take the recursion equation determined by a closed counter. Its frame contains the base
and the step's captures, which can remain symbolic while the counter is evaluated. -/
def closedRecursionStep (a b : Term) : CommandElabM Proof := do
  let env := CoreEnvironment.getState (← getEnv)
  let some (r, arg) := programArgs a | throwError "expected a compiled recursion"
  let some (frame, count) := pairArgs arg | throwError "expected a frame and a counter"
  let counter ← normalize env (fun _ _ => false) count
  let input := programEq r (pairEq (unchanged frame) counter)
  let some step := headEquation env input.rhs | throwError "expected a numerical recursion equation"
  let some (f, x) := programArgs step.rhs | throwError "expected a compiled recursion body"
  let routed ← compute env (fun e _ => (ast e).1.getPrefix != `Primrec.Code) f x
  let h := (input.thenEq step).thenEq routed
  let tail ← proveTermEquality h.rhs b
  return (h.thenEq ⟨h.rhs, b, some tail⟩).proof

/-- Compare the input routing and the two bodies of a compiled recursion at arbitrary inputs. -/
def compiledRecursionEquation (a b : Term) : CommandElabM Proof := do
  let env := CoreEnvironment.getState (← getEnv)
  let compare := fun x y => do
    let keep := fun e _ => (ast e).1.getPrefix != `Primrec.Code
    let lhs ← normalize env keep x
    let rhs ← normalize env keep y
    let some h := sourceApplication env lhs.rhs rhs.rhs [] |
      throwError "the two compiled recursion bodies give different terms at the same input"
    return some ⟨x, y, join (lhs.thenEq h) rhs⟩
  let some h ← compareRecursions env a b compare |
    throwError "the compiled recursions have different inputs"
  return h.proof

def shortEquality (env : Core.Environment) (a b : Term) (budget : Nat := 64) :
    Option Equation :=
  ((meetHeads env a b).run' budget).orElse fun () =>
    ((reduceTo env a b).run' budget).orElse fun () =>
      ((reduceTo env b a).run' budget).map fun reverse => ⟨a, b, join (unchanged a) reverse⟩

-- Keep a shared program folded and compare the input it receives from a composition.
private def exactComposition (env : Core.Environment) (a b : Term) : Option Equation := do
  let (target, y) ← programArgs b
  for step in compositionHeads env a do
    let some (code, x) := programArgs step.rhs | continue
    if step.rhs == a || code != target then continue
    let some input := shortEquality env x y 1200 | continue
    return step.thenEq (programEq code input)
  none

-- A closure can assemble its input with several projections from the caller's frame.
-- Keep the programs supplied as arguments folded while computing that tuple.
private def compareCompositionInputs (env : Core.Environment) (a b : Term) :
    CommandElabM (Option Equation) := do
  let some (target, y) := programArgs b | return none
  for step in compositionHeads env a do
    let some (code, x) := programArgs step.rhs | continue
    if step.rhs == a || code != target then continue
    let codes := collectPrograms y []
    let keep := fun e _ => codes.contains e || (codeView env e).1 == `Primrec.Code.rec
    let lhs ← normalize env keep x
    let rhs ← normalize env keep y
    let some input := shortEquality env lhs.rhs rhs.rhs 128 | continue
    let h := ⟨x, y, some (join (lhs.thenEq input) rhs)⟩
    return some (step.thenEq (programEq code h))
  return none

private partial def evaluationSubterms (term : Term) : List Term :=
  if let some (_, input) := programArgs term then
    term :: evaluationSubterms input
  else if let some (a, b) := pairArgs term then
    evaluationSubterms a ++ evaluationSubterms b
  else if let (`FOL.Term.app, [_, .zero, arg]) := ast term then
    evaluationSubterms arg
  else []

-- Abstract an input that occurs on both sides. Its program stays opaque while
-- the equations for the enclosing operations are proved.
private partial def abstractInput (input term : Term) : Option (Term × Bool) := do
  if term == input then return (varTerm 0, true)
  if let some (code, arg) := programArgs term then
    let (arg, found) ← abstractInput input arg
    return (evalTerm code arg, found)
  if let some (a, b) := pairArgs term then
    let (a, lhs) ← abstractInput input a
    let (b, rhs) ← abstractInput input b
    return (mkPair a b, lhs || rhs)
  if let (`FOL.Term.app, [_, .zero, arg]) := ast term then
    let (arg, found) ← abstractInput input arg
    return (succTerm arg, found)
  return (← shiftTerm 1 term, false)

private def abstractEquation (env : Core.Environment) (a b : Term) :
    CommandElabM (Option Equation) := do
  for input in (evaluationSubterms a).take 8 do
    if input == a || input == b then continue
    let some (rhs, true) := abstractInput input b | continue
    let some (lhs, true) := abstractInput input a | continue
    let some eq := shortEquality env lhs rhs | continue
    let body := formulaEqual lhs rhs
    let general := innerRule `FOL.Provable.gen [body] [eq.proof]
    let specialized ← specializeInner body input (formulaEqual a b) general
    return some ⟨a, b, specialized⟩
  return none

private def exposeRecursion (env : Core.Environment) (term : Term) : Equation := Id.run do
  let mut result := unchanged term
  for _ in List.range 12 do
    if let some (code, _) := programArgs result.rhs then
      if (headRecursion? env code).isSome then break
    let some step := headEquation env result.rhs | break
    result := result.thenEq step
  return result

partial def sourceEdge (env : Core.Environment) (a b : Term) (budget : Nat := 64)
    (depth : Nat := 3) : CommandElabM (Option Equation) := do
  if let some eq := shortEquality env a b budget then return some eq
  if let some eq := exactComposition env a b then return some eq
  if let some eq := exactComposition env b a then
    return some ⟨a, b, join (unchanged a) eq⟩
  if depth == 0 then return none
  if let some eq ← compareCompositionInputs env a b then return some eq
  if let some eq ← compareCompositionInputs env b a then
    return some ⟨a, b, join (unchanged a) eq⟩
  if let some eq ← abstractEquation env a b then return some eq
  let lhs := exposeRecursion env a
  let rhs := exposeRecursion env b
  let compare := fun x y => sourceEdge env x y 64 (depth - 1)
  let some eq ← compareRecursions env lhs.rhs rhs.rhs compare | return none
  return some ⟨a, b, join (lhs.thenEq eq) rhs⟩

end PRAProver.Library.FOL.PRA.Derive.Evaluation

end
