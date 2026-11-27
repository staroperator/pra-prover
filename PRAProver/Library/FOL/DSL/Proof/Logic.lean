module

public meta import PRAProver.Library.FOL.DSL.Proof.Derivation

/-!
# Logical steps for first-order proofs

These operations construct Hilbert derivations for the usual introduction and elimination rules.
Conjunction, disjunction, and existence use the encodings in `FormulaView`.

- `falseElim` and `doubleNegation` provide classical reasoning.
- `conjunctionIntro` and `disjunctionElim` combine propositional derivations.
- `existsIntro` and `existsElim` construct and use existential witnesses.
- `formulaTransport` substitutes equals throughout a formula.
- `propositional` proves a consequence by splitting on propositional atoms.
-/

public meta section

namespace PRAProver.Library.FOL.DSL

open Lean Elab Command

private def freshHypothesis (a : FormulaView) : DeriveM (Name × Nat) := do
  let h ← liftCoreM (mkFreshUserName `h)
  return (h, ← addNode a (.hypothesis h))

private def useLemma (name : Name) (arguments : List FormulaView) (schema : FormulaView)
    (premises : List Nat) : DeriveM (Option Nat) := do
  if ((PRAProver.Surface.CoreEnvironment.getState (← getEnv)).lookup name).isNone then return none
  let mut p ← addNode schema (.lemma name arguments)
  for q in premises do p ← mp p q
  return some p

def falseElim (a : FormulaView) (p : Nat) : DeriveM Nat := do
  if let some q ← useLemma `FOL.Provable.falsum_imp [a] (.imp .falsum a) [p] then return q
  let h ← mp (← axK FormulaView.falsum.neg a.neg) (← identity .falsum)
  let ax ← logical (.imp (.imp a.neg FormulaView.falsum.neg) (.imp .falsum a)) 2
    [.formula a, .formula .falsum, .number 0]
  mp (← mp ax h) p

def doubleNegation (a : FormulaView) (p : Nat) : DeriveM Nat := do
  if let some q ← useLemma `FOL.Provable.neg_neg_elim [a] (.imp a.neg.neg a) [p] then return q
  let (h, hn) ← freshHypothesis a.neg
  let (k, hnn) ← freshHypothesis a.neg.neg
  let q ← deduct h a.neg (← deduct k a.neg.neg (← mp hnn hn))
  let ax ← logical (.imp (.imp a.neg a.neg.neg.neg) (.imp a.neg.neg a)) 2
    [.formula a, .formula a.neg.neg, .number 0]
  mp (← mp ax q) p

def conjunctionIntro (p q : Nat) : DeriveM Nat := do
  let a ← conclusion p
  let b ← conclusion q
  if let some r ← useLemma `FOL.Provable.conj_intro [a, b]
      (.imp a (.imp b (a.conj b))) [p, q] then return r
  let (h, r) ← freshHypothesis (.imp a b.neg)
  deduct h (.imp a b.neg) (← mp (← mp r p) q)

def conjunctionLeft (p : Nat) : DeriveM Nat := do
  let .imp (.imp a (.imp b .falsum)) .falsum ← conclusion p |
    throwError "expected a conjunction"
  if let some q ← useLemma `FOL.Provable.conj_left [a, b] (.imp (a.conj b) a) [p] then
    return q
  let (h, hn) ← freshHypothesis a.neg
  let (k, ha) ← freshHypothesis a
  let q ← deduct k a (← falseElim b.neg (← mp hn ha))
  doubleNegation a (← deduct h a.neg (← mp p q))

def conjunctionRight (p : Nat) : DeriveM Nat := do
  let .imp (.imp a (.imp b .falsum)) .falsum ← conclusion p |
    throwError "expected a conjunction"
  if let some q ← useLemma `FOL.Provable.conj_right [a, b] (.imp (a.conj b) b) [p] then
    return q
  let (h, hn) ← freshHypothesis b.neg
  let q ← mp (← axK b.neg a) hn
  doubleNegation b (← deduct h b.neg (← mp p q))

def disjunctionLeft (b : FormulaView) (p : Nat) : DeriveM Nat := do
  let a ← conclusion p
  if let some q ← useLemma `FOL.Provable.disj_intro_left [a, b] (.imp a (a.disj b)) [p] then
    return q
  let (h, hn) ← freshHypothesis a.neg
  deduct h a.neg (← falseElim b (← mp hn p))

def disjunctionRight (a : FormulaView) (p : Nat) : DeriveM Nat := do
  mp (← axK (← conclusion p) a.neg) p

def disjunctionElim (p lhs rhs : Nat) : DeriveM Nat := do
  let .imp (.imp a .falsum) b ← conclusion p | throwError "expected a disjunction"
  let .imp _ c ← conclusion lhs | throwError "expected a branch implication"
  if let some q ← useLemma `FOL.Provable.disj_elim [a, b, c]
      (.imp (a.disj b) (.imp (.imp a c) (.imp (.imp b c) c))) [p, lhs, rhs] then return q
  let (h, hn) ← freshHypothesis c.neg
  let (k, ha) ← freshHypothesis a
  let na ← deduct k a (← mp hn (← mp lhs ha))
  let hb ← mp p na
  doubleNegation c (← deduct h c.neg (← mp hn (← mp rhs hb)))

def existsIntro (x : Name) (a : FormulaView) (t : TermView) (p : Nat) : DeriveM Nat := do
  let (h, hn) ← freshHypothesis (.all x a.neg)
  deduct h (.all x a.neg) (← mp (← instantiate hn t) p)

def existsElim (p branch : Nat) : DeriveM Nat := do
  let .imp (.all x (.imp a .falsum)) .falsum ← conclusion p |
    throwError "expected an existential formula"
  let .all y (.imp b c) ← conclusion branch | throwError "expected a quantified branch"
  unless (a.replace x (.var y)).equiv b && !c.variables.contains y do
    throwError "existential witness escapes its branch"
  let existential ← conclusion p
  let branchFormula ← conclusion branch
  let (exName, exProof) ← freshHypothesis existential
  let (branchName, branchProof) ← freshHypothesis branchFormula
  let (h, hn) ← freshHypothesis c.neg
  let (k, hb) ← freshHypothesis b
  let q ← instantiate branchProof (.var y)
  let nb ← generalize y (← deduct k b (← mp hn (← mp q hb)))
  let result ← doubleNegation c (← deduct h c.neg (← mp exProof nb))
  let lemma ← deduct exName existential (← deduct branchName branchFormula result)
  mp (← mp lemma p) branch

private partial def termTransport (x : Name) (p : Nat) (t : TermView) : DeriveM Nat := do
  let .equal a _ ← conclusion p | throwError "expected an equation"
  match t with
  | .var y => if x == y then return p else eqRefl t
  | .app i ts => eqCongr i (← ts.mapM (termTransport x p))
  | .indexedApp i k ts => eqCongr i (← ts.mapM (termTransport x p)) (some k)
  | .code _ _ args =>
    if args.any (fun t => t.variables.contains x) then
      throwError "substitution in an opaque term needs a substitution theorem"
    eqRefl t
  | _ => eqRefl (t.replace x a)

partial def formulaTransport (x : Name) (p : Nat) (a : FormulaView) (q : Nat) :
    DeriveM Nat := do
  let .equal s t ← conclusion p | throwError "expected an equation"
  match a with
  | .falsum => return q
  | .equal u v =>
    eqTrans (← eqSymm (← termTransport x p u)) (← eqTrans q (← termTransport x p v))
  | .relation i ts | .indexedRelation i _ ts =>
    let (rel, symbol) := match a with
      | .indexedRelation _ k _ => (FormulaView.indexedRelation i k, SchemaArg.member i k true)
      | _ => (FormulaView.relation i, SchemaArg.number i)
    let proofs ← ts.mapM (termTransport x p)
    let us := ts.map (·.replace x s)
    let vs := ts.map (·.replace x t)
    let result := FormulaView.imp (rel us) (rel vs)
    let schema := (us.zip vs).foldr (fun (u, v) r => .imp (.equal u v) r) result
    let mut r ← logical schema 10 [symbol, .tuple us, .tuple vs]
    for h in proofs do r ← mp r h
    mp r q
  | .imp b c =>
    let bt := b.replace x t
    let (h, hb) ← freshHypothesis bt
    let hs ← formulaTransport x (← eqSymm p) b hb
    deduct h bt (← formulaTransport x p c (← mp q hs))
  | .all y b =>
    -- Binder names are fresh, so a variable of the equation that is named like the binder
    -- is the bound variable itself, and the equation holds beneath the quantifier.
    if x == y then return q
    generalize y (← formulaTransport x p b (← instantiate q (.var y)))
  | .code _ _ args =>
    if args.any (fun t => t.variables.contains x) then
      throwError "substitution in an opaque formula needs a substitution theorem"
    return q
  | .parameter _ _ => throwError "uninstantiated formula parameter"

private def atoms : FormulaView → List FormulaView
  | .falsum => []
  | .imp a b => atoms a ++ atoms b
  | a => [a]

private partial def valuation (values : List (FormulaView × Bool × Nat))
    (a : FormulaView) : DeriveM (Bool × Nat) := do
  match a with
  | .falsum => return (false, ← identity .falsum)
  | .imp b c =>
    let (bv, bp) ← valuation values b
    let (cv, cp) ← valuation values c
    if cv then return (true, ← mp (← axK c b) cp)
    if !bv then
      let (h, hb) ← freshHypothesis b
      return (true, ← deduct h b (← falseElim c (← mp bp hb)))
    let (h, hi) ← freshHypothesis a
    return (false, ← deduct h a (← mp cp (← mp hi bp)))
  | _ =>
    let some (_, v, p) := values.find? (fun (b, _, _) => a.equiv b) |
      throwError "missing propositional atom"
    return (v, p)

private partial def splitAtoms (rest : List FormulaView)
    (values : List (FormulaView × Bool × Nat)) (a : FormulaView) : DeriveM Nat := do
  match rest with
  | [] =>
    let (v, p) ← valuation values a
    unless v do throwError "the supplied facts do not propositionally imply the goal"
    return p
  | b :: rest =>
    let (h, hb) ← freshHypothesis b
    let lhs ← deduct h b (← splitAtoms rest ((b, true, hb) :: values) a)
    let (k, hn) ← freshHypothesis b.neg
    let rhs ← deduct k b.neg (← splitAtoms rest ((b, false, hn) :: values) a)
    let (j, na) ← freshHypothesis a.neg
    let (l, pb) ← freshHypothesis b
    let nb ← deduct l b (← mp na (← mp lhs pb))
    doubleNegation a (← deduct j a.neg (← mp na (← mp rhs nb)))

/-- Prove a propositional consequence, treating quantified formulas and equations as atoms. -/
def propositional (target : FormulaView) (facts : List Nat) : DeriveM Nat := do
  for p in facts do
    if target.equiv (← conclusion p) then return p
  let premises ← facts.mapM conclusion
  let formula := premises.foldr FormulaView.imp target
  let mut unique : List FormulaView := []
  for a in atoms formula do
    unless unique.any (·.equiv a) do unique := unique ++ [a]
  if unique.length > 8 then throwError "too many atoms for propositional case splitting"
  let mut p ← splitAtoms unique [] formula
  for q in facts do p ← mp p q
  return p

end PRAProver.Library.FOL.DSL
