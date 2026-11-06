module

public import LeanPRA.Metatheory.Core.Judgement.Substitution

/-!
# Renaming and substituting proof hypotheses

- `Proof.renameHypotheses` changes only proof-hypothesis indices.
- `Proof.substHypotheses` inserts explicit proofs for hypotheses while keeping numerical data.
- `ProofTyping.renameHypotheses` and `ProofTyping.substHypotheses` prove preservation.
- `ProofTyping.weakenHypothesis` and `ProofTyping.substHypothesis0` handle one added assumption.

Proof and number binders have distinct effects. A proof binder shifts kept hypothesis indices;
a number binder shifts numerical occurrences in inserted proofs and their hypothesis formulas.
-/

namespace LeanPRA.Core

/-- Rename only proof-hypothesis indices, lifting under newly introduced proof hypotheses. -/
@[expose] public def Proof.renameHypotheses (r : Renaming) : Proof → Proof
  | .hyp i => .hyp (r i)
  | .trueIntro => .trueIntro
  | .theoremE name fs ps => .theoremE name fs ps
  | .impIntro binderName A p => .impIntro binderName A
      (p.renameHypotheses (Renaming.lift 1 r))
  | .impElim p q => .impElim (p.renameHypotheses r) (q.renameHypotheses r)
  | .andIntro p q => .andIntro (p.renameHypotheses r) (q.renameHypotheses r)
  | .andLeft p => .andLeft (p.renameHypotheses r)
  | .andRight p => .andRight (p.renameHypotheses r)
  | .orLeft A p => .orLeft A (p.renameHypotheses r)
  | .orRight A p => .orRight A (p.renameHypotheses r)
  | .orElim leftName rightName A p q s => .orElim leftName rightName A (p.renameHypotheses r)
      (q.renameHypotheses (Renaming.lift 1 r)) (s.renameHypotheses (Renaming.lift 1 r))
  | .falseElim A p => .falseElim A (p.renameHypotheses r)
  | .forallIntro binderName P p => .forallIntro binderName P (p.renameHypotheses r)
  | .forallElim p a => .forallElim (p.renameHypotheses r) a
  | .existsIntro P a p => .existsIntro P a (p.renameHypotheses r)
  | .existsElim variableName hypothesisName A p q =>
      .existsElim variableName hypothesisName A
        (p.renameHypotheses r) (q.renameHypotheses (Renaming.lift 1 r))
  | .letE binderName A p q => .letE binderName A
      (p.renameHypotheses r) (q.renameHypotheses (Renaming.lift 1 r))
  | .letTerm binderName a p => .letTerm binderName a (p.renameHypotheses r)
  | .letPredicate binderName P p => .letPredicate binderName P (p.renameHypotheses r)
  | .ascribe A p => .ascribe A (p.renameHypotheses r)
  | .eqRefl t => .eqRefl t
  | .eqSubst P e p => .eqSubst P (e.renameHypotheses r) (p.renameHypotheses r)
  | .succNeZero t => .succNeZero t
  | .succInj p => .succInj (p.renameHypotheses r)
  | .lem A => .lem A
  | .induction variableName hypothesisName P b s a =>
      .induction variableName hypothesisName P
        (b.renameHypotheses r) (s.renameHypotheses (Renaming.lift 1 r)) a

/-- Extend a proof substitution under a new proof hypothesis. -/
@[expose] public def Proof.liftHypotheses (s : Nat → Proof) : Nat → Proof
  | 0 => .hyp 0
  | i + 1 => (s i).renameHypotheses (fun j => j + 1)

/-- Substitute proofs for hypotheses. Number binders weaken the numerical occurrences in every
kept actual; proof binders weaken the kept proof-hypothesis indices. -/
@[expose] public def Proof.substHypotheses (s : Nat → Proof) : Proof → Proof
  | .hyp i => s i
  | .trueIntro => .trueIntro
  | .theoremE name fs ps => .theoremE name fs ps
  | .impIntro binderName A p => .impIntro binderName A
      (p.substHypotheses (Proof.liftHypotheses s))
  | .impElim p q => .impElim (p.substHypotheses s) (q.substHypotheses s)
  | .andIntro p q => .andIntro (p.substHypotheses s) (q.substHypotheses s)
  | .andLeft p => .andLeft (p.substHypotheses s)
  | .andRight p => .andRight (p.substHypotheses s)
  | .orLeft A p => .orLeft A (p.substHypotheses s)
  | .orRight A p => .orRight A (p.substHypotheses s)
  | .orElim leftName rightName A p q r => .orElim leftName rightName A (p.substHypotheses s)
      (q.substHypotheses (Proof.liftHypotheses s)) (r.substHypotheses (Proof.liftHypotheses s))
  | .falseElim A p => .falseElim A (p.substHypotheses s)
  | .forallIntro binderName P p => .forallIntro binderName P
      (p.substHypotheses (fun i => (s i).rename (fun j => j + 1)))
  | .forallElim p a => .forallElim (p.substHypotheses s) a
  | .existsIntro P a p => .existsIntro P a (p.substHypotheses s)
  | .existsElim variableName hypothesisName A p q =>
      .existsElim variableName hypothesisName A
        (p.substHypotheses s)
        (q.substHypotheses (Proof.liftHypotheses (fun i => (s i).rename (fun j => j + 1))))
  | .letE binderName A p q => .letE binderName A
      (p.substHypotheses s) (q.substHypotheses (Proof.liftHypotheses s))
  | .letTerm binderName a p => .letTerm binderName a (p.substHypotheses s)
  | .letPredicate binderName P p => .letPredicate binderName P (p.substHypotheses s)
  | .ascribe A p => .ascribe A (p.substHypotheses s)
  | .eqRefl t => .eqRefl t
  | .eqSubst P e p => .eqSubst P (e.substHypotheses s) (p.substHypotheses s)
  | .succNeZero t => .succNeZero t
  | .succInj p => .succInj (p.substHypotheses s)
  | .lem A => .lem A
  | .induction variableName hypothesisName P b step a =>
      .induction variableName hypothesisName P
        (b.substHypotheses s)
        (step.substHypotheses (Proof.liftHypotheses (fun i => (s i).rename (fun j => j + 1)))) a

end LeanPRA.Core

namespace LeanPRA.Core.Theory

/-- A hypothesis renaming preserves each looked-up formula literally. -/
@[expose] public def HypothesisRenamingTyping (H K : ProofContext) (r : Renaming) : Prop :=
  ∀ (i : Nat) A, H[i]? = some A → K[r i]? = some A

/-- Each source hypothesis is replaced by an explicit proof of the same formula. -/
@[expose] public def HypothesisSubstitutionTyping (E : Environment) (Ξ : ParameterContext)
    (Γ : LocalContext) (H K : ProofContext) (s : Nat → Proof) : Prop :=
  ∀ (i : Nat) A, H[i]? = some A → ProofTyping E Ξ Γ K (s i) A

private theorem renaming_cons {H K r} (h : HypothesisRenamingTyping H K r) (A : Predicate) :
    HypothesisRenamingTyping (A :: H) (A :: K) (Renaming.lift 1 r) := by
  intro i B hi
  cases i with
  | zero => simpa [Renaming.lift] using hi
  | succ i => simpa [Renaming.lift, Nat.add_comm] using h i B hi

private theorem renaming_shift {H K r} (h : HypothesisRenamingTyping H K r) :
    HypothesisRenamingTyping (H.map Predicate.shift) (K.map Predicate.shift) r := by
  intro i A lookup
  rw [List.getElem?_map] at lookup
  cases hi : H[i]? with
  | none => simp [hi] at lookup
  | some B =>
      have hA : B.shift = A := Option.some.inj (by simpa [hi] using lookup)
      subst A
      simp [List.getElem?_map, h i B hi]

private theorem proof_rename {E Ξ Γ H p A} (h : ProofTyping E Ξ Γ H p A)
    {K} (r : Renaming) (hr : HypothesisRenamingTyping H K r) :
    ProofTyping E Ξ Γ K (p.renameHypotheses r) A := by
  induction h generalizing K r with
  | hyp lookup => simp only [Proof.renameHypotheses]; exact .hyp (hr _ _ lookup)
  | trueIntro => simp only [Proof.renameHypotheses]; exact .trueIntro
  | theoremE lookup functions predicates =>
      simp only [Proof.renameHypotheses]; exact .theoremE lookup functions predicates
  | impIntro type body ih =>
      simp only [Proof.renameHypotheses]; exact .impIntro type (ih _ (renaming_cons hr _))
  | impElim p q ihp ihq => simp only [Proof.renameHypotheses]; exact .impElim (ihp _ hr) (ihq _ hr)
  | andIntro p q ihp ihq =>
      simp only [Proof.renameHypotheses]; exact .andIntro (ihp _ hr) (ihq _ hr)
  | andLeft p ih => simp only [Proof.renameHypotheses]; exact .andLeft (ih _ hr)
  | andRight p ih => simp only [Proof.renameHypotheses]; exact .andRight (ih _ hr)
  | orLeft type p ih => simp only [Proof.renameHypotheses]; exact .orLeft type (ih _ hr)
  | orRight type p ih => simp only [Proof.renameHypotheses]; exact .orRight type (ih _ hr)
  | orElim target p q s ihp ihq ihs =>
      simp only [Proof.renameHypotheses]
      exact .orElim target (ihp _ hr) (ihq _ (renaming_cons hr _)) (ihs _ (renaming_cons hr _))
  | falseElim type p ih => simp only [Proof.renameHypotheses]; exact .falseElim type (ih _ hr)
  | forallIntro motive body ih =>
      simp only [Proof.renameHypotheses]; exact .forallIntro motive (ih _ (renaming_shift hr))
  | forallElim p a ih => simp only [Proof.renameHypotheses]; exact .forallElim (ih _ hr) a
  | existsIntro motive witness p ih =>
      simp only [Proof.renameHypotheses]; exact .existsIntro motive witness (ih _ hr)
  | existsElim target p q ihp ihq =>
      simp only [Proof.renameHypotheses]
      exact .existsElim target (ihp _ hr) (ihq _ (renaming_cons (renaming_shift hr) _))
  | letE type p q ihp ihq =>
      simp only [Proof.renameHypotheses]; exact .letE type (ihp _ hr) (ihq _ (renaming_cons hr _))
  | letTerm value body ih => simp only [Proof.renameHypotheses]; exact .letTerm value (ih _ hr)
  | letPredicate value body ih =>
      simp only [Proof.renameHypotheses]; exact .letPredicate value (ih _ hr)
  | ascribe type p ih => simp only [Proof.renameHypotheses]; exact .ascribe type (ih _ hr)
  | eqRefl term => simp only [Proof.renameHypotheses]; exact .eqRefl term
  | eqSubst motive e p ihe ihp =>
      simp only [Proof.renameHypotheses]; exact .eqSubst motive (ihe _ hr) (ihp _ hr)
  | succNeZero term => simp only [Proof.renameHypotheses]; exact .succNeZero term
  | succInj p ih => simp only [Proof.renameHypotheses]; exact .succInj (ih _ hr)
  | lem formula => simp only [Proof.renameHypotheses]; exact .lem formula
  | induction motive base step argument ihb ihs =>
      simp only [Proof.renameHypotheses]
      exact .induction motive (ihb _ hr) (ihs _ (renaming_cons (renaming_shift hr) _)) argument
  | conversion p type ih => exact .conversion (ih _ hr) type

private theorem substitution_cons {E Ξ Γ H K s}
    (h : HypothesisSubstitutionTyping E Ξ Γ H K s) (A : Predicate) :
    HypothesisSubstitutionTyping E Ξ Γ (A :: H) (A :: K) (Proof.liftHypotheses s) := by
  intro i B hi
  cases i with
  | zero => simp only [Proof.liftHypotheses]; exact .hyp hi
  | succ i =>
      simp only [Proof.liftHypotheses]
      exact proof_rename (h i B hi) _ (by intro j C hj; exact hj)

private theorem substitution_shift {E Ξ Γ H K s} (valid : EnvironmentWF E)
    (h : HypothesisSubstitutionTyping E Ξ Γ H K s) :
    HypothesisSubstitutionTyping E Ξ (0 :: Γ) (H.map Predicate.shift) (K.map Predicate.shift)
      (fun i => (s i).rename (fun j => j + 1)) := by
  intro i A lookup
  rw [List.getElem?_map] at lookup
  cases hi : H[i]? with
  | none => simp [hi] at lookup
  | some B =>
      have hA : B.shift = A := Option.some.inj (by simpa [hi] using lookup)
      subst A
      simpa only [Predicate.shift, Nat.not_lt_zero, ↓reduceIte] using
        ProofTyping.rename valid (h i B hi) (fun j => j + 1) (by intro j k hj; exact hj)

private theorem proof_subst {E Ξ Γ H p A} (valid : EnvironmentWF E)
    (h : ProofTyping E Ξ Γ H p A) {K} (s : Nat → Proof)
    (hs : HypothesisSubstitutionTyping E Ξ Γ H K s) :
    ProofTyping E Ξ Γ K (p.substHypotheses s) A := by
  induction h generalizing K s with
  | hyp lookup => simp only [Proof.substHypotheses]; exact hs _ _ lookup
  | trueIntro => simp only [Proof.substHypotheses]; exact .trueIntro
  | theoremE lookup functions predicates =>
      simp only [Proof.substHypotheses]; exact .theoremE lookup functions predicates
  | impIntro type body ih =>
      simp only [Proof.substHypotheses]; exact .impIntro type (ih _ (substitution_cons hs _))
  | impElim p q ihp ihq => simp only [Proof.substHypotheses]; exact .impElim (ihp _ hs) (ihq _ hs)
  | andIntro p q ihp ihq => simp only [Proof.substHypotheses]; exact .andIntro (ihp _ hs) (ihq _ hs)
  | andLeft p ih => simp only [Proof.substHypotheses]; exact .andLeft (ih _ hs)
  | andRight p ih => simp only [Proof.substHypotheses]; exact .andRight (ih _ hs)
  | orLeft type p ih => simp only [Proof.substHypotheses]; exact .orLeft type (ih _ hs)
  | orRight type p ih => simp only [Proof.substHypotheses]; exact .orRight type (ih _ hs)
  | orElim target p q r ihp ihq ihr =>
      simp only [Proof.substHypotheses]
      exact .orElim target (ihp _ hs) (ihq _ (substitution_cons hs _))
        (ihr _ (substitution_cons hs _))
  | falseElim type p ih => simp only [Proof.substHypotheses]; exact .falseElim type (ih _ hs)
  | forallIntro motive body ih =>
      simp only [Proof.substHypotheses]
      exact .forallIntro motive (ih _ (substitution_shift valid hs))
  | forallElim p a ih => simp only [Proof.substHypotheses]; exact .forallElim (ih _ hs) a
  | existsIntro motive witness p ih =>
      simp only [Proof.substHypotheses]; exact .existsIntro motive witness (ih _ hs)
  | existsElim target p q ihp ihq =>
      simp only [Proof.substHypotheses]
      exact .existsElim target (ihp _ hs)
        (ihq _ (substitution_cons (substitution_shift valid hs) _))
  | letE type p q ihp ihq =>
      simp only [Proof.substHypotheses]
      exact .letE type (ihp _ hs) (ihq _ (substitution_cons hs _))
  | letTerm value body ih => simp only [Proof.substHypotheses]; exact .letTerm value (ih _ hs)
  | letPredicate value body ih =>
      simp only [Proof.substHypotheses]; exact .letPredicate value (ih _ hs)
  | ascribe type p ih => simp only [Proof.substHypotheses]; exact .ascribe type (ih _ hs)
  | eqRefl term => simp only [Proof.substHypotheses]; exact .eqRefl term
  | eqSubst motive e p ihe ihp =>
      simp only [Proof.substHypotheses]; exact .eqSubst motive (ihe _ hs) (ihp _ hs)
  | succNeZero term => simp only [Proof.substHypotheses]; exact .succNeZero term
  | succInj p ih => simp only [Proof.substHypotheses]; exact .succInj (ih _ hs)
  | lem formula => simp only [Proof.substHypotheses]; exact .lem formula
  | induction motive base step argument ihb ihs =>
      simp only [Proof.substHypotheses]
      exact .induction motive (ihb _ hs)
        (ihs _ (substitution_cons (substitution_shift valid hs) _)) argument
  | conversion p type ih => exact .conversion (ih _ hs) type

/-- Renaming assumptions preserves a proof when every renamed index has the same formula. -/
public theorem ProofTyping.renameHypotheses {E Ξ Γ H p A} (h : ProofTyping E Ξ Γ H p A)
    {K} (r : Renaming) (hr : HypothesisRenamingTyping H K r) :
    ProofTyping E Ξ Γ K (p.renameHypotheses r) A := proof_rename h r hr

/-- A fresh proof hypothesis weakens every kept proof-hypothesis index. -/
public theorem ProofTyping.weakenHypothesis {E Ξ Γ H p A} (h : ProofTyping E Ξ Γ H p A)
    (B : Predicate) : ProofTyping E Ξ Γ (B :: H) (p.renameHypotheses (fun i => i + 1)) A :=
  proof_rename h _ (by intro i C hi; exact hi)

/-- Substituting checked explicit proofs for assumptions preserves the conclusion. -/
public theorem ProofTyping.substHypotheses {E Ξ Γ H p A} (valid : EnvironmentWF E)
    (h : ProofTyping E Ξ Γ H p A) {K} (s : Nat → Proof)
    (hs : HypothesisSubstitutionTyping E Ξ Γ H K s) :
    ProofTyping E Ξ Γ K (p.substHypotheses s) A := proof_subst valid h s hs

/-- Substitute one proof for the newest assumption and remove that assumption's binder. -/
public theorem ProofTyping.substHypothesis0 {E Ξ Γ H p A q B} (valid : EnvironmentWF E)
    (body : ProofTyping E Ξ Γ (B :: H) p A) (value : ProofTyping E Ξ Γ H q B) :
    ProofTyping E Ξ Γ H (p.substHypotheses (fun | 0 => q | i + 1 => .hyp i)) A := by
  apply proof_subst valid body
  intro i C hi
  cases i with
  | zero => have hc := Option.some.inj hi; subst hc; exact value
  | succ i => exact .hyp hi

end LeanPRA.Core.Theory
