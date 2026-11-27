module

public import PRAProver.Metatheory.PRA.Basic

/-!
# Primitive-recursive witnesses for first-order PRA

Witness extraction for existential theorems of first-order PRA:

- `exists_primrec_witness` extracts a primitive recursive witness `f : Primrec n` and a
  `QFProof` derivation of `P.inst (.app f Term.var)` from a `Proof` of `∃' P.toFormula`.
- `forall_exists_primrec_witness` specializes this to closed `∀ x ∃ y` theorems with a
  quantifier-free matrix.

The proof interprets first-order formulas using a Friedman-style A-translation paired with a
Kripke-style context of quantifier-free assumptions, where falsity is interpreted by the existence
of a term witness for `P`. Conditionals (`Term.choose`) combine witnesses across case splits, and
primitive recursion (`Term.recApp`) iterates step witnesses across quantifier-free induction.
-/

namespace PRA

open QFFormula
open Term (choose recApp choose_subst recApp_subst)

variable {n : Nat}

namespace Witness

open QFProof

variable {φ ψ χ θ : QFFormula n}

private def merge (P : QFFormula (k + 1)) (v : Fin k → Term n) (s t : Term n) : Term n :=
  choose (P.subst (Fin.cases s v)) s t

private theorem merge_correct (P : QFFormula (k + 1)) (v : Fin k → Term n)
    (s t : Term n) :
    QFProof ((P.subst (Fin.cases s v) ⊔ P.subst (Fin.cases t v)) ⇒
      P.subst (Fin.cases (merge P v s t) v)) := by
  apply cases_rule (excluded_middle (P.subst (Fin.cases s v)))
  · apply imp_trans_rule _ imp_imp_self
    exact mp_under (instance_congr_under P v (imp_trans_rule (choose_left _ s t) eq_symm)) imp_refl
  · apply or_elim_under
    · exact imp_trans_under imp_refl (weaken false_elim)
    · exact instance_congr_under P v (imp_trans_rule (choose_right _ s t) eq_symm)

private def witnessStep (P : QFFormula (n + 1)) (t : Term (n + 1)) : Term (n + 2) :=
  choose (P.subst (Fin.cases (.var 1) (fun i => .var i.succ.succ))) (.var 1)
    (t.subst (Fin.cases (.var 0) (fun i => .var i.succ.succ)))

private theorem witnessStep_subst (P : QFFormula (k + 1)) (t : Term (k + 1))
    (x r : Term n) (v : Fin k → Term n) :
    (witnessStep P t).subst (Fin.cases x (Fin.cases r v)) =
      merge P v r (t.subst (Fin.cases x v)) := by
  simp only [witnessStep, choose_subst, QFFormula.subst_comp, Term.subst_comp,
    Fin.map_cases (fun t => Term.subst t (Fin.cases x (Fin.cases r v))),
    Term.subst, Fin.cases_one, Fin.cases_zero, Fin.cases_succ, merge]

-- The induction invariant is Γ.shift ⇒ A ⊔ P(r). The accumulator keeps a successful
-- witness; otherwise it takes the witness supplied by the next step.
private theorem iteration (A P : QFFormula (n + 1)) (Γ : QFFormula n)
    (b : Term n) (s : Term (n + 1))
    (hb : QFProof (Γ ⇒ A.inst 0 ⊔ P.inst b))
    (hs : QFProof (Γ.shift ⇒ (A ⇒ A.replace (.succ (.var 0))) ⊔
      P.subst (Fin.cases s (Term.var ∘ Fin.succ)))) (u : Term n) :
    ∃ t : Term n, QFProof (Γ ⇒ A.inst u ⊔ P.inst t) := by
  let r : Term (n + 1) := recApp b (witnessStep P s) (.var 0) (Term.var ∘ Fin.succ)
  let B := P.subst (Fin.cases r (Term.var ∘ Fin.succ))
  have hr₀ : QFProof (r.inst 0 ≡ b) := by
    simpa only [r, Term.inst, recApp_subst, Term.subst, Fin.cases_zero,
      Function.comp_apply, Fin.cases_succ, Term.subst_id] using
      recApp_zero b (witnessStep P s) Term.var
  have hrs : QFProof ((r.subst (Fin.cases (.succ (.var 0)) (Term.var ∘ Fin.succ))) ≡
      merge P (Term.var ∘ Fin.succ) r s) := by
    have h := recApp_succ b (witnessStep P s) (.var 0) (Term.var ∘ Fin.succ)
    rw [witnessStep_subst] at h
    have hv : (Fin.cases (Term.var 0) (Term.var ∘ Fin.succ) : Fin (n + 1) → Term (n + 1)) =
        Term.var := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    simp only [r, recApp_subst, Term.subst, Fin.cases_zero, Fin.cases_succ,
      Function.comp_apply, hv, Term.subst_id] at h ⊢
    exact h
  have hB : QFProof ((B ⊔ P.subst (Fin.cases s (Term.var ∘ Fin.succ))) ⇒
      B.replace (.succ (.var 0))) := by
    apply imp_trans_rule (merge_correct P (Term.var ∘ Fin.succ) r s)
    have h := instance_congr_under P (Term.var ∘ Fin.succ)
      (φ := ⊤) (weaken (eq_symm_rule hrs))
    have ht := mp h imp_refl
    simp only [B, QFFormula.replace, QFFormula.subst_cons,
      Function.comp_apply, Term.subst, Fin.cases_succ]
    exact ht
  have hnext : QFProof (Γ.shift ⇒ (A ⊔ B) ⇒
      A.replace (.succ (.var 0)) ⊔ B.replace (.succ (.var 0))) :=
    imp_trans_under (imp_trans_rule hs or_mp)
      (weaken (or_elim_imp or_left (imp_trans_rule hB or_right)))
  have hi : QFProof (Γ.shift ⇒ A ⊔ B) := by
    apply induction
    · have ht := mp (instance_congr_under P Term.var (φ := ⊤)
        (weaken (eq_symm_rule hr₀))) imp_refl
      have hb' := imp_trans_rule hb (or_elim_imp or_left (imp_trans_rule ht or_right))
      simp only [QFFormula.inst, QFFormula.subst, QFFormula.subst_shift, QFFormula.subst_id,
        B, QFFormula.subst_cons, Function.comp_apply, Term.subst, Fin.cases_succ] at hb' ⊢
      exact hb'
    · have hh := mp imp_distrib hnext
      simp only [QFFormula.replace, QFFormula.subst, QFFormula.subst_shift,
        Function.comp_apply, Fin.cases_succ] at hh ⊢
      exact hh
  refine ⟨r.inst u, ?_⟩
  have ht := QFProof.subst (v := Fin.cases u Term.var) hi
  simpa only [QFFormula.subst, QFFormula.subst_shift, Fin.cases_succ, QFFormula.subst_id,
    B, QFFormula.subst_comp, Fin.map_cases (fun t => Term.subst t (Fin.cases u Term.var)),
    Function.comp_apply, Term.subst, QFFormula.inst, Term.inst] using ht

namespace Forcing

private abbrev Val (k n : Nat) := Fin k → Term n

private def act (v : Val k n) (w : Val n m) : Val k m := fun i => (v i).subst w

private theorem act_id (v : Val k n) : act v Term.var = v := by
  funext i
  exact Term.subst_id (v i)

private theorem act_assoc (v : Val k n) (w : Val n m) (u : Val m l) :
    act (act v w) u = act v (act w u) := by
  funext i
  exact Term.subst_comp (v i) w u

private theorem act_cons (t : Term n) (v : Val k n) (w : Val n m) :
    act (Fin.cases t v) w = Fin.cases (t.subst w) (act v w) :=
  Fin.map_cases (fun t => t.subst w) t v

private theorem act_lift (σ : Val k l) (v : Val l n) (w : Val n m) (t : Term m) :
    act (Fin.cases (Term.var 0) (fun i => (σ i).shift))
      (Fin.cases t (act v w)) = Fin.cases t (act (act σ v) w) := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  simp only [act, Fin.cases_succ, Term.subst_shift, Term.subst_comp]

private theorem act_shift_cons (σ : Val k l) (v : Val l n) (t : Term n) :
    act (fun i => (σ i).shift) (Fin.cases t v) = act σ v := by
  funext i
  simp only [act, Term.subst_shift, Fin.cases_succ]

private theorem act_vars (v : Val k n) : act Term.var v = v := rfl

-- A world records QF assumptions and terms for the fixed existential matrix's parameters.
private structure World (r n : Nat) where
  ctx : QFFormula n
  env : Val r n

private def Ext (Γ : World r n) (Δ : World r m) (v : Val n m) : Prop :=
  QFProof (Δ.ctx ⇒ Γ.ctx.subst v) ∧ Δ.env = act Γ.env v

private theorem ext_id (Γ : World r n) : Ext Γ Γ Term.var := by
  constructor
  · simpa only [QFFormula.subst_id] using (imp_refl (φ := Γ.ctx))
  · exact (act_id Γ.env).symm

private theorem ext_comp {Γ : World r n} {Δ : World r m} {Θ : World r l}
    {v : Val n m} {w : Val m l} (h : Ext Γ Δ v) (h' : Ext Δ Θ w) :
    Ext Γ Θ (act v w) := by
  constructor
  · have ht := imp_trans_rule h'.1 (QFProof.subst (v := w) h.1)
    change QFProof (Θ.ctx ⇒ (Γ.ctx.subst v).subst w) at ht
    rw [QFFormula.subst_comp] at ht
    exact ht
  · rw [h'.2, h.2, act_assoc]

private abbrev Pred (r k : Nat) := ∀ {n}, World r n → Val k n → Prop

-- Falsity in this interpretation carries a provable instance of the fixed matrix.
private def bot (P : QFFormula (r + 1)) : Pred r k := fun Γ _ =>
  ∃ t, QFProof (Γ.ctx ⇒ P.subst (Fin.cases t Γ.env))

private def imp (p q : Pred r k) : Pred r k := fun {n} Γ v =>
  ∀ {m} (Δ : World r m) (w : Val n m), Ext Γ Δ w → p Δ (act v w) → q Δ (act v w)

private def conj (p q : Pred r k) : Pred r k := fun Γ v => p Γ v ∧ q Γ v

private def neg (P : QFFormula (r + 1)) (p : Pred r k) : Pred r k := imp p (bot P)

private def disj (P : QFFormula (r + 1)) (p q : Pred r k) : Pred r k :=
  neg P (conj (neg P p) (neg P q))

private def all (p : Pred r (k + 1)) : Pred r k := fun {n} Γ v =>
  ∀ {m} (Δ : World r m) (w : Val n m), Ext Γ Δ w →
    ∀ t : Term m, p Δ (Fin.cases t (act v w))

private def ex (P : QFFormula (r + 1)) (p : Pred r (k + 1)) : Pred r k :=
  neg P (all (neg P p))

-- A QF formula holds if it follows from the assumptions or a witness has already been found.
private def qf (P : QFFormula (r + 1)) (A : QFFormula k) : Pred r k := fun Γ v =>
  ∃ t, QFProof (Γ.ctx ⇒ A.subst v ⊔ P.subst (Fin.cases t Γ.env))

private def interp (P : QFFormula (r + 1)) : Formula k → Pred r k
  | .false => bot P
  | .eq s t => qf P (.eq s t)
  | .imp A B => imp (interp P A) (interp P B)
  | .and A B => conj (interp P A) (interp P B)
  | .or A B => disj P (interp P A) (interp P B)
  | .all A => all (interp P A)
  | .ex A => ex P (interp P A)

private def Monotone (p : Pred r k) : Prop :=
  ∀ {n m} {Γ : World r n} {Δ : World r m} {w : Val n m} {v : Val k n},
    Ext Γ Δ w → p Γ v → p Δ (act v w)

variable {P : QFFormula (r + 1)}

private theorem qf_monotone (A : QFFormula k) : Monotone (qf P A) := by
  intro n m Γ Δ w v he h
  obtain ⟨t, ht⟩ := h
  refine ⟨t.subst w, ?_⟩
  have hh := imp_trans_rule he.1 (QFProof.subst (v := w) ht)
  change QFProof (Δ.ctx ⇒ (A.subst v).subst w ⊔ (P.subst (Fin.cases t Γ.env)).subst w) at hh
  simp only [QFFormula.subst_comp, Fin.map_cases (fun t => Term.subst t w)] at hh
  rw [he.2]
  exact hh

private theorem qf_false : @qf r k P .false = @bot r k P := by
  funext n Γ v
  apply propext
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, imp_trans_rule ht (or_elim_imp false_elim imp_refl)⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, imp_trans_rule ht or_right⟩

private theorem bot_monotone : Monotone (bot P : Pred r k) := by
  rw [← qf_false]
  exact qf_monotone .false

private theorem imp_monotone (p q : Pred r k) : Monotone (imp p q) := by
  intro n m Γ Δ w v he h l Θ u he' hp
  have hp' : p Θ (act v (act w u)) := by simpa only [act_assoc] using hp
  have result := h Θ (act w u) (ext_comp he he') hp'
  simpa only [act_assoc] using result

private theorem conj_monotone {p q : Pred r k} (hp : Monotone p) (hq : Monotone q) :
    Monotone (conj p q) := by
  intro n m Γ Δ w v he h
  exact ⟨hp he h.1, hq he h.2⟩

private theorem all_monotone (p : Pred r (k + 1)) : Monotone (all p) := by
  intro n m Γ Δ w v he h l Θ u he' t
  have result := h Θ (act w u) (ext_comp he he') t
  simpa only [act_assoc] using result

private theorem interp_monotone (A : Formula k) : Monotone (interp P A) := by
  induction A with
  | false => exact bot_monotone
  | eq s t => exact qf_monotone _
  | imp A B => exact imp_monotone _ _
  | and A B ihA ihB => exact conj_monotone ihA ihB
  | or A B => exact imp_monotone _ _
  | all A => exact all_monotone _
  | ex A => exact imp_monotone _ _

private theorem imp_elim {p q : Pred r k} {Γ : World r n} {v : Val k n}
    (h : imp p q Γ v) (hp : p Γ v) : q Γ v := by
  have result := h Γ Term.var (ext_id Γ)
  simpa only [act_id] using result (by simpa only [act_id] using hp)

private theorem qf_imp (A B : QFFormula k) :
    @imp r k (@qf r k P A) (@qf r k P B) = @qf r k P (A ⇒ B) := by
  funext n Γ v
  apply propext
  constructor
  · intro h
    let Δ : World r n := ⟨Γ.ctx ⊓ A.subst v, Γ.env⟩
    have he : Ext Γ Δ Term.var := by
      constructor
      · simpa only [QFFormula.subst_id] using (and_left (φ := Γ.ctx) (ψ := A.subst v))
      · exact (act_id Γ.env).symm
    have ha : qf P A Δ (act v Term.var) := by
      refine ⟨0, ?_⟩
      simpa only [act_id] using imp_trans_rule (and_right (φ := Γ.ctx) (ψ := A.subst v)) or_left
    obtain ⟨t, ht⟩ := h Δ Term.var he ha
    refine ⟨t, ?_⟩
    simp only [act_id] at ht
    exact imp_trans_rule (and_curry ht) imp_or
  · intro h m Δ w he ha
    obtain ⟨s, hs⟩ := qf_monotone (A ⇒ B) he h
    obtain ⟨t, ht⟩ := ha
    refine ⟨merge P Δ.env t s, ?_⟩
    exact imp_trans_rule (mp_under (imp_trans_rule hs or_mp) ht)
      (or_map imp_refl (merge_correct P Δ.env t s))

private theorem qf_conj (A B : QFFormula k) :
    @conj r k (@qf r k P A) (@qf r k P B) = @qf r k P (A ⊓ B) := by
  funext n Γ v
  apply propext
  constructor
  · rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    refine ⟨merge P Γ.env s t, ?_⟩
    exact imp_trans_rule (mp_under (imp_trans_rule hs or_and) ht)
      (or_map imp_refl (merge_correct P Γ.env s t))
  · rintro ⟨t, ht⟩
    exact ⟨⟨t, imp_trans_rule ht (or_map and_left imp_refl)⟩,
      ⟨t, imp_trans_rule ht (or_map and_right imp_refl)⟩⟩

private theorem qf_neg (A : QFFormula k) : @neg r k P (@qf r k P A) = @qf r k P (∼ A) := by
  unfold neg
  rw [← qf_false]
  exact qf_imp A .false

private theorem qf_transport {A B : QFFormula k} (h : QFProof (A ⇒ B))
    {Γ : World r n} {v : Val k n} (ha : qf P A Γ v) : qf P B Γ v := by
  obtain ⟨t, ht⟩ := ha
  exact ⟨t, imp_trans_rule ht (or_map (QFProof.subst (v := v) h) imp_refl)⟩

private theorem qf_congr {A B : QFFormula k} (h₁ : QFProof (A ⇒ B))
    (h₂ : QFProof (B ⇒ A)) : @qf r k P A = @qf r k P B := by
  funext n Γ v
  exact propext ⟨qf_transport h₁, qf_transport h₂⟩

private theorem qf_disj (A B : QFFormula k) :
    @disj r k P (@qf r k P A) (@qf r k P B) = @qf r k P (A ⊔ B) := by
  unfold disj
  rw [qf_neg, qf_neg, qf_conj, qf_neg]
  apply qf_congr
  · apply imp_trans_rule _ not_not_elim
    apply contrapose
    exact and_intro_under (contrapose or_left) (contrapose or_right)
  · apply or_elim_imp
    · exact imp_swap_rule (imp_trans_rule and_left imp_refl)
    · exact imp_swap_rule (imp_trans_rule and_right imp_refl)

private theorem interp_qf (A : QFFormula k) : @interp r k P A.toFormula = @qf r k P A := by
  induction A with
  | false => exact qf_false.symm
  | eq => rfl
  | imp A B ihA ihB => simp only [QFFormula.toFormula, interp, ihA, ihB, qf_imp]
  | and A B ihA ihB => simp only [QFFormula.toFormula, interp, ihA, ihB, qf_conj]
  | or A B ihA ihB => simp only [QFFormula.toFormula, interp, ihA, ihB, qf_disj]

private def Stable (P : QFFormula (r + 1)) (p : Pred r k) : Prop :=
  ∀ {n} {Γ : World r n} {v : Val k n}, neg P (neg P p) Γ v → p Γ v

private theorem qf_stable (A : QFFormula k) : Stable P (qf P A) := by
  intro n Γ v h
  rw [qf_neg, qf_neg] at h
  exact qf_transport not_not_elim h

private theorem interp_qf_sound {A : QFFormula k} (h : QFProof A)
    (Γ : World r n) (v : Val k n) : interp P A.toFormula Γ v := by
  rw [interp_qf]
  exact ⟨0, imp_trans_rule (weaken (QFProof.subst (v := v) h)) or_left⟩

private theorem neg_monotone (p : Pred r k) : Monotone (neg P p) := imp_monotone _ _

private theorem bot_stable : Stable P (bot P : Pred r k) := by
  rw [← qf_false]
  exact qf_stable .false

private theorem imp_stable {p q : Pred r k} (hp : Monotone p) (hq : Stable P q) :
    Stable P (imp p q) := by
  intro n Γ v h m Δ w he ha
  apply hq
  intro l Θ u he' hnq
  have hh : neg P (neg P (imp p q)) Δ (act v w) :=
    neg_monotone (neg P (imp p q)) he h
  have hhh : neg P (neg P (imp p q)) Θ (act (act v w) u) :=
    neg_monotone (neg P (imp p q)) he' hh
  apply imp_elim hhh
  intro j Ξ z he'' hi
  have ha' := hp he' ha
  have ha'' := hp he'' ha'
  have hq' := imp_elim hi ha''
  have hnq' : neg P q Ξ (act (act (act v w) u) z) := neg_monotone q he'' hnq
  exact imp_elim hnq' hq'

private theorem conj_stable {p q : Pred r k} (hp : Stable P p) (hq : Stable P q) :
    Stable P (conj p q) := by
  intro n Γ v h
  constructor
  · apply hp
    intro m Δ w he hn
    have hh : neg P (neg P (conj p q)) Δ (act v w) :=
      neg_monotone (neg P (conj p q)) he h
    apply imp_elim hh
    intro l Θ u he' ha
    exact imp_elim (neg_monotone p he' hn) ha.1
  · apply hq
    intro m Δ w he hn
    have hh : neg P (neg P (conj p q)) Δ (act v w) :=
      neg_monotone (neg P (conj p q)) he h
    apply imp_elim hh
    intro l Θ u he' ha
    exact imp_elim (neg_monotone q he' hn) ha.2

private theorem all_elim {p : Pred r (k + 1)} {Γ : World r n} {v : Val k n}
    (h : all p Γ v) (t : Term n) : p Γ (Fin.cases t v) := by
  simpa only [act_id] using h Γ Term.var (ext_id Γ) t

private theorem all_stable {p : Pred r (k + 1)} (hp : Stable P p) : Stable P (all p) := by
  intro n Γ v h m Δ w he t
  apply hp
  intro l Θ u he' hn
  have hh : neg P (neg P (all p)) Δ (act v w) :=
    neg_monotone (neg P (all p)) he h
  have hhh : neg P (neg P (all p)) Θ (act (act v w) u) :=
    neg_monotone (neg P (all p)) he' hh
  apply imp_elim hhh
  intro j Ξ z he'' ha
  have hn' : neg P p Ξ (act (act (Fin.cases t (act v w)) u) z) :=
    neg_monotone p he'' hn
  have ht := all_elim ha ((t.subst u).subst z)
  apply imp_elim hn'
  simpa only [act_cons] using ht

private theorem interp_stable (A : Formula k) : Stable P (interp P A) := by
  induction A with
  | false => exact bot_stable
  | eq s t => exact qf_stable _
  | imp A B _ ihB => exact imp_stable (interp_monotone A) ihB
  | and A B ihA ihB => exact conj_stable ihA ihB
  | or A B =>
    exact imp_stable (conj_monotone (neg_monotone _) (neg_monotone _)) bot_stable
  | all A ih => exact all_stable ih
  | ex A => exact imp_stable (all_monotone _) bot_stable

private theorem interp_subst (A : Formula k) (σ : Val k l) :
    @interp r l P (A.subst σ) = fun {n} Γ (v : Val l n) => interp P A Γ (act σ v) := by
  induction A generalizing l with
  | false => rfl
  | eq s t =>
    funext n Γ v
    simp only [Formula.subst, interp, qf, QFFormula.subst, Term.subst_comp]
    rfl
  | imp A B ihA ihB =>
    funext n Γ v
    simp only [Formula.subst, interp, imp, ihA, ihB, act_assoc]
  | and A B ihA ihB =>
    funext n Γ v
    simp only [Formula.subst, interp, conj, ihA, ihB]
  | or A B ihA ihB =>
    funext n Γ v
    simp only [Formula.subst, interp, disj, neg, conj, imp, bot, ihA, ihB, act_assoc]
  | all A ih =>
    funext n Γ v
    simp only [Formula.subst, interp, all, ih, act_lift]
  | ex A ih =>
    funext n Γ v
    simp only [Formula.subst, interp, ex, neg, imp, bot, all, ih, act_cons,
      act_shift_cons, Term.subst, Fin.cases_zero, act_assoc]

private theorem interp_inst (A : Formula (k + 1)) (t : Term k)
    (Γ : World r n) (v : Val k n) :
    interp P (A.inst t) Γ v = interp P A Γ (Fin.cases (t.subst v) v) := by
  simp only [Formula.inst, interp_subst, act_cons, act_vars]

private theorem interp_shift (A : Formula k) (Γ : World r n) (v : Val (k + 1) n) :
    interp P A.shift Γ v = interp P A Γ (fun i => v i.succ) := by
  simp only [Formula.shift, interp_subst]
  rfl

private theorem interp_replace (A : Formula (k + 1)) (t : Term (k + 1))
    (Γ : World r n) (v : Val (k + 1) n) :
    interp P (A.replace t) Γ v = interp P A Γ (Fin.cases (t.subst v) (fun i => v i.succ)) := by
  simp only [Formula.replace, interp_subst, act_cons]
  rfl

private theorem qf_induction (A : QFFormula (k + 1)) (Γ : World r n) (v : Val k n)
    (hb : interp P (A.toFormula.inst 0) Γ v)
    (hs : all (interp P (.imp A.toFormula
      (A.toFormula.replace (.succ (.var 0))))) Γ v) (t : Term n) :
    interp P A.toFormula Γ (Fin.cases t v) := by
  have hb' : ∃ b, QFProof (Γ.ctx ⇒ A.subst (Fin.cases 0 v) ⊔
      P.subst (Fin.cases b Γ.env)) := by
    simpa only [interp_inst, Term.subst_zero, interp_qf, qf] using hb
  obtain ⟨b, hb'⟩ := hb'
  let Δ : World r (n + 1) := ⟨Γ.ctx.shift, fun i => (Γ.env i).shift⟩
  have he : Ext Γ Δ (Term.var ∘ Fin.succ) := ⟨imp_refl, rfl⟩
  have hs' : interp P (.imp A.toFormula (A.toFormula.replace (.succ (.var 0))))
      Δ (Fin.cases (.var 0) (act v (Term.var ∘ Fin.succ))) :=
    hs Δ (Term.var ∘ Fin.succ) he (.var 0)
  have hr : @interp r (k + 1) P (A.toFormula.replace (.succ (.var 0))) =
      @qf r (k + 1) P (A.replace (.succ (.var 0))) := by
    funext m Θ u
    simp only [interp_replace, interp_qf, qf, QFFormula.subst_replace]
  have hc : ∃ s, QFProof (Γ.ctx.shift ⇒
      (A ⇒ A.replace (.succ (.var 0))).subst
        (Fin.cases (.var 0) (act v (Term.var ∘ Fin.succ))) ⊔
      P.subst (Fin.cases s Δ.env)) := by
    simpa only [interp, interp_qf, hr, qf_imp, qf] using @hs'
  obtain ⟨s, hc⟩ := hc
  let A' := A.subst (Fin.cases (.var 0) (fun i => (v i).shift))
  let P' := P.subst (Fin.cases (.var 0) (fun i => (Γ.env i).shift))
  have hb'' : QFProof (Γ.ctx ⇒ A'.inst 0 ⊔ P'.inst b) := by
    simpa only [A', P', QFFormula.inst_subst] using hb'
  have hs'' : QFProof (Γ.ctx.shift ⇒ (A' ⇒ A'.replace (.succ (.var 0))) ⊔
      P'.subst (Fin.cases s (Term.var ∘ Fin.succ))) := by
    change QFProof (Γ.ctx.shift ⇒ (A' ⇒ A'.replace (.succ (.var 0))) ⊔ P'.replace s)
    simp only [A', P', QFFormula.replace_subst]
    simp only [QFFormula.subst, QFFormula.subst_replace, Term.subst_succ, Term.subst,
      Fin.cases_zero, Fin.cases_succ] at hc
    exact hc
  obtain ⟨u, hu⟩ := iteration A' P' Γ.ctx b s hb'' hs'' t
  rw [interp_qf]
  refine ⟨u, ?_⟩
  simpa only [A', P', QFFormula.inst_subst] using hu

private theorem contra_elim {p q : Pred r k} {Γ : World r n} {v : Val k n}
    (h : imp p q Γ v) (hn : neg P q Γ v) : neg P p Γ v := by
  intro m Δ w he hp
  exact imp_elim (neg_monotone q he hn) (imp_elim (imp_monotone p q he h) hp)

private theorem disj_elim {p q R : Pred r k} (hr : Stable P R)
    {Γ : World r n} {v : Val k n} (hp : imp p R Γ v) (hq : imp q R Γ v)
    (h : disj P p q Γ v) : R Γ v := by
  apply hr
  intro m Δ w he hn
  apply imp_elim (neg_monotone (conj (neg P p) (neg P q)) he h)
  exact ⟨contra_elim (imp_monotone p R he hp) hn,
    contra_elim (imp_monotone q R he hq) hn⟩

private theorem proof_sound {A : Formula k} (h : Proof A) :
    ∀ {n} (Γ : World r n) (v : Val k n), interp P A Γ v := by
  induction h with
  | @imp_imp_self k A B =>
    intro n Γ v m Δ w he ha l Θ u he' _
    exact interp_monotone A he' ha
  | @imp_distrib k A B C =>
    intro n Γ v m Δ w he habc l Θ u he' hab j Ξ z he'' ha
    have habc' : interp P (.imp A (.imp B C)) Ξ (act (act (act v w) u) z) := by
      simpa only [interp, imp, act_assoc] using
        @interp_monotone _ P _ (.imp A (.imp B C)) _ _ _ _ _ _ (ext_comp he' he'') habc
    have hbc : interp P (.imp B C) Ξ (act (act (act v w) u) z) := imp_elim habc' ha
    exact imp_elim hbc (imp_elim (interp_monotone (.imp A B) he'' hab) ha)
  | @imp_contra k A B =>
    intro n Γ v m Δ w he h l Θ u he' hb
    apply interp_stable A
    intro j Ξ z he'' hna
    have h' : interp P (.imp A.neg B.neg) Ξ (act (act (act v w) u) z) := by
      simpa only [interp, imp, act_assoc] using
        @interp_monotone _ P _ (.imp A.neg B.neg) _ _ _ _ _ _ (ext_comp he' he'') h
    have hnb : interp P B.neg Ξ (act (act (act v w) u) z) := imp_elim h' hna
    exact imp_elim hnb (interp_monotone B he'' hb)
  | @and_intro k A B =>
    intro n Γ v m Δ w he ha l Θ u he' hb
    exact ⟨interp_monotone A he' ha, hb⟩
  | and_left => intro n Γ v m Δ w he h; exact h.1
  | and_right => intro n Γ v m Δ w he h; exact h.2
  | @or_left k A B =>
    intro n Γ v m Δ w he ha l Θ u he' hn
    exact imp_elim hn.1 (interp_monotone A he' ha)
  | @or_right k A B =>
    intro n Γ v m Δ w he hb l Θ u he' hn
    exact imp_elim hn.2 (interp_monotone B he' hb)
  | @or_elim k A B C =>
    intro n Γ v m Δ w he hac l Θ u he' hbc j Ξ z he'' h
    have hac' : interp P (.imp A C) Ξ (act (act (act v w) u) z) := by
      simpa only [interp, imp, act_assoc] using
        @interp_monotone _ P _ (.imp A C) _ _ _ _ _ _ (ext_comp he' he'') hac
    exact disj_elim (interp_stable C) hac' (interp_monotone (.imp B C) he'' hbc) h
  | mp _ _ ih₁ ih₂ =>
    intro n Γ v
    exact imp_elim (ih₁ Γ v) (ih₂ Γ v)
  | @forall_elim k A t =>
    intro n Γ v m Δ w he h
    rw [interp_inst]
    exact all_elim h (t.subst (act v w))
  | @forall_imp k A B =>
    intro n Γ v m Δ w he h l Θ u he' ha j Ξ z he'' t
    have hab : interp P (.imp A.shift B) Ξ (Fin.cases t (act (act v w) (act u z))) :=
      h Ξ (act u z) (ext_comp he' he'') t
    simp only [act_assoc] at hab ⊢
    apply imp_elim hab
    rw [interp_shift]
    simpa only [Fin.cases_succ, act_assoc] using interp_monotone A he'' ha
  | @exists_intro k A t =>
    intro n Γ v m Δ w he ha l Θ u he' hn
    have ha' := interp_monotone (A.inst t) he' ha
    simp only [interp_inst] at ha'
    exact imp_elim (p := interp P A) (q := bot P)
      (all_elim hn (t.subst (act (act v w) u))) ha'
  | @exists_elim k A B =>
    intro n Γ v m Δ w he h l Θ u he' hex
    apply interp_stable B
    intro j Ξ z he'' hnb
    apply imp_elim (interp_monotone (.ex A) he'' hex)
    intro d Ω s he3 t e Λ r he4 ha
    have hab : interp P (.imp A B.shift) Λ
        (Fin.cases (t.subst r) (act (act v w) (act (act (act u z) s) r))) :=
      h Λ (act (act (act u z) s) r)
        (ext_comp (ext_comp (ext_comp he' he'') he3) he4) (t.subst r)
    have hb := imp_elim hab (by simpa only [act_assoc, act_cons] using ha)
    rw [interp_shift] at hb
    apply imp_elim (neg_monotone (interp P B) (ext_comp he3 he4) hnb)
    simpa only [act_assoc, Fin.cases_succ] using hb
  | gen _ ih =>
    intro n Γ v m Δ w he t
    exact ih Δ (Fin.cases t (act v w))
  | @eq_refl k t =>
    intro n Γ v
    exact interp_qf_sound (A := .eq t t) .eq_refl Γ v
  | @eq_symm k s t =>
    intro n Γ v
    exact interp_qf_sound (A := .imp (.eq s t) (.eq t s)) .eq_symm Γ v
  | @eq_trans k s t u =>
    intro n Γ v
    exact interp_qf_sound (A := .imp (.eq s t) (.imp (.eq t u) (.eq s u))) .eq_trans Γ v
  | @eq_congr_ith k m f u i t =>
    intro n Γ v
    exact interp_qf_sound (A := .imp (.eq (u i) t)
      (.eq (.app f u) (.app f (fun j => if j = i then t else u j)))) .eq_congr_ith Γ v
  | @succ_ne_zero k t =>
    intro n Γ v
    exact interp_qf_sound (A := ∼ (.eq (.succ t) 0)) .succ_ne_zero Γ v
  | @succ_inj k s t =>
    intro n Γ v
    exact interp_qf_sound (A := .imp (.eq (.succ s) (.succ t)) (.eq s t)) .succ_inj Γ v
  | @app_proj k m i u =>
    intro n Γ v
    exact interp_qf_sound (A := .eq (.app (.proj i) u) (u i)) .app_proj Γ v
  | @app_comp k m l f g u =>
    intro n Γ v
    exact interp_qf_sound (A := .eq (.app (.comp f g) u)
      (.app f (fun i => .app (g i) u))) .app_comp Γ v
  | @app_prec_zero k m f g u =>
    intro n Γ v
    exact interp_qf_sound (A := .eq (.app (.prec f g) (Fin.cases 0 u)) (.app f u))
      .app_prec_zero Γ v
  | @app_prec_succ k m f g t u =>
    intro n Γ v
    exact interp_qf_sound (A := .eq (.app (.prec f g) (Fin.cases (.succ t) u))
      (.app g (Fin.cases t (Fin.cases (.app (.prec f g) (Fin.cases t u)) u))))
      .app_prec_succ Γ v
  | @induction k A hA =>
    obtain ⟨B, rfl⟩ := Formula.quantifierFree_image hA
    intro n Γ v m Δ w he hb l Θ u he' hs j Ξ z he'' t
    apply qf_induction B Ξ (act (act (act v w) u) z) ?_ ?_ t
    · have hh := interp_monotone _ (ext_comp he' he'') hb
      simpa only [act_assoc] using hh
    · exact all_monotone _ he'' hs

private theorem extract_term (P : QFFormula (n + 1)) (h : Proof (.ex P.toFormula)) :
    ∃ t : Term n, QFProof (P.inst t) := by
  let Γ : World n n := ⟨⊤, Term.var⟩
  have hh : ex P (interp P P.toFormula) Γ Term.var := proof_sound h Γ Term.var
  have hn : all (neg P (interp P P.toFormula)) Γ Term.var := by
    intro m Δ w he t l Θ u he' ht
    rw [interp_qf] at ht
    obtain ⟨s, hs⟩ := ht
    have heq : Θ.env = act (act Term.var w) u := by
      rw [he'.2, he.2]
    have hs' : QFProof (Θ.ctx ⇒
        P.subst (Fin.cases (t.subst u) Θ.env) ⊔ P.subst (Fin.cases s Θ.env)) := by
      rw [heq]
      simpa only [act_cons, heq] using hs
    exact ⟨merge P Θ.env (t.subst u) s,
      imp_trans_rule hs' (merge_correct P Θ.env (t.subst u) s)⟩
  obtain ⟨t, ht⟩ := imp_elim hh hn
  exact ⟨t, mp ht imp_refl⟩

end Forcing

end Witness

/-- From a first-order PRA proof of `∃' P.toFormula`, extract a primitive recursive witness
`f : Primrec n` and a quantifier-free PRA proof of `P.inst (.app f Term.var)`. Variable `0` of `P`
is the existential variable, and the remaining `n` variables are free parameters. -/
public theorem exists_primrec_witness {P : QFFormula (n + 1)}
    (h : Proof (.ex P.toFormula)) :
    ∃ f : Primrec n, QFProof (P.inst (.app f Term.var)) :=
  qf_witness_iff_primrec.mp (Witness.Forcing.extract_term P h)

/-- If first-order PRA proves `∀' ∃' P.toFormula`, then quantifier-free PRA proves
`P.inst (.app f Term.var)` for some unary primitive recursive expression `f`. In `P`, variable
`0` is the existential variable and variable `1` is the universal variable. -/
public theorem forall_exists_primrec_witness {P : QFFormula 2}
    (h : Proof (.all (.ex P.toFormula))) :
    ∃ f : Primrec 1, QFProof (P.inst (.app f Term.var)) :=
  exists_primrec_witness (Proof.forall_body h)

end PRA
