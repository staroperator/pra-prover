module

public import PRAProver.Surface.Command

/-!
# Logic in PRA

Derived propositional, equality, and quantifier reasoning in the PRA language, together with
the predicates `Subsingleton` and `ExistsUnique` for unique existence on `Nat`.
-/

@[expose] public section

pra

theorem imp_id {P : Prop} : P → P :=
  fun h => h

theorem imp_trans {P Q R : Prop} : (P → Q) → (Q → R) → P → R :=
  fun h₁ h₂ h => h₂ (h₁ h)

theorem iff_refl {P : Prop} : P ↔ P :=
  (imp_id, imp_id)

theorem iff_trans {P Q R : Prop} : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
  fun h₁ h₂ => (imp_trans (and_left h₁) (and_left h₂), imp_trans (and_right h₂) (and_right h₁))

theorem and_symm {P Q : Prop} : P ∧ Q → Q ∧ P :=
  fun (h₁, h₂) => (h₂, h₁)

theorem and_comm {P Q : Prop} : P ∧ Q ↔ Q ∧ P :=
  (and_symm, and_symm)

theorem and_assoc {P Q R : Prop} : P ∧ Q ∧ R ↔ (P ∧ Q) ∧ R :=
  (fun (h₁, h₂, h₃) => ((h₁, h₂), h₃), fun ((h₁, h₂), h₃) => (h₁, h₂, h₃))

theorem and_idem {P : Prop} : P ∧ P ↔ P :=
  (fun (h, _) => h, fun h => (h, h))

theorem and_congr {P Q R S : Prop} : (P ↔ R) → (Q ↔ S) → (P ∧ Q ↔ R ∧ S) :=
  fun h₁ h₂ => (fun (hP, hQ) => (and_left h₁ hP, and_left h₂ hQ),
    fun (hR, hS) => (and_right h₁ hR, and_right h₂ hS))

theorem or_symm {P Q : Prop} : P ∨ Q → Q ∨ P :=
  fun h => or_elim h (fun hP => or_right hP) fun hQ => or_left hQ

theorem or_comm {P Q : Prop} : P ∨ Q ↔ Q ∨ P :=
  (or_symm, or_symm)

theorem or_assoc {P Q R : Prop} : P ∨ Q ∨ R ↔ (P ∨ Q) ∨ R :=
  (fun h => or_elim h (fun hP => or_left (or_left hP))
      fun h => or_elim h (fun hQ => or_left (or_right hQ)) fun hR => or_right hR,
    fun h => or_elim h (fun h => or_elim h (fun hP => or_left hP) fun hQ => or_right (or_left hQ))
      fun hR => or_right (or_right hR))

theorem or_idem {P : Prop} : P ∨ P ↔ P :=
  (fun h => or_elim h imp_id imp_id, fun h => or_left h)

theorem or_congr {P Q R S : Prop} : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) :=
  fun h₁ h₂ =>
    (fun h => or_elim h (imp_trans (and_left h₁) or_left) (imp_trans (and_left h₂) or_right),
      fun h => or_elim h (imp_trans (and_right h₁) or_left) (imp_trans (and_right h₂) or_right))

/-- Eliminate double negation using excluded middle. -/
theorem dne (P : Prop) : ¬ ¬ P → P :=
  fun h => or_elim (lem P) imp_id fun h' => false_elim (h h')

theorem eq_symm : ∀ {x y}, x = y → y = x :=
  fun x y h => eq_subst (fun z => z = x) h rfl

theorem eq_comm : ∀ {x y}, x = y ↔ y = x :=
  fun x y => (eq_symm, eq_symm)

theorem eq_trans : ∀ {x y z}, x = y → y = z → x = z :=
  fun x y z h₁ h₂ => eq_subst (fun a => x = a) h₂ h₁

theorem eq_congr (f : Nat → Nat) : ∀ {x y}, x = y → f x = f y :=
  fun x y h => eq_subst (fun z => f x = f z) h rfl

theorem eq_congr₂ (f : Nat → Nat → Nat) : ∀ {a b c d}, a = c → b = d → f a b = f c d :=
  fun a b c d h₁ h₂ => eq_trans (eq_congr (fun x => f x b) h₁) (eq_congr (f c) h₂)

theorem eq_congr₃ (f : Nat → Nat → Nat → Nat) :
    ∀ {a b c d e g}, a = d → b = e → c = g → f a b c = f d e g :=
  fun a b c d e g h₁ h₂ h₃ => eq_trans (eq_congr₂ (fun x y => f x y c) h₁ h₂) (eq_congr (f d e) h₃)

theorem forall_congr {P Q : Nat → Prop} : (∀ x, P x ↔ Q x) → ((∀ x, P x) ↔ (∀ x, Q x)) :=
  fun h => (fun hP x => and_left (h x) (hP x), fun hQ x => and_right (h x) (hQ x))

theorem exists_congr {P Q : Nat → Prop} : (∀ x, P x ↔ Q x) → ((∃ x, P x) ↔ (∃ x, Q x)) :=
  fun h => (fun (x, hx) => (x, and_left (h x) hx), fun (x, hx) => (x, and_right (h x) hx))

/-- At most one natural number satisfies `P`. -/
def Subsingleton (P : Nat → Prop) : Prop :=
  ∀ x y, P x → P y → x = y

/-- Exactly one natural number satisfies `P`. -/
def ExistsUnique (P : Nat → Prop) : Prop :=
  ∃ x, P x ∧ ∀ y, P y → y = x

theorem existsUnique_iff_exists_and_subsingleton {P : Nat → Prop} :
    ExistsUnique P ↔ (∃ x, P x) ∧ Subsingleton P :=
  (fun (x, h₁, h₂) => ((x, h₁), fun y z hy hz => eq_trans (h₂ y hy) (eq_symm (h₂ z hz))),
    fun ((x, h₁), h₂) => (x, h₁, fun y hy => eq_symm (h₂ x y h₁ hy)))

end
