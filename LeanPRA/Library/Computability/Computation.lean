module

public import LeanPRA.Library.Computability.Code
public import LeanPRA.Library.Nat.Sequence

/-!
# Primitive-recursive computations

Finite computation trees describe the evaluation of unary programs, with numerical pairing
supplying multiple arguments.

- `Computation.node` stores a program, its input and output, and its child computations.
- `Computation.isValid` checks a tree by course-of-values recursion on smaller children;
  `Computation.Evaluates e x y t` states its program, input, and output as a
  quantifier-free formula.
- `Computation.constTrace`, `Computation.idTrace`, `Computation.compTrace`,
  `Computation.pairTrace`, and `Computation.recTrace` build trees. Their correctness proofs use
  explicit builders and quantifier-free induction.
- `Computation.recTraceAt`, `Computation.recValue`, `Computation.recBaseTrace`, and
  `Computation.recStepTrace` extract a recursion's computations and intermediate outputs.
- `Computes e x y` asserts existence of a checked tree, and `Primrec f` asserts that one program
  computes `f` on every input. `Primrec.of_evaluates` supplies such a program from a tree builder.
-/

@[expose] public section

pra

namespace Primrec

namespace Computation

/-! ## Tree encoding -/

/-- `node e x y p q` stores program code `e`, input `x`, output `y`, and child trees `p`, `q`.
Unused children are zero. The encoding is `S (pair (pair e (pair x y)) (pair p q))`. -/
def node : Nat → Nat → Nat → Nat → Nat → Nat := fun e x y p q =>
  S (pair (pair e (pair x y)) (pair p q))

/-- `program t` reads the program code at the root of computation tree `t`. -/
def program : Nat → Nat := fun t => unpairLeft (unpairLeft (pred t))

/-- `input t` reads the numerical input at the root of computation tree `t`. -/
def input : Nat → Nat := fun t => unpairLeft (unpairRight (unpairLeft (pred t)))

/-- `output t` reads the numerical output at the root of computation tree `t`. -/
def output : Nat → Nat := fun t => unpairRight (unpairRight (unpairLeft (pred t)))

/-- `childLeft t` reads the first child computation, or zero when that child is unused. -/
def childLeft : Nat → Nat := fun t => unpairLeft (unpairRight (pred t))

/-- `childRight t` reads the second child computation, or zero when that child is unused. -/
def childRight : Nat → Nat := fun t => unpairRight (unpairRight (pred t))

theorem program_node : ∀ e x y p q, program (node e x y p q) = e := by
  intro e x y p q
  rw [program, node, pred_succ, unpairLeft_pair, unpairLeft_pair]

theorem input_node : ∀ e x y p q, input (node e x y p q) = x := by
  intro e x y p q
  rw [input, node, pred_succ, unpairLeft_pair, unpairRight_pair, unpairLeft_pair]

theorem output_node : ∀ e x y p q, output (node e x y p q) = y := by
  intro e x y p q
  rw [output, node, pred_succ, unpairLeft_pair, unpairRight_pair, unpairRight_pair]

theorem childLeft_node : ∀ e x y p q, childLeft (node e x y p q) = p := by
  intro e x y p q
  rw [childLeft, node, pred_succ, unpairRight_pair, unpairLeft_pair]

theorem childRight_node : ∀ e x y p q, childRight (node e x y p q) = q := by
  intro e x y p q
  rw [childRight, node, pred_succ, unpairRight_pair, unpairRight_pair]

theorem childLeft_lt_node : ∀ e x y p q, p < node e x y p q := by
  intro e x y p q
  apply and_right (lt_succ p (pair (pair e (pair x y)) (pair p q)))
  exact le_trans _ _ _ (left_le_pair p q) (right_le_pair (pair e (pair x y)) (pair p q))

theorem childRight_lt_node : ∀ e x y p q, q < node e x y p q := by
  intro e x y p q
  apply and_right (lt_succ q (pair (pair e (pair x y)) (pair p q)))
  exact le_trans _ _ _ (right_le_pair p q) (right_le_pair (pair e (pair x y)) (pair p q))

theorem node_eta : ∀ t, ¬ t = 0 →
    node (program t) (input t) (output t) (childLeft t) (childRight t) = t := by
  intro t ht
  rw [node, program, input, output, childLeft, childRight,
    pair_unpair, pair_unpair, pair_unpair, pair_unpair]
  exact succ_pred t ht

theorem childLeft_lt : ∀ t, ¬ t = 0 → childLeft t < t := by
  intro t ht
  have h := childLeft_lt_node (program t) (input t) (output t) (childLeft t) (childRight t)
  rw [node_eta t ht] at h
  exact h

theorem childRight_lt : ∀ t, ¬ t = 0 → childRight t < t := by
  intro t ht
  have h := childRight_lt_node (program t) (input t) (output t) (childLeft t) (childRight t)
  rw [node_eta t ht] at h
  exact h

/-! ## Checking computation trees -/

/-- `checkNode e x y p q hp hq` checks one evaluation rule. The numbers `hp` and `hq` are
validation results for the child computations; unused children must have code zero. -/
def checkNode : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat := fun e x y p q hp hq =>
  let k := Code.tag e;
  let args := Code.args e;
  let f := unpairLeft args;
  let g := unpairRight args;
  let px := band hp (eqb (input p) x);
  let qy := band hq (eqb (output q) y);
  let leaf := band (eqb args 0) (band (eqb p 0) (eqb q 0));
  ite (eqb k 0) (band leaf (eqb y 0))
    (ite (eqb k 1) (band leaf (eqb y (S x)))
    (ite (eqb k 2) (band leaf (eqb y (unpairLeft x)))
    (ite (eqb k 3) (band leaf (eqb y (unpairRight x)))
    (ite (eqb k 4)
      (band px (band hq (band (eqb (program p) f) (band (eqb (program q) g)
        (band (eqb (input q) x) (eqb y (pair (output p) (output q))))))))
    (ite (eqb k 5)
      (band px (band qy (band (eqb (program p) g)
        (band (eqb (program q) f) (eqb (input q) (output p))))))
    (ite (eqb k 6)
      (ite (unpairRight x)
        (band hp (band qy (band (eqb (program p) e) (band (eqb (program q) g)
          (band (eqb (input p) (pair (unpairLeft x) (pred (unpairRight x))))
            (eqb (input q)
              (pair (unpairLeft x) (pair (pred (unpairRight x)) (output p)))))))))
        (band hp (band (eqb q 0) (band (eqb (program p) f)
          (band (eqb (input p) (unpairLeft x)) (eqb (output p) y))))))
    0))))))

/-- `isValid t` checks the complete computation tree `t`. Zero is invalid. -/
def isValid : Nat → Nat := covrec (fun t history => ite t
  (checkNode (program t) (input t) (output t) (childLeft t) (childRight t)
    (Sequence.rget history (childLeft t)) (Sequence.rget history (childRight t))) 0)

theorem isValid_zero : isValid 0 = 0 := rfl

theorem isValid_node : ∀ e x y p q,
    isValid (node e x y p q) = checkNode e x y p q (isValid p) (isValid q) := by
  intro e x y p q
  rw [isValid, covrec, program_node, input_node, output_node, childLeft_node, childRight_node]
  rw [ite_of_ne_zero _ _ _ (succ_ne_zero (pair (pair e (pair x y)) (pair p q)))]
  rw [Sequence.rget_generate _ p (node e x y p q) (childLeft_lt_node e x y p q),
    Sequence.rget_generate _ q (node e x y p q) (childRight_lt_node e x y p q)]
  rfl

theorem ite_isBool : ∀ c x y, IsBool x → IsBool y → IsBool (ite c x y) := ite_bool

theorem checkNode_bool : ∀ e x y p q hp hq, IsBool (checkNode e x y p q hp hq) := by
  intro e x y p q hp hq
  rw [checkNode]
  apply ite_isBool
  · exact band_bool _ _
  · apply ite_isBool
    · exact band_bool _ _
    · apply ite_isBool
      · exact band_bool _ _
      · apply ite_isBool
        · exact band_bool _ _
        · apply ite_isBool
          · exact band_bool _ _
          · apply ite_isBool
            · exact band_bool _ _
            · apply ite_isBool
              · apply ite_isBool
                · exact band_bool _ _
                · exact band_bool _ _
              · left
                rfl

theorem isValid_bool : ∀ t, IsBool (isValid t) := by
  intro t
  rw [isValid, covrec]
  apply ite_isBool
  · exact checkNode_bool _ _ _ _ _ _ _
  · left
    rfl

theorem ne_zero_of_isValid : ∀ t, isValid t = 1 → ¬ t = 0 := by
  intro t h hz
  rw [hz, isValid_zero] at h
  exact zero_ne_succ 0 h

/-! ## Evaluation rules -/

/-- `Evaluates e x y t` states that tree code `t` is a valid computation of program `e` from
input `x` to output `y`. All four conditions are quantifier-free. -/
def Evaluates : Nat → Nat → Nat → Nat → QFProp := fun e x y t =>
  isValid t = 1 ∧ program t = e ∧ input t = x ∧ output t = y

theorem evaluates_node : ∀ e x y p q,
    checkNode e x y p q (isValid p) (isValid q) = 1 →
    Evaluates e x y (node e x y p q) := by
  intro e x y p q h
  exact (eq_trans (isValid_node e x y p q) h, program_node e x y p q,
    input_node e x y p q, output_node e x y p q)

theorem evaluates_zero : ∀ x,
    Evaluates Code.zero x (0) (node Code.zero x (0) 0 0) := by
  intro x
  apply evaluates_node
  rw [Code.zero, checkNode]
  change isPos (eqb (0) (0)) = 1
  repeat rw [eqb_self]
  rfl

theorem evaluates_succ : ∀ x,
    Evaluates Code.succ x (S x) (node Code.succ x (S x) 0 0) := by
  intro x
  apply evaluates_node
  rw [Code.succ, checkNode]
  change isPos (eqb (S x) (S x)) = 1
  repeat rw [eqb_self]
  rfl

theorem checkNode_left : ∀ x y hp hq,
    checkNode Code.left x y 0 0 hp hq = isPos (eqb y (unpairLeft x)) :=
  fun x y hp hq => rfl

theorem evaluates_left : ∀ x,
    Evaluates Code.left x (unpairLeft x) (node Code.left x (unpairLeft x) 0 0) := by
  intro x
  apply evaluates_node
  rw [checkNode_left, eqb_self, isPos_succ]

theorem checkNode_right : ∀ x y hp hq,
    checkNode Code.right x y 0 0 hp hq = isPos (eqb y (unpairRight x)) :=
  fun x y hp hq => rfl

theorem evaluates_right : ∀ x,
    Evaluates Code.right x (unpairRight x) (node Code.right x (unpairRight x) 0 0) := by
  intro x
  apply evaluates_node
  rw [checkNode_right, eqb_self, isPos_succ]

theorem evaluates_pair : ∀ f g x y z p q,
    Evaluates f x y p → Evaluates g x z q →
    Evaluates (Code.pair f g) x (pair y z) (node (Code.pair f g) x (pair y z) p q) := by
  intro f g x y z p q hp hq
  rcases hp with (hp, hpe, hpx, hpy)
  rcases hq with (hq, hqe, hqx, hqy)
  apply evaluates_node
  rw [Code.pair, checkNode, Code.tag_binary 0 f g rfl, Code.args_binary 0 f g rfl,
    unpairLeft_pair, unpairRight_pair]
  rw [hp, hpe, hpx, hpy, hq, hqe, hqx, hqy]
  change band (band 1 (eqb x x)) (band 1 (band (eqb f f)
    (band (eqb g g) (band (eqb x x) (eqb (pair y z) (pair y z)))))) = 1
  repeat rw [eqb_self]
  rfl

theorem evaluates_comp : ∀ f g x y z p q,
    Evaluates g x y p → Evaluates f y z q →
    Evaluates (Code.comp f g) x z (node (Code.comp f g) x z p q) := by
  intro f g x y z p q hp hq
  rcases hp with (hp, hpe, hpx, hpy)
  rcases hq with (hq, hqe, hqx, hqy)
  apply evaluates_node
  rw [Code.comp, checkNode, Code.tag_binary 1 f g rfl, Code.args_binary 1 f g rfl,
    unpairLeft_pair, unpairRight_pair]
  rw [hp, hpe, hpx, hpy, hq, hqe, hqx, hqy]
  change band (band 1 (eqb x x)) (band (band 1 (eqb z z))
    (band (eqb g g) (band (eqb f f) (eqb y y)))) = 1
  repeat rw [eqb_self]
  rfl

theorem evaluates_rec_zero : ∀ f g x y p,
    Evaluates f x y p →
    Evaluates (Code.rec f g) (pair x 0) y (node (Code.rec f g) (pair x 0) y p 0) := by
  intro f g x y p hp
  rcases hp with (hp, hpe, hpx, hpy)
  apply evaluates_node
  rw [Code.rec, checkNode, Code.tag_binary 2 f g rfl, Code.args_binary 2 f g rfl,
    unpairLeft_pair, unpairRight_pair,
    unpairRight_pair, unpairLeft_pair]
  rw [hp, hpe, hpx, hpy]
  change band 1 (band (eqb 0 0) (band (eqb f f) (band (eqb x x) (eqb y y)))) = 1
  repeat rw [eqb_self]
  rfl

theorem evaluates_rec_succ : ∀ f g x n y z p q,
    Evaluates (Code.rec f g) (pair x n) y p →
    Evaluates g (pair x (pair n y)) z q →
    Evaluates (Code.rec f g) (pair x (S n)) z (node (Code.rec f g) (pair x (S n)) z p q) := by
  intro f g x n y z p q hp hq
  rcases hp with (hp, hpe, hpx, hpy)
  rcases hq with (hq, hqe, hqx, hqy)
  apply evaluates_node
  rw [Code.rec, checkNode, Code.tag_binary 2 f g rfl, Code.args_binary 2 f g rfl,
    unpairLeft_pair, unpairRight_pair,
    unpairRight_pair, unpairLeft_pair]
  rw [hp, hpe, hpx, hpy, hq, hqe, hqx, hqy]
  change band 1 (band (band 1 (eqb z z)) (band (eqb (Code.rec f g) (Code.rec f g))
    (band (eqb g g) (band (eqb (pair x n) (pair x n))
      (eqb (pair x (pair n y)) (pair x (pair n y))))))) = 1
  repeat rw [eqb_self]
  rfl

/-! ## Constructing computation trees -/

/-- `constTrace n x` constructs the computation of the constant program `Code.const n` at `x`. -/
def constTrace : Nat → Nat → Nat := fun n x =>
  primrec (node Code.zero x 0 0 0)
    (fun k t => node (Code.comp Code.succ (Code.const k)) x (S k) t
      (node Code.succ k (S k) 0 0)) n

theorem evaluates_const : ∀ n x, Evaluates (Code.const n) x n (constTrace n x) := by
  intro n x
  induction n with k ih
  · exact evaluates_zero x
  · exact evaluates_comp Code.succ (Code.const k) x k (S k) (constTrace k x)
      (node Code.succ k (S k) 0 0) ih (evaluates_succ k)

/-- `idTrace x` constructs the identity program's computation at `x`. -/
def idTrace : Nat → Nat := fun x => node Code.id x x
  (node Code.left x (unpairLeft x) 0 0) (node Code.right x (unpairRight x) 0 0)

theorem evaluates_id : ∀ x, Evaluates Code.id x x (idTrace x) := by
  intro x
  have h := evaluates_pair Code.left Code.right x (unpairLeft x) (unpairRight x)
    (node Code.left x (unpairLeft x) 0 0) (node Code.right x (unpairRight x) 0 0)
    (evaluates_left x) (evaluates_right x)
  rw [pair_unpair] at h
  exact h

/-- `recTrace base step baseTrace stepTrace f g x n` constructs a computation of `Code.rec f g`
from computations supplied by `baseTrace` and `stepTrace`. The step input is
`pair x (pair i previous)`, and the result is `primrec (base x) (step x) n`. -/
def recTrace (base : Nat → Nat) (step : Nat → Nat → Nat → Nat)
    (baseTrace : Nat → Nat) (stepTrace : Nat → Nat → Nat → Nat) :
    Nat → Nat → Nat → Nat → Nat := fun f g x n =>
  primrec (node (Code.rec f g) (pair x 0) (base x) (baseTrace x) 0)
    (fun i t => node (Code.rec f g) (pair x (S i))
      (step x i (primrec (base x) (step x) i)) t
      (stepTrace x i (primrec (base x) (step x) i))) n

/-- Correct computation trees for the base and step give a correct tree for primitive recursion.
The induction predicate is quantifier-free because all tree builders are explicit functions. -/
theorem evaluates_rec (base : Nat → Nat) (step : Nat → Nat → Nat → Nat)
    (baseTrace : Nat → Nat) (stepTrace : Nat → Nat → Nat → Nat) :
    ∀ f g, (∀ x, Evaluates f x (base x) (baseTrace x)) →
    (∀ x i y, Evaluates g (pair x (pair i y)) (step x i y) (stepTrace x i y)) →
    ∀ x n, Evaluates (Code.rec f g) (pair x n) (primrec (base x) (step x) n)
      (recTrace base step baseTrace stepTrace f g x n) := by
  intro f g hb hs x n
  induction n with i ih
  · exact evaluates_rec_zero f g x (base x) (baseTrace x) (hb x)
  · exact evaluates_rec_succ f g x i (primrec (base x) (step x) i)
      (step x i (primrec (base x) (step x) i))
      (recTrace base step baseTrace stepTrace f g x i)
      (stepTrace x i (primrec (base x) (step x) i)) ih
      (hs x i (primrec (base x) (step x) i))

theorem evaluates_congr : ∀ e x y z t,
    y = z → Evaluates e x y t → Evaluates e x z t := by
  intro e x y z t h ht
  rw [← h]
  exact ht

/-- `compTrace f g tf tg a b x` composes the computations `tg x` and `tf (g x)` of programs
`b` and `a`, respectively. -/
def compTrace (f g tf tg : Nat → Nat) : Nat → Nat → Nat → Nat := fun a b x =>
  node (Code.comp a b) x (f (g x)) (tg x) (tf (g x))

theorem evaluates_compTrace (f g tf tg : Nat → Nat) : ∀ a b,
    (∀ x, Evaluates a x (f x) (tf x)) → (∀ x, Evaluates b x (g x) (tg x)) →
    ∀ x, Evaluates (Code.comp a b) x (f (g x)) (compTrace f g tf tg a b x) := by
  intro a b hf hg x
  exact evaluates_comp a b x (g x) (f (g x)) (tg x) (tf (g x)) (hg x) (hf (g x))

/-- `pairTrace f g tf tg a b x` pairs the outputs of computations `tf x` and `tg x` of
programs `a` and `b`. -/
def pairTrace (f g tf tg : Nat → Nat) : Nat → Nat → Nat → Nat := fun a b x =>
  node (Code.pair a b) x (pair (f x) (g x)) (tf x) (tg x)

theorem evaluates_pairTrace (f g tf tg : Nat → Nat) : ∀ a b,
    (∀ x, Evaluates a x (f x) (tf x)) → (∀ x, Evaluates b x (g x) (tg x)) →
    ∀ x, Evaluates (Code.pair a b) x (pair (f x) (g x)) (pairTrace f g tf tg a b x) := by
  intro a b hf hg x
  exact evaluates_pair a b x (f x) (g x) (tf x) (tg x) (hf x) (hg x)

theorem evaluates_rec_unary (base step tb ts : Nat → Nat) : ∀ a b,
    (∀ x, Evaluates a x (base x) (tb x)) → (∀ x, Evaluates b x (step x) (ts x)) →
    ∀ z, Evaluates (Code.rec a b) z
      (primrec (base (unpairLeft z))
        (fun i y => step (pair (unpairLeft z) (pair i y))) (unpairRight z))
      (recTrace base (fun x i y => step (pair x (pair i y)))
        tb (fun x i y => ts (pair x (pair i y))) a b (unpairLeft z) (unpairRight z)) := by
  intro a b hb hs z
  have h := evaluates_rec base (fun x i y => step (pair x (pair i y)))
    tb (fun x i y => ts (pair x (pair i y))) a b hb
    (fun x i y => hs (pair x (pair i y))) (unpairLeft z) (unpairRight z)
  rw [pair_unpair] at h
  exact h

/-! ## Recovering child computations -/

theorem checkNode_of_evaluates : ∀ e x y t, Evaluates e x y t →
    checkNode e x y (childLeft t) (childRight t) (isValid (childLeft t))
      (isValid (childRight t)) = 1 := by
  intro e x y t h
  rcases h with (hv, he, hx, hy)
  have ht := ne_zero_of_isValid t hv
  have hn := node_eta t ht
  rw [he, hx, hy] at hn
  have hc := isValid_node e x y (childLeft t) (childRight t)
  rw [hn] at hc
  exact eq_trans (eq_symm hc) hv

theorem output_zero_of_evaluates : ∀ x y t, Evaluates Code.zero x y t → y = 0 := by
  intro x y t h
  have checked := checkNode_of_evaluates Code.zero x y t h
  have components := and_left (band_eq_one _ _) checked
  exact and_left (eqb_ne_zero y (0)) (and_right components)

theorem output_succ_of_evaluates : ∀ x y t, Evaluates Code.succ x y t → y = S x := by
  intro x y t h
  have checked := checkNode_of_evaluates Code.succ x y t h
  have components := and_left (band_eq_one _ _) checked
  exact and_left (eqb_ne_zero y (S x)) (and_right components)

theorem output_left_of_evaluates : ∀ x y t,
    Evaluates Code.left x y t → y = _root_.unpairLeft x := by
  intro x y t h
  have checked := checkNode_of_evaluates Code.left x y t h
  have components := and_left (band_eq_one _ _) checked
  exact and_left (eqb_ne_zero y (_root_.unpairLeft x)) (and_right components)

theorem output_right_of_evaluates : ∀ x y t,
    Evaluates Code.right x y t → y = _root_.unpairRight x := by
  intro x y t h
  have checked := checkNode_of_evaluates Code.right x y t h
  have components := and_left (band_eq_one _ _) checked
  exact and_left (eqb_ne_zero y (_root_.unpairRight x)) (and_right components)

theorem band_ne_zero : ∀ a b, ¬ band a b = 0 → ¬ a = 0 ∧ ¬ b = 0 := by
  intro a b h
  apply and_left (band_eq_one a b)
  exact and_right (bool_eq_one (band a b) (band_bool a b)) h

theorem checkNode_pair : ∀ f g x y p q hp hq,
    checkNode (Code.pair f g) x y p q hp hq =
      band (band hp (eqb (input p) x)) (band hq (band (eqb (program p) f)
        (band (eqb (program q) g) (band (eqb (input q) x)
          (eqb y (_root_.pair (output p) (output q))))))) := by
  intro f g x y p q hp hq
  have select : ∀ a b c d e rest,
      ite (eqb (4 + 0) 0) a (ite (eqb (4 + 0) 1) b
        (ite (eqb (4 + 0) 2) c (ite (eqb (4 + 0) 3) d
        (ite (eqb (4 + 0) 4) e rest)))) = e :=
    fun a b c d e rest => rfl
  unfold Code.pair checkNode
  rw [Code.tag_binary 0 f g rfl, select, Code.args_binary 0 f g rfl,
    unpairLeft_pair, unpairRight_pair]

theorem evaluates_pair_elim : ∀ f g x y t, Evaluates (Code.pair f g) x y t →
    Evaluates f x (output (childLeft t)) (childLeft t) ∧
    Evaluates g x (output (childRight t)) (childRight t) ∧
    y = _root_.pair (output (childLeft t)) (output (childRight t)) := by
  intro f g x y t h
  have checked := checkNode_of_evaluates (Code.pair f g) x y t h
  rw [checkNode_pair] at checked
  rcases and_left (band_eq_one _ _) checked with (hp, hq)
  rcases band_ne_zero _ _ hp with (hp, hpx)
  rcases band_ne_zero _ _ hq with (hq, rest)
  rcases band_ne_zero _ _ rest with (hpe, rest)
  rcases band_ne_zero _ _ rest with (hqe, rest)
  rcases band_ne_zero _ _ rest with (hqx, hy)
  exact ((and_right (bool_eq_one _ (isValid_bool _)) hp,
    and_left (eqb_ne_zero _ _) hpe, and_left (eqb_ne_zero _ _) hpx, rfl),
    (and_right (bool_eq_one _ (isValid_bool _)) hq,
    and_left (eqb_ne_zero _ _) hqe, and_left (eqb_ne_zero _ _) hqx, rfl),
    and_left (eqb_ne_zero _ _) hy)

theorem checkNode_comp : ∀ f g x y p q hp hq,
    checkNode (Code.comp f g) x y p q hp hq =
      band (band hp (eqb (input p) x)) (band (band hq (eqb (output q) y))
        (band (eqb (program p) g) (band (eqb (program q) f)
          (eqb (input q) (output p))))) := by
  intro f g x y p q hp hq
  have select : ∀ a b c d e f rest,
      ite (eqb (4 + 1) 0) a (ite (eqb (4 + 1) 1) b
        (ite (eqb (4 + 1) 2) c (ite (eqb (4 + 1) 3) d
        (ite (eqb (4 + 1) 4) e (ite (eqb (4 + 1) 5) f rest))))) = f :=
    fun a b c d e f rest => rfl
  unfold Code.comp checkNode
  rw [Code.tag_binary 1 f g rfl, select, Code.args_binary 1 f g rfl,
    unpairLeft_pair, unpairRight_pair]

theorem evaluates_comp_elim : ∀ f g x y t, Evaluates (Code.comp f g) x y t →
    Evaluates g x (output (childLeft t)) (childLeft t) ∧
    Evaluates f (output (childLeft t)) y (childRight t) := by
  intro f g x y t h
  have checked := checkNode_of_evaluates (Code.comp f g) x y t h
  rw [checkNode_comp] at checked
  rcases and_left (band_eq_one _ _) checked with (hp, rest)
  rcases band_ne_zero _ _ hp with (hp, hpx)
  rcases band_ne_zero _ _ rest with (hq, rest)
  rcases band_ne_zero _ _ hq with (hq, hqy)
  rcases band_ne_zero _ _ rest with (hpe, rest)
  rcases band_ne_zero _ _ rest with (hqe, hqx)
  exact ((and_right (bool_eq_one _ (isValid_bool _)) hp,
    and_left (eqb_ne_zero _ _) hpe, and_left (eqb_ne_zero _ _) hpx, rfl),
    (and_right (bool_eq_one _ (isValid_bool _)) hq,
    and_left (eqb_ne_zero _ _) hqe, and_left (eqb_ne_zero _ _) hqx,
    and_left (eqb_ne_zero _ _) hqy))

theorem checkNode_rec_zero : ∀ f g x y p q hp hq,
    checkNode (Code.rec f g) (_root_.pair x 0) y p q hp hq =
      band hp (band (eqb q 0) (band (eqb (program p) f)
        (band (eqb (input p) x) (eqb (output p) y)))) := by
  intro f g x y p q hp hq
  rw [Code.rec, checkNode, Code.tag_binary 2 f g rfl, Code.args_binary 2 f g rfl,
    unpairLeft_pair, unpairRight_pair,
    unpairRight_pair, unpairLeft_pair]
  rfl

theorem evaluates_rec_zero_elim : ∀ f g x y t, Evaluates (Code.rec f g) (_root_.pair x 0) y t →
    Evaluates f x y (childLeft t) := by
  intro f g x y t h
  have checked := checkNode_of_evaluates (Code.rec f g) (_root_.pair x 0) y t h
  rw [checkNode_rec_zero] at checked
  rcases and_left (band_eq_one _ _) checked with (hp, rest)
  rcases band_ne_zero _ _ rest with (hq, rest)
  rcases band_ne_zero _ _ rest with (hpe, rest)
  rcases band_ne_zero _ _ rest with (hpx, hpy)
  exact (and_right (bool_eq_one _ (isValid_bool _)) hp,
    and_left (eqb_ne_zero _ _) hpe, and_left (eqb_ne_zero _ _) hpx,
    and_left (eqb_ne_zero _ _) hpy)

theorem checkNode_rec_succ : ∀ f g x n y p q hp hq,
    checkNode (Code.rec f g) (_root_.pair x (S n)) y p q hp hq =
      band hp (band (band hq (eqb (output q) y))
        (band (eqb (program p) (Code.rec f g)) (band (eqb (program q) g)
          (band (eqb (input p) (_root_.pair x n))
            (eqb (input q) (_root_.pair x (_root_.pair n (output p)))))))) := by
  intro f g x n y p q hp hq
  rw [Code.rec, checkNode, Code.tag_binary 2 f g rfl, Code.args_binary 2 f g rfl,
    unpairLeft_pair, unpairRight_pair,
    unpairRight_pair, unpairLeft_pair]
  rfl

theorem evaluates_rec_succ_elim : ∀ f g x n y t,
    Evaluates (Code.rec f g) (_root_.pair x (S n)) y t →
    Evaluates (Code.rec f g) (_root_.pair x n) (output (childLeft t)) (childLeft t) ∧
    Evaluates g (_root_.pair x (_root_.pair n (output (childLeft t)))) y (childRight t) := by
  intro f g x n y t h
  have checked := checkNode_of_evaluates (Code.rec f g) (_root_.pair x (S n)) y t h
  rw [checkNode_rec_succ] at checked
  rcases and_left (band_eq_one _ _) checked with (hp, rest)
  rcases band_ne_zero _ _ rest with (hq, rest)
  rcases band_ne_zero _ _ hq with (hq, hqy)
  rcases band_ne_zero _ _ rest with (hpe, rest)
  rcases band_ne_zero _ _ rest with (hqe, rest)
  rcases band_ne_zero _ _ rest with (hpx, hqx)
  exact ((and_right (bool_eq_one _ (isValid_bool _)) hp,
    and_left (eqb_ne_zero _ _) hpe, and_left (eqb_ne_zero _ _) hpx, rfl),
    (and_right (bool_eq_one _ (isValid_bool _)) hq,
    and_left (eqb_ne_zero _ _) hqe, and_left (eqb_ne_zero _ _) hqx,
    and_left (eqb_ne_zero _ _) hqy))

/-! ## Recursion histories -/

/-- `followLeft k t` follows `childLeft` from computation tree `t` for `k` steps. -/
def followLeft : Nat → Nat → Nat := fun k t =>
  primrec t (fun _ u => childLeft u) k

theorem followLeft_zero : ∀ t, followLeft 0 t = t := fun t => rfl

theorem followLeft_succ : ∀ k t, followLeft (S k) t = childLeft (followLeft k t) :=
  fun k t => rfl

theorem followLeft_evaluates : ∀ f g x n y t k,
    Evaluates (Code.rec f g) (_root_.pair x n) y t → k ≤ n →
    Evaluates (Code.rec f g) (_root_.pair x (n - k)) (output (followLeft k t)) (followLeft k t) ∧
      followLeft k t ≤ t := by
  intro f g x n y t k h
  induction k with k ih
  · intro hk
    rcases h with (hv, he, hx, hy)
    exact ((hv, he, hx, rfl), le_refl t)
  · intro hk
    have previous := ih (le_trans k (S k) n (le_succ_self k) hk)
    rcases previous with (hc, hb)
    have nonzero := ne_zero_of_isValid (followLeft k t) (and_left hc)
    have less := childLeft_lt (followLeft k t) nonzero
    rw [← succ_sub_succ_eq_sub n k hk] at hc
    have step := evaluates_rec_succ_elim f g x (n - S k) (output (followLeft k t))
      (followLeft k t) hc
    exact (and_left step, le_trans _ _ _ (le_of_lt _ _ less) hb)

/-- `recTraceAt t n i` extracts the subtree for step `i` from an `n`-step recursion tree `t`. -/
def recTraceAt : Nat → Nat → Nat → Nat := fun t n i => followLeft (n - i) t

/-- `recValue t n i` reads the intermediate output at step `i` of an `n`-step recursion tree `t`. -/
def recValue : Nat → Nat → Nat → Nat := fun t n i => output (recTraceAt t n i)

/-- `recBaseTrace t n` extracts the base-case computation from an `n`-step recursion tree `t`. -/
def recBaseTrace : Nat → Nat → Nat := fun t n => childLeft (recTraceAt t n 0)

/-- `recStepTrace t n i` extracts the step computation at index `i` from an `n`-step recursion
tree `t`. -/
def recStepTrace : Nat → Nat → Nat → Nat := fun t n i => childRight (recTraceAt t n (S i))

theorem recTraceAt_evaluates : ∀ f g x n y t i,
    Evaluates (Code.rec f g) (_root_.pair x n) y t → i ≤ n →
    Evaluates (Code.rec f g) (_root_.pair x i) (recValue t n i) (recTraceAt t n i) ∧
      recTraceAt t n i ≤ t := by
  intro f g x n y t i h hi
  have hc := followLeft_evaluates f g x n y t (n - i) h (sub_le n i)
  rw [sub_sub_cancel n i hi] at hc
  exact hc

theorem recTraceAt_step : ∀ t n i, i < n →
    recTraceAt t n i = childLeft (recTraceAt t n (S i)) := by
  intro t n i hi
  rw [recTraceAt, ← succ_sub_succ_eq_sub n i hi, followLeft_succ]
  rfl

theorem recValue_last : ∀ n y t, output t = y → recValue t n n = y := by
  intro n y t h
  rw [recValue, recTraceAt, sub_self, followLeft_zero]
  exact h

theorem recBaseTrace_evaluates : ∀ f g x n y t,
    Evaluates (Code.rec f g) (_root_.pair x n) y t →
    Evaluates f x (recValue t n 0) (recBaseTrace t n) ∧ recBaseTrace t n < t := by
  intro f g x n y t h
  have hc := recTraceAt_evaluates f g x n y t 0 h (zero_le n)
  have ht := and_left hc
  have hv := evaluates_rec_zero_elim f g x (recValue t n 0) (recTraceAt t n 0) ht
  have less := childLeft_lt (recTraceAt t n 0)
    (ne_zero_of_isValid (recTraceAt t n 0) (and_left ht))
  exact (hv, lt_of_lt_of_le _ _ _ less (and_right hc))

theorem recStepTrace_evaluates : ∀ f g x n y t i,
    Evaluates (Code.rec f g) (_root_.pair x n) y t → i < n →
    Evaluates g (_root_.pair x (_root_.pair i (recValue t n i))) (recValue t n (S i))
      (recStepTrace t n i) ∧ recStepTrace t n i < t := by
  intro f g x n y t i h hi
  have hc := recTraceAt_evaluates f g x n y t (S i) h hi
  have ht := and_left hc
  have steps := evaluates_rec_succ_elim f g x i (recValue t n (S i))
    (recTraceAt t n (S i)) ht
  have hv := and_right steps
  have he := recTraceAt_step t n i hi
  have value : output (childLeft (recTraceAt t n (S i))) = recValue t n i := by
    rw [recValue, he]
  rw [value] at hv
  have less := childRight_lt (recTraceAt t n (S i))
    (ne_zero_of_isValid (recTraceAt t n (S i)) (and_left ht))
  exact (hv, lt_of_lt_of_le _ _ _ less (and_right hc))

end Computation

/-! ## Computed functions -/

/-- `Computes e x y` means that program code `e` has a finite computation from `x` to `y`. -/
def Computes : Nat → Nat → Nat → Prop := fun e x y => ∃ t, Computation.Evaluates e x y t

theorem computes_pair : ∀ f g x y z,
    Computes f x y → Computes g x z → Computes (Code.pair f g) x (pair y z) := by
  rintro f g x y z (p, hp) (q, hq)
  exact (Computation.node (Code.pair f g) x (pair y z) p q,
    Computation.evaluates_pair f g x y z p q hp hq)

theorem computes_comp : ∀ f g x y z,
    Computes g x y → Computes f y z → Computes (Code.comp f g) x z := by
  rintro f g x y z (p, hp) (q, hq)
  exact (Computation.node (Code.comp f g) x z p q,
    Computation.evaluates_comp f g x y z p q hp hq)

end Primrec

/-- `Primrec f` means that a program using basic functions, composition, pairing, and primitive
recursion computes `f x` for every input `x`. -/
def Primrec (f : Nat → Nat) : Prop :=
  ∃ e, ∀ x, Primrec.Computes e x (f x)

/-- A primitive-recursive program with an explicit correct computation for every input witnesses
primitive recursiveness. The tree builder is a numerical function in the PRA language. -/
theorem Primrec.of_evaluates (f trace : Nat → Nat) : ∀ e,
    (∀ x, Primrec.Computation.Evaluates e x (f x) (trace x)) → Primrec f := by
  intro e h
  exists e
  intro x
  exact (trace x, h x)

end
