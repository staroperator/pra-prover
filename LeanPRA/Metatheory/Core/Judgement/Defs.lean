module

public import LeanPRA.Core.PrimitiveTypes

/-!
# Declarative PRA judgements

These rules specify the full core language:

- `ParameterContext`, `LocalContext`, and `ProofContext` keep the four index spaces separate.
- `Context.parameters` presents executable parameter fields as a declarative parameter context.
- `PredicateSubtyping` includes QF predicates into general predicates at the same arity.
- `TermTyping` and `PredicateTyping` form terms and predicates; formulas have arity zero.
- `TermEq` and `PredicateEq` specify typed beta/eta, unfolding, and congruence equations.
- `ProofTyping` checks explicit object proof data, including conversion and QF induction.
- `ContextWF`, `DeclarationWF`, and `EnvironmentWF` specify valid assumptions and declarations.
- `DeclarationsWF` records fresh, well-formed admissions in a specified list order.
- `EnvironmentExtends` preserves successful lookups; extensional map equality compares contents.

The environment and parameter context are fixed throughout each judgement. Local term contexts
change under numerical binders and function-valued lets. Only proof typing has proof hypotheses.
All parameter and local types are intrinsically formed arities or predicate signatures. Proof
hypotheses are formulas in the entire current local context.

Typing and equality rules can be stated over arbitrary maps; metatheorems about global bodies
and proofs require `EnvironmentWF` and, where applicable, `ContextWF`. Equality regularity in a
valid environment means that both endpoints have the displayed type. Structural results that
inspect transparent bodies use their declarative validity so that global bodies have no unbound
local variables.

The imported substitution operations act on syntax only. `subst0` removes a local binder;
`instantiate` replaces declaration parameters simultaneously in a single pass. List judgements
below require one typed actual per declared parameter. Predicate references use their declared
signatures. A Prop declaration stays Prop when its arguments are instantiated, including when its
body is QF. Theorem bodies remain opaque to definitional equality.
-/

@[expose] public section

namespace LeanPRA.Core.Theory

/-- Declaration parameters, numbered in declaration order in two independent index spaces. -/
structure ParameterContext where
  functions : List Arity := []
  predicates : List PredicateSignature := []
  deriving Repr, BEq, Inhabited

/-- The parameter spaces of the executable context, separated from locals and hypotheses. -/
def _root_.LeanPRA.Core.Context.parameters (c : Context) : ParameterContext :=
  { functions := c.functions, predicates := c.predicates }

/-- Local term arities, with the newest variable first. Only lets can bind a nonzero arity. -/
abbrev LocalContext := List Arity

/-- Local proof hypotheses, newest first, expressed in the current local term context. -/
abbrev ProofContext := List Predicate

/-- The only predicate subtyping: reflexivity and QF inclusion at an unchanged numerical arity. -/
inductive PredicateSubtyping : PredicateSignature → PredicateSignature → Prop where
  | refl : PredicateSubtyping σ σ
  | lift : PredicateSubtyping ⟨k, .qf⟩ ⟨k, .prop⟩

mutual

/-- Declarative first-order term typing. An ordinary lambda or application binds or consumes
only a number. Function actuals belong to declaration and recursor interfaces. -/
inductive TermTyping (E : Environment) (Ξ : ParameterContext) :
    LocalContext → Term → Arity → Prop where
  | bvar (lookup : Γ[i]? = some k) : TermTyping E Ξ Γ (.bvar i) k
  | parameter (lookup : Ξ.functions[i]? = some k) : TermTyping E Ξ Γ (.parameter i) k
  | zero : TermTyping E Ξ Γ .zero 0
  | succ : TermTyping E Ξ Γ .succ 1
  | lam (body : TermTyping E Ξ (0 :: Γ) t k) : TermTyping E Ξ Γ (.lam binderName t) (k + 1)
  | app (function : TermTyping E Ξ Γ f (k + 1)) (argument : TermTyping E Ξ Γ a 0) :
      TermTyping E Ξ Γ (.app f a) k
  | letE (value : TermTyping E Ξ Γ a j) (body : TermTyping E Ξ (j :: Γ) t k) :
      TermTyping E Ξ Γ (.letE binderName a t) k
  | primrec (base : TermTyping E Ξ Γ b 0) (step : TermTyping E Ξ Γ s 2) :
      TermTyping E Ξ Γ (.primrec b s) 1
  | definition (lookup : E[name]? = some (.function d))
      (arguments : FunctionArguments E Ξ Γ fs d.functions) :
      TermTyping E Ξ Γ (.definition name fs) d.arity

/-- Exact, ordered function-parameter instantiation, including function-valued actuals. -/
inductive FunctionArguments (E : Environment) (Ξ : ParameterContext) :
    LocalContext → List Term → List Arity → Prop where
  | nil : FunctionArguments E Ξ Γ [] []
  | cons (head : TermTyping E Ξ Γ t k) (tail : FunctionArguments E Ξ Γ ts ks) :
      FunctionArguments E Ξ Γ (t :: ts) (k :: ks)

end

mutual

/-- Predicate typing at a full signature. Connectives use a common sort, quantifiers produce
Prop, and global references use the signature stored in the environment. -/
inductive PredicateTyping (E : Environment) (Ξ : ParameterContext) :
    LocalContext → Predicate → PredicateSignature → Prop where
  | false : PredicateTyping E Ξ Γ .false ⟨0, .qf⟩
  | true : PredicateTyping E Ξ Γ .true ⟨0, .qf⟩
  | equal (left : TermTyping E Ξ Γ a 0) (right : TermTyping E Ξ Γ b 0) :
      PredicateTyping E Ξ Γ (.equal a b) ⟨0, .qf⟩
  | imp (left : PredicateTyping E Ξ Γ A ⟨0, s⟩)
      (right : PredicateTyping E Ξ Γ B ⟨0, s⟩) :
      PredicateTyping E Ξ Γ (.imp A B) ⟨0, s⟩
  | and (left : PredicateTyping E Ξ Γ A ⟨0, s⟩)
      (right : PredicateTyping E Ξ Γ B ⟨0, s⟩) :
      PredicateTyping E Ξ Γ (.and A B) ⟨0, s⟩
  | or (left : PredicateTyping E Ξ Γ A ⟨0, s⟩)
      (right : PredicateTyping E Ξ Γ B ⟨0, s⟩) :
      PredicateTyping E Ξ Γ (.or A B) ⟨0, s⟩
  | all (body : PredicateTyping E Ξ Γ P ⟨1, .prop⟩) :
      PredicateTyping E Ξ Γ (.all P) ⟨0, .prop⟩
  | ex (body : PredicateTyping E Ξ Γ P ⟨1, .prop⟩) :
      PredicateTyping E Ξ Γ (.ex P) ⟨0, .prop⟩
  | parameter (lookup : Ξ.predicates[i]? = some σ) :
      PredicateTyping E Ξ Γ (.parameter i) σ
  | lam (body : PredicateTyping E Ξ (0 :: Γ) P ⟨k, s⟩) :
      PredicateTyping E Ξ Γ (.lam binderName P) ⟨k + 1, s⟩
  | app (function : PredicateTyping E Ξ Γ P ⟨k + 1, s⟩)
      (argument : TermTyping E Ξ Γ a 0) : PredicateTyping E Ξ Γ (.app P a) ⟨k, s⟩
  | letTerm (value : TermTyping E Ξ Γ a j) (body : PredicateTyping E Ξ Γ P σ) :
      PredicateTyping E Ξ Γ (.letTerm binderName a P) σ
  | letPredicate (value : PredicateTyping E Ξ Γ Q τ) (body : PredicateTyping E Ξ Γ P σ) :
      PredicateTyping E Ξ Γ (.letPredicate binderName Q P) σ
  | definition (lookup : E[name]? = some (.predicate d))
      (functions : FunctionArguments E Ξ Γ fs d.functions)
      (predicates : PredicateArguments E Ξ Γ ps d.predicates) :
      PredicateTyping E Ξ Γ (.definition name fs ps) d.signature
  | subsumption (typing : PredicateTyping E Ξ Γ P σ) (subtype : PredicateSubtyping σ τ) :
      PredicateTyping E Ξ Γ P τ

/-- Exact predicate-parameter instantiation at the declared signatures, allowing QF inclusion. -/
inductive PredicateArguments (E : Environment) (Ξ : ParameterContext) :
    LocalContext → List Predicate → List PredicateSignature → Prop where
  | nil : PredicateArguments E Ξ Γ [] []
  | cons (head : PredicateTyping E Ξ Γ P σ) (tail : PredicateArguments E Ξ Γ ps signatures) :
      PredicateArguments E Ξ Γ (P :: ps) (σ :: signatures)

end

mutual

/-- Typed computational definitional equality. Unfolding requires a typed specialized body;
in valid environments this premise is supplied by parameter-instantiation preservation. -/
inductive TermEq (E : Environment) (Ξ : ParameterContext) :
    LocalContext → Term → Term → Arity → Prop where
  | refl (typing : TermTyping E Ξ Γ t k) : TermEq E Ξ Γ t t k
  | symm (equality : TermEq E Ξ Γ t u k) : TermEq E Ξ Γ u t k
  | trans (left : TermEq E Ξ Γ t u k) (right : TermEq E Ξ Γ u v k) : TermEq E Ξ Γ t v k
  | beta (body : TermTyping E Ξ (0 :: Γ) t k) (argument : TermTyping E Ξ Γ a 0) :
      TermEq E Ξ Γ (.app (.lam binderName t) a) (t.subst0 a) k
  | eta (function : TermTyping E Ξ Γ f (k + 1)) :
      TermEq E Ξ Γ (.lam binderName (.app f.shift (.bvar 0))) f (k + 1)
  | zeta (value : TermTyping E Ξ Γ a j) (body : TermTyping E Ξ (j :: Γ) t k) :
      TermEq E Ξ Γ (.letE binderName a t) (t.subst0 a) k
  | delta (lookup : E[name]? = some (.function d))
      (arguments : FunctionArguments E Ξ Γ fs d.functions)
      (body : TermTyping E Ξ Γ (d.body.instantiate fs) d.arity) :
      TermEq E Ξ Γ (.definition name fs) (d.body.instantiate fs) d.arity
  | primrecZero (base : TermTyping E Ξ Γ b 0) (step : TermTyping E Ξ Γ s 2) :
      TermEq E Ξ Γ (.app (.primrec b s) .zero) b 0
  | primrecSucc (base : TermTyping E Ξ Γ b 0) (step : TermTyping E Ξ Γ s 2)
      (argument : TermTyping E Ξ Γ n 0) :
      TermEq E Ξ Γ (.app (.primrec b s) (.app .succ n)) (.app (.app s n) (.app (.primrec b s) n)) 0
  | lam (body : TermEq E Ξ (0 :: Γ) t u k) :
      TermEq E Ξ Γ (.lam binderName t) (.lam otherBinderName u) (k + 1)
  | app (function : TermEq E Ξ Γ f g (k + 1)) (argument : TermEq E Ξ Γ a b 0) :
      TermEq E Ξ Γ (.app f a) (.app g b) k
  | letE (value : TermEq E Ξ Γ a b j) (body : TermEq E Ξ (j :: Γ) t u k) :
      TermEq E Ξ Γ (.letE binderName a t) (.letE otherBinderName b u) k
  | primrec (base : TermEq E Ξ Γ a b 0) (step : TermEq E Ξ Γ s t 2) :
      TermEq E Ξ Γ (.primrec a s) (.primrec b t) 1
  | definition (lookup : E[name]? = some (.function d))
      (arguments : FunctionArgumentEq E Ξ Γ fs gs d.functions) :
      TermEq E Ξ Γ (.definition name fs) (.definition name gs) d.arity

/-- Pointwise typed conversion of function actuals at their declaration-interface arities. -/
inductive FunctionArgumentEq (E : Environment) (Ξ : ParameterContext) :
    LocalContext → List Term → List Term → List Arity → Prop where
  | nil : FunctionArgumentEq E Ξ Γ [] [] []
  | cons (head : TermEq E Ξ Γ t u k) (tail : FunctionArgumentEq E Ξ Γ ts us ks) :
      FunctionArgumentEq E Ξ Γ (t :: ts) (u :: us) (k :: ks)

end

mutual

/-- Typed predicate definitional equality, indexed by both arity and sort. Subsumption raises
QFProp to Prop. Unfolding and definition congruence preserve the declared signature or raise it. -/
inductive PredicateEq (E : Environment) (Ξ : ParameterContext) :
    LocalContext → Predicate → Predicate → PredicateSignature → Prop where
  | refl (typing : PredicateTyping E Ξ Γ P σ) : PredicateEq E Ξ Γ P P σ
  | symm (equality : PredicateEq E Ξ Γ P Q σ) : PredicateEq E Ξ Γ Q P σ
  | trans (left : PredicateEq E Ξ Γ P Q σ) (right : PredicateEq E Ξ Γ Q R σ) :
      PredicateEq E Ξ Γ P R σ
  | subsumption (equality : PredicateEq E Ξ Γ P Q σ) (subtype : PredicateSubtyping σ τ) :
      PredicateEq E Ξ Γ P Q τ
  | beta (body : PredicateTyping E Ξ (0 :: Γ) P ⟨k, s⟩)
      (argument : TermTyping E Ξ Γ a 0) :
      PredicateEq E Ξ Γ (.app (.lam binderName P) a) (P.subst0 a) ⟨k, s⟩
  | eta (function : PredicateTyping E Ξ Γ P ⟨k + 1, s⟩) :
      PredicateEq E Ξ Γ (.lam binderName (.app P.shift (.bvar 0))) P ⟨k + 1, s⟩
  | zetaTerm (value : TermTyping E Ξ Γ a j) (body : PredicateTyping E Ξ Γ P σ) :
      PredicateEq E Ξ Γ (.letTerm binderName a P) P σ
  | zetaPredicate (value : PredicateTyping E Ξ Γ Q τ) (body : PredicateTyping E Ξ Γ P σ) :
      PredicateEq E Ξ Γ (.letPredicate binderName Q P) P σ
  | delta (lookup : E[name]? = some (.predicate d))
      (functions : FunctionArguments E Ξ Γ fs d.functions)
      (predicates : PredicateArguments E Ξ Γ ps d.predicates)
      (body : PredicateTyping E Ξ Γ (d.body.instantiate fs ps) σ)
      (bound : PredicateSubtyping d.signature σ) :
      PredicateEq E Ξ Γ (.definition name fs ps) (d.body.instantiate fs ps) σ
  | equal (left : TermEq E Ξ Γ a b 0) (right : TermEq E Ξ Γ c d 0) :
      PredicateEq E Ξ Γ (.equal a c) (.equal b d) ⟨0, .qf⟩
  | imp (left : PredicateEq E Ξ Γ A C ⟨0, s⟩)
      (right : PredicateEq E Ξ Γ B D ⟨0, s⟩) :
      PredicateEq E Ξ Γ (.imp A B) (.imp C D) ⟨0, s⟩
  | and (left : PredicateEq E Ξ Γ A C ⟨0, s⟩)
      (right : PredicateEq E Ξ Γ B D ⟨0, s⟩) :
      PredicateEq E Ξ Γ (.and A B) (.and C D) ⟨0, s⟩
  | or (left : PredicateEq E Ξ Γ A C ⟨0, s⟩)
      (right : PredicateEq E Ξ Γ B D ⟨0, s⟩) :
      PredicateEq E Ξ Γ (.or A B) (.or C D) ⟨0, s⟩
  | all (body : PredicateEq E Ξ Γ P Q ⟨1, .prop⟩) :
      PredicateEq E Ξ Γ (.all P) (.all Q) ⟨0, .prop⟩
  | ex (body : PredicateEq E Ξ Γ P Q ⟨1, .prop⟩) :
      PredicateEq E Ξ Γ (.ex P) (.ex Q) ⟨0, .prop⟩
  | lam (body : PredicateEq E Ξ (0 :: Γ) P Q ⟨k, s⟩) :
      PredicateEq E Ξ Γ (.lam binderName P) (.lam otherBinderName Q) ⟨k + 1, s⟩
  | app (function : PredicateEq E Ξ Γ P Q ⟨k + 1, s⟩)
      (argument : TermEq E Ξ Γ a b 0) :
      PredicateEq E Ξ Γ (.app P a) (.app Q b) ⟨k, s⟩
  | definition (lookup : E[name]? = some (.predicate d))
      (functions : FunctionArgumentEq E Ξ Γ fs gs d.functions)
      (predicates : PredicateArgumentEq E Ξ Γ ps qs d.predicates)
      (left : PredicateTyping E Ξ Γ (.definition name fs ps) σ)
      (right : PredicateTyping E Ξ Γ (.definition name gs qs) σ) :
      PredicateEq E Ξ Γ (.definition name fs ps) (.definition name gs qs) σ

/-- Pointwise typed conversion of predicate actuals at their declared full signatures. -/
inductive PredicateArgumentEq (E : Environment) (Ξ : ParameterContext) :
    LocalContext → List Predicate → List Predicate → List PredicateSignature → Prop where
  | nil : PredicateArgumentEq E Ξ Γ [] [] []
  | cons (head : PredicateEq E Ξ Γ P Q σ)
      (tail : PredicateArgumentEq E Ξ Γ ps qs signatures) :
      PredicateArgumentEq E Ξ Γ (P :: ps) (Q :: qs) (σ :: signatures)

end

/-- Explicit PRA derivations. Only this judgement depends on proof hypotheses. Numerical binders
shift kept hypotheses. Primitive proof heads check their schema predicates in the surrounding
context and expose their full formulas; induction requires a unary QF motive. -/
inductive ProofTyping (E : Environment) (Ξ : ParameterContext) :
    LocalContext → ProofContext → Proof → Predicate → Prop where
  | hyp (lookup : H[i]? = some A) : ProofTyping E Ξ Γ H (.hyp i) A
  | trueIntro : ProofTyping E Ξ Γ H .trueIntro .true
  | theoremE (lookup : E[name]? = some (.theoremE d))
      (functions : FunctionArguments E Ξ Γ fs d.functions)
      (predicates : PredicateArguments E Ξ Γ ps d.predicates) :
      ProofTyping E Ξ Γ H (.theoremE name fs ps) (d.type.instantiate fs ps)
  | impIntro (antecedent : PredicateTyping E Ξ Γ A ⟨0, .prop⟩)
      (body : ProofTyping E Ξ Γ (A :: H) p B) :
      ProofTyping E Ξ Γ H (.impIntro binderName A p) (.imp A B)
  | impElim (function : ProofTyping E Ξ Γ H p (.imp A B))
      (argument : ProofTyping E Ξ Γ H q A) : ProofTyping E Ξ Γ H (.impElim p q) B
  | andIntro (left : ProofTyping E Ξ Γ H p A) (right : ProofTyping E Ξ Γ H q B) :
      ProofTyping E Ξ Γ H (.andIntro p q) (.and A B)
  | andLeft (left : PredicateTyping E Ξ Γ A ⟨0, .prop⟩)
      (right : PredicateTyping E Ξ Γ B ⟨0, .prop⟩) :
      ProofTyping E Ξ Γ H (.andLeft A B) (.imp (.and A B) A)
  | andRight (left : PredicateTyping E Ξ Γ A ⟨0, .prop⟩)
      (right : PredicateTyping E Ξ Γ B ⟨0, .prop⟩) :
      ProofTyping E Ξ Γ H (.andRight A B) (.imp (.and A B) B)
  | orLeft (left : PredicateTyping E Ξ Γ A ⟨0, .prop⟩)
      (right : PredicateTyping E Ξ Γ B ⟨0, .prop⟩) :
      ProofTyping E Ξ Γ H (.orLeft A B) (.imp A (.or A B))
  | orRight (left : PredicateTyping E Ξ Γ A ⟨0, .prop⟩)
      (right : PredicateTyping E Ξ Γ B ⟨0, .prop⟩) :
      ProofTyping E Ξ Γ H (.orRight A B) (.imp B (.or A B))
  | orElim (left : PredicateTyping E Ξ Γ A ⟨0, .prop⟩)
      (right : PredicateTyping E Ξ Γ B ⟨0, .prop⟩)
      (target : PredicateTyping E Ξ Γ C ⟨0, .prop⟩) :
      ProofTyping E Ξ Γ H (.orElim A B C)
        (.imp (.or A B) (.imp (.imp A C) (.imp (.imp B C) C)))
  | falseElim (target : PredicateTyping E Ξ Γ A ⟨0, .prop⟩) :
      ProofTyping E Ξ Γ H (.falseElim A) (.imp .false A)
  | forallIntro (motive : PredicateTyping E Ξ Γ P ⟨1, .prop⟩)
      (body : ProofTyping E Ξ (0 :: Γ) (H.map Predicate.shift) p (.app P.shift (.bvar 0))) :
      ProofTyping E Ξ Γ H (.forallIntro binderName P p) (.all P)
  | forallElim (proof : ProofTyping E Ξ Γ H p (.all P)) (argument : TermTyping E Ξ Γ a 0) :
      ProofTyping E Ξ Γ H (.forallElim p a) (.app P a)
  | existsIntro (motive : PredicateTyping E Ξ Γ P ⟨1, .prop⟩)
      (witness : TermTyping E Ξ Γ a 0) (proof : ProofTyping E Ξ Γ H p (.app P a)) :
      ProofTyping E Ξ Γ H (.existsIntro P a p) (.ex P)
  | existsElim (motive : PredicateTyping E Ξ Γ P ⟨1, .prop⟩)
      (target : PredicateTyping E Ξ Γ C ⟨0, .prop⟩) :
      ProofTyping E Ξ Γ H (.existsElim P C) (existentialEliminationType P C)
  | letE (type : PredicateTyping E Ξ Γ A ⟨0, .prop⟩)
      (value : ProofTyping E Ξ Γ H p A) (body : ProofTyping E Ξ Γ (A :: H) q B) :
      ProofTyping E Ξ Γ H (.letE binderName A p q) B
  | letTerm (value : TermTyping E Ξ Γ a j) (body : ProofTyping E Ξ Γ H p A) :
      ProofTyping E Ξ Γ H (.letTerm binderName a p) A
  | letPredicate (value : PredicateTyping E Ξ Γ P σ) (body : ProofTyping E Ξ Γ H p A) :
      ProofTyping E Ξ Γ H (.letPredicate binderName P p) A
  | ascribe (type : PredicateTyping E Ξ Γ A ⟨0, .prop⟩)
      (proof : ProofTyping E Ξ Γ H p A) : ProofTyping E Ξ Γ H (.ascribe A p) A
  | eqRefl : ProofTyping E Ξ Γ H .eqRefl reflexivityType
  | eqSubst (motive : PredicateTyping E Ξ Γ P ⟨1, .prop⟩) :
      ProofTyping E Ξ Γ H (.eqSubst P) (substitutionType P)
  | succNeZero : ProofTyping E Ξ Γ H .succNeZero successorNonzeroType
  | succInj : ProofTyping E Ξ Γ H .succInj successorInjectivityType
  | lem (formula : PredicateTyping E Ξ Γ A ⟨0, .prop⟩) :
      ProofTyping E Ξ Γ H (.lem A) (.or A (.imp A .false))
  | induction (motive : PredicateTyping E Ξ Γ P ⟨1, .qf⟩) :
      ProofTyping E Ξ Γ H (.induction P) (inductionType P)
  | conversion (proof : ProofTyping E Ξ Γ H p A)
      (type : PredicateEq E Ξ Γ A B ⟨0, .prop⟩) : ProofTyping E Ξ Γ H p B

/-- Valid proof assumptions in a fixed parameter and local term context. The other context
components contain only intrinsically formed arities and signatures, so need no scope premises. -/
inductive ContextWF (E : Environment) (Ξ : ParameterContext) (Γ : LocalContext) :
    ProofContext → Prop where
  | nil : ContextWF E Ξ Γ []
  | cons (head : PredicateTyping E Ξ Γ A ⟨0, .prop⟩) (tail : ContextWF E Ξ Γ H) :
      ContextWF E Ξ Γ (A :: H)

/-- A declaration is well formed against the preceding map. Bodies have only their own declared
parameters, no local variables or proof assumptions. Freshness is imposed by `EnvironmentWF`. -/
inductive DeclarationWF (E : Environment) : Declaration → Prop where
  | function (body : TermTyping E { functions := d.functions } [] d.body d.arity) :
      DeclarationWF E (.function d)
  | predicate (body : PredicateTyping E
      { functions := d.functions, predicates := d.predicates } [] d.body d.signature) :
      DeclarationWF E (.predicate d)
  | theoremE (type : PredicateTyping E
      { functions := d.functions, predicates := d.predicates } [] d.type ⟨0, .prop⟩)
      (body : ProofTyping E { functions := d.functions, predicates := d.predicates }
        [] [] d.body d.type) : DeclarationWF E (.theoremE d)

/-- Every successful lookup in the smaller map has the same result in the larger map. -/
def EnvironmentExtends (smaller larger : Environment) : Prop :=
  ∀ (name : Lean.Name) (declaration : Declaration),
    smaller[name]? = some declaration → larger[name]? = some declaration

/-- Valid maps are built by fresh, well-formed insertions. Extensional equality makes validity
independent of internal capacity and layout. Fresh insertion prevents replacement, self
reference, and dependency cycles. -/
inductive EnvironmentWF : Environment → Prop where
  | empty : EnvironmentWF ∅
  | insert (previous : EnvironmentWF E) (fresh : E[d.name]? = none)
      (declaration : DeclarationWF E d) : EnvironmentWF (E.insert d.name d)

/-- Each declaration is fresh and well formed against exactly its preceding declarations. -/
public inductive DeclarationsWF : Environment → List Declaration → Environment → Prop
  | nil : DeclarationsWF E [] E
  | cons (fresh : E[d.name]? = none) (formed : DeclarationWF E d)
      (tail : DeclarationsWF (E.insert d.name d) ds F) : DeclarationsWF E (d :: ds) F

/-- A local renaming preserves the arity of every in-scope variable. Parameters are unchanged. -/
def RenamingTyping (source target : LocalContext) (rename : Renaming) : Prop :=
  ∀ i k, source[i]? = some k → target[rename i]? = some k

/-- A simultaneous local substitution replaces each variable by a term of its arity. This
includes function-valued locals; declaration parameters remain unchanged. -/
def SubstitutionTyping (E : Environment) (Ξ : ParameterContext)
    (source target : LocalContext) (subst : Subst) : Prop :=
  ∀ i k, source[i]? = some k → TermTyping E Ξ target (subst i) k

/-- A complete simultaneous instantiation from source parameters to a caller's context.
Local variables of the source expression are handled separately by local substitution. -/
structure InstantiationTyping (E : Environment) (source target : ParameterContext)
    (Γ : LocalContext) (functions : List Term) (predicates : List Predicate) : Prop where
  functions : FunctionArguments E target Γ functions source.functions
  predicates : PredicateArguments E target Γ predicates source.predicates

/-- Pointwise conversion of proof assumptions in a fixed numerical and parameter context,
preserving the hypothesis count and indices. -/
inductive ProofContextEq (E : Environment) (Ξ : ParameterContext) (Γ : LocalContext) :
    ProofContext → ProofContext → Prop where
  | nil : ProofContextEq E Ξ Γ [] []
  | cons (head : PredicateEq E Ξ Γ A B ⟨0, .prop⟩) (tail : ProofContextEq E Ξ Γ H K) :
      ProofContextEq E Ξ Γ (A :: H) (B :: K)

end LeanPRA.Core.Theory
