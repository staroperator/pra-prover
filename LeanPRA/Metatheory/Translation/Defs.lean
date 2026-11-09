module

public import LeanPRA.Metatheory.Core.Judgement.Defs
public import LeanPRA.Metatheory.PRA.Defs

/-!
# Relational translation to first-order PRA

Relational translation from the typed PRA language to the first-order theory of PRA:

- `Fin.embedLeft`, `Fin.succAdd`, and `Fin.moveToFront` reindex argument and local-variable
  blocks.
- `FunctionAssignment` and `PredicateAssignment` assign primitive recursive expressions and
  first-order formulas to declaration parameters at their declared arities and signatures.
- `TermTranslation` translates a term of arity `k` under `n` numerical local variables to a
  `Primrec (k + n)`.
- `PredicateTranslation` translates a predicate of signature `σ` under `n` numerical local
  variables to a `PRA.Formula (σ.arity + n)`.
- `FunctionArgumentsTranslation` and `PredicateArgumentsTranslation` translate argument lists for
  parameterized declarations.
- `TranslatedDeclaration` and `DeclarationTranslation` translate closed function, predicate, and
  theorem declarations to target schemas, requiring `PRA.Proof` for every instance of a theorem.

In `TermTranslation` and `PredicateTranslation`, the `k` remaining argument inputs precede the `n`
local variables (ordered from innermost to outermost). Lambda abstraction moves the first argument
input to local variable `0`, and application supplies the first argument input by composition or
substitution. Let-bindings and global references unfold their bodies by source substitution and
parameter instantiation.
-/

@[expose] public section

namespace Fin

/-- Embed the first block of `Fin (k + n)`, preserving the index's numerical value. -/
def embedLeft {k n : Nat} (i : Fin k) : Fin (k + n) :=
  (i.rev.addNat n).rev

/-- Map `(k + 1) + n` positions to `(k + n) + 1` positions without changing their values. -/
def succAdd {k n : Nat} : Fin ((k + 1) + n) → Fin ((k + n) + 1) :=
  Fin.addCases (Fin.cases 0 (fun i => (embedLeft i).succ))
    (fun i => (i.natAdd k).succ)

/-- Move position `k` to zero, shift earlier positions by one, and keep later positions fixed. -/
def moveToFront {k n : Nat} : Fin (k + (n + 1)) → Fin ((k + 1) + n) :=
  Fin.addCases (fun i => embedLeft i.succ)
    (Fin.cases (embedLeft 0) (Fin.natAdd (k + 1)))

end Fin

namespace LeanPRA.Translation

open Core Core.Theory

/-- Assign a primitive-recursive expression to each function parameter at its declared arity. -/
abbrev FunctionAssignment (arities : List Arity) :=
  (i k : Nat) → arities[i]? = some k → Primrec k

/-- Assign formulas to predicate parameters at their declared arities and QF restrictions. -/
abbrev PredicateAssignment (signatures : List PredicateSignature) :=
  (i : Nat) → (σ : PredicateSignature) → signatures[i]? = some σ →
    {A : PRA.Formula σ.arity // σ.sort = .qf → A.QuantifierFree}

def FunctionAssignment.empty : FunctionAssignment [] :=
  fun _ _ h => by simp at h

def PredicateAssignment.empty : PredicateAssignment [] :=
  fun _ _ h => by simp at h

mutual

/-- Translate a term of arity `k` under `n` numerical local variables to a `Primrec (k + n)`,
with the `k` argument inputs preceding the `n` local variables. -/
inductive TermTranslation (E : Environment) (Ξ : ParameterContext)
    (ρ : FunctionAssignment Ξ.functions) :
    (n : Nat) → Term → (k : Arity) → Primrec (k + n) → Prop where
  | bvar (i : Fin n) :
      TermTranslation E Ξ ρ n (.bvar i.val) 0 (.proj (i.natAdd 0))
  | zero : TermTranslation E Ξ ρ n .zero 0 (Primrec.comp₀ .zero)
  | succ : TermTranslation E Ξ ρ n .succ 1 (Primrec.reindex .succ Fin.embedLeft)
  | parameter (lookup : Ξ.functions[i]? = some k) :
      TermTranslation E Ξ ρ n (.parameter i) k (Primrec.reindex (ρ i k lookup) Fin.embedLeft)
  | lam (body : TermTranslation E Ξ ρ (n + 1) t k f) :
      TermTranslation E Ξ ρ n (.lam name t) (k + 1) (Primrec.reindex f Fin.moveToFront)
  | app (function : TermTranslation E Ξ ρ n t (k + 1) f)
      (argument : TermTranslation E Ξ ρ n u 0 g) :
      TermTranslation E Ξ ρ n (.app t u) k
        (.comp f (fun i => Fin.cases
          (Primrec.reindex g (Fin.addCases Fin.elim0 (Fin.natAdd k)))
          Primrec.proj (Fin.succAdd i)))
  | letE (value : TermTranslation E Ξ ρ n t j g)
      (body : TermTranslation E Ξ ρ n (u.subst0 t) k f) :
      TermTranslation E Ξ ρ n (.letE name t u) k f
  | primrec (base : TermTranslation E Ξ ρ n b 0 f)
      (step : TermTranslation E Ξ ρ n s 2 g) :
      TermTranslation E Ξ ρ n (.primrec b s) 1
        (Primrec.reindex (.prec f (Primrec.reindex g
          (fun i => Fin.cases 0 (fun j => (Fin.succAdd j).succ) (Fin.succAdd i))))
          (Fin.cases (Fin.embedLeft 0) (Fin.addCases Fin.elim0 (Fin.natAdd 1))))
  | definition {n : Nat} {d : FunctionDefinition} {f : Primrec (d.arity + n)}
      (lookup : E[name]? = some (.function d))
      (arguments : FunctionArgumentsTranslation E Ξ ρ n fs d.functions)
      (body : TermTranslation E Ξ ρ n (d.body.instantiate fs) d.arity f) :
      TermTranslation E Ξ ρ n (.definition name fs) d.arity f

/-- Translate every function actual at its declared arity, including its captured locals. -/
inductive FunctionArgumentsTranslation (E : Environment) (Ξ : ParameterContext)
    (ρ : FunctionAssignment Ξ.functions) : Nat → List Term → List Arity → Prop where
  | nil : FunctionArgumentsTranslation E Ξ ρ n [] []
  | cons (head : TermTranslation E Ξ ρ n t k f)
      (tail : FunctionArgumentsTranslation E Ξ ρ n ts ks) :
      FunctionArgumentsTranslation E Ξ ρ n (t :: ts) (k :: ks)

end

mutual

/-- Translate a predicate of signature `σ` under `n` numerical local variables to a
`PRA.Formula (σ.arity + n)`, with the `σ.arity` argument inputs preceding the `n` local
variables. -/
inductive PredicateTranslation (E : Environment) (Ξ : ParameterContext)
    (ρ : FunctionAssignment Ξ.functions) (π : PredicateAssignment Ξ.predicates) :
    (n : Nat) → Predicate → (σ : PredicateSignature) → PRA.Formula (σ.arity + n) → Prop where
  | false : PredicateTranslation E Ξ ρ π n .false ⟨0, s⟩ .false
  | true : PredicateTranslation E Ξ ρ π n .true ⟨0, s⟩ .true
  | equal (left : TermTranslation E Ξ ρ n t 0 f)
      (right : TermTranslation E Ξ ρ n u 0 g) :
      PredicateTranslation E Ξ ρ π n (.equal t u) ⟨0, s⟩
        (.eq (.app f PRA.Term.var) (.app g PRA.Term.var))
  | imp (left : PredicateTranslation E Ξ ρ π n P ⟨0, s⟩ A)
      (right : PredicateTranslation E Ξ ρ π n Q ⟨0, s⟩ B) :
      PredicateTranslation E Ξ ρ π n (.imp P Q) ⟨0, s⟩ (.imp A B)
  | and (left : PredicateTranslation E Ξ ρ π n P ⟨0, s⟩ A)
      (right : PredicateTranslation E Ξ ρ π n Q ⟨0, s⟩ B) :
      PredicateTranslation E Ξ ρ π n (.and P Q) ⟨0, s⟩ (.and A B)
  | or (left : PredicateTranslation E Ξ ρ π n P ⟨0, s⟩ A)
      (right : PredicateTranslation E Ξ ρ π n Q ⟨0, s⟩ B) :
      PredicateTranslation E Ξ ρ π n (.or P Q) ⟨0, s⟩ (.or A B)
  | all (body : PredicateTranslation E Ξ ρ π n P ⟨1, .prop⟩ A) :
      PredicateTranslation E Ξ ρ π n (.all P) ⟨0, .prop⟩
        (.all (A.subst (fun i => .var (Fin.succAdd i))))
  | ex (body : PredicateTranslation E Ξ ρ π n P ⟨1, .prop⟩ A) :
      PredicateTranslation E Ξ ρ π n (.ex P) ⟨0, .prop⟩
        (.ex (A.subst (fun i => .var (Fin.succAdd i))))
  | parameter (lookup : Ξ.predicates[i]? = some σ)
      (sort : σ.sort = .qf ∨ σ.sort = s) :
      PredicateTranslation E Ξ ρ π n (.parameter i) ⟨σ.arity, s⟩
        ((π i σ lookup).val.subst (fun i => .var (Fin.embedLeft i)))
  | lam (body : PredicateTranslation E Ξ ρ π (n + 1) P ⟨k, s⟩ A) :
      PredicateTranslation E Ξ ρ π n (.lam name P) ⟨k + 1, s⟩
        (A.subst (fun i => .var (Fin.moveToFront i)))
  | app (function : PredicateTranslation E Ξ ρ π n P ⟨k + 1, s⟩ A)
      (argument : TermTranslation E Ξ ρ n t 0 f) :
      PredicateTranslation E Ξ ρ π n (.app P t) ⟨k, s⟩
        (A.subst (fun i => Fin.cases
          (.app (Primrec.reindex f (Fin.addCases Fin.elim0 (Fin.natAdd k))) PRA.Term.var)
          PRA.Term.var (Fin.succAdd i)))
  | letTerm (value : TermTranslation E Ξ ρ n t j f)
      (body : PredicateTranslation E Ξ ρ π n P σ A) :
      PredicateTranslation E Ξ ρ π n (.letTerm name t P) σ A
  | letPredicate (value : PredicateTranslation E Ξ ρ π n Q τ B)
      (body : PredicateTranslation E Ξ ρ π n P σ A) :
      PredicateTranslation E Ξ ρ π n (.letPredicate name Q P) σ A
  | definition {n : Nat} {d : PredicateDefinition}
      {A : PRA.Formula (d.signature.arity + n)} (lookup : E[name]? = some (.predicate d))
      (functions : FunctionArgumentsTranslation E Ξ ρ n fs d.functions)
      (predicates : PredicateArgumentsTranslation E Ξ ρ π n ps d.predicates)
      (body : PredicateTranslation E Ξ ρ π n (d.body.instantiate fs ps) d.signature A)
      (sort : d.signature.sort = .qf ∨ d.signature.sort = s) :
      PredicateTranslation E Ξ ρ π n (.definition name fs ps) ⟨d.signature.arity, s⟩ A

/-- Translate every predicate actual at its declared signature, including its captured locals. -/
inductive PredicateArgumentsTranslation (E : Environment) (Ξ : ParameterContext)
    (ρ : FunctionAssignment Ξ.functions) (π : PredicateAssignment Ξ.predicates) :
    Nat → List Predicate → List PredicateSignature → Prop where
  | nil : PredicateArgumentsTranslation E Ξ ρ π n [] []
  | cons (head : PredicateTranslation E Ξ ρ π n P σ A)
      (tail : PredicateArgumentsTranslation E Ξ ρ π n ps signatures) :
      PredicateArgumentsTranslation E Ξ ρ π n (P :: ps) (σ :: signatures)

end

/-- Target declaration schemas with explicit parameter arities and result signatures.
Theorem entries contain the translated statements. -/
inductive TranslatedDeclaration where
  | function (name : Lean.Name) (parameters : List Arity) (arity : Arity)
      (body : FunctionAssignment parameters → Primrec arity)
  | predicate (name : Lean.Name) (parameters : ParameterContext) (signature : PredicateSignature)
      (body : FunctionAssignment parameters.functions → PredicateAssignment parameters.predicates →
        PRA.Formula signature.arity)
  | theoremE (name : Lean.Name) (parameters : ParameterContext)
      (body : FunctionAssignment parameters.functions → PredicateAssignment parameters.predicates →
        PRA.Formula 0)

/-- Translate a closed declaration to a schema over parameter assignments. Function and predicate
declarations translate their bodies; theorem declarations translate their statements and require a
first-order PRA proof for every parameter assignment. -/
inductive DeclarationTranslation (E : Environment) : Declaration → TranslatedDeclaration → Prop
  | function {d : FunctionDefinition}
      {f : FunctionAssignment d.functions → Primrec d.arity}
      (body : ∀ ρ, TermTranslation E { functions := d.functions } ρ 0 d.body d.arity (f ρ)) :
      DeclarationTranslation E (.function d) (.function d.name d.functions d.arity f)
  | predicate {d : PredicateDefinition}
      {A : FunctionAssignment d.functions → PredicateAssignment d.predicates →
        PRA.Formula d.signature.arity}
      (body : ∀ ρ π, PredicateTranslation E
        { functions := d.functions, predicates := d.predicates } ρ π 0
        d.body d.signature (A ρ π)) :
      DeclarationTranslation E (.predicate d)
        (.predicate d.name { functions := d.functions, predicates := d.predicates } d.signature A)
  | theoremE {d : TheoremDefinition}
      {A : FunctionAssignment d.functions → PredicateAssignment d.predicates → PRA.Formula 0}
      (type : ∀ ρ π, PredicateTranslation E
        { functions := d.functions, predicates := d.predicates } ρ π 0 d.type ⟨0, .prop⟩ (A ρ π))
      (proof : ∀ ρ π, PRA.Proof (A ρ π)) :
      DeclarationTranslation E (.theoremE d)
        (.theoremE d.name { functions := d.functions, predicates := d.predicates } A)

end LeanPRA.Translation
