module

public import LeanPRA.Core.Substitution

/-!
# Syntactic weak-head and normal forms

- `TermWhnf` and `PredicateWhnf` exclude reductions at the outermost constructor.
- `TermApplications` and `PredicateApplications` describe neutral heads with uninspected arguments.
- `TermBlocked` excludes the two numerical constructors that trigger primitive recursion.
- `TermNormal` and `TermNeutral` describe beta-normal, eta-long numerical syntax.
- `PredicateNormal` and `PredicateNeutral` describe the corresponding predicate syntax.

These predicates concern syntax at a given arity. Positive arities have the prescribed numerical
lambdas, with anonymous name hints. Normal recursors have a blocked argument, and normal forms
are free of definitions, lets, and beta redexes.
-/

@[expose] public section

namespace LeanPRA.Core.Theory

/-- An argument distinct from `.zero` and `.app .succ u` at the outermost level. -/
def TermBlocked (t : Term) : Prop := t ≠ .zero ∧ ∀ u, t ≠ .app .succ u

/-- Weak-head term syntax, including the uninspected bodies of lambdas and blocked recursors. -/
inductive TermWhnf : Term → Prop where
  | bvar : TermWhnf (.bvar i)
  | parameter : TermWhnf (.parameter i)
  | zero : TermWhnf .zero
  | succ : TermWhnf .succ
  | lam : TermWhnf (.lam binderName t)
  | app (function : TermWhnf f) (notLam : ∀ t n, f ≠ .lam n t) : TermWhnf (.app f a)
  | primrec (argument : TermWhnf a) (blocked : TermBlocked a) : TermWhnf (.primrec b s a)

/-- A local, function parameter, or successor followed by possibly unreduced arguments. -/
inductive TermApplications : Term → Prop where
  | bvar : TermApplications (.bvar i)
  | parameter : TermApplications (.parameter i)
  | succ : TermApplications .succ
  | app (function : TermApplications f) : TermApplications (.app f a)

private theorem applications_not_lam {t} (h : TermApplications t) :
    ∀ u n, t ≠ .lam n u := by
  cases h <;> intro u n heq <;> cases heq

/-- Applications with a neutral head are in weak-head form, independently of their arguments. -/
public theorem TermApplications.whnf {t} (h : TermApplications t) : TermWhnf t := by
  induction h with
  | bvar => exact .bvar
  | parameter => exact .parameter
  | succ => exact .succ
  | app f ih => exact .app ih (applications_not_lam f)

/-- Local renaming preserves the head's kind and the number of applications. -/
public theorem TermApplications.rename {t} (h : TermApplications t) (r : Renaming) :
    TermApplications (t.rename r) := by
  induction h with
  | bvar => simpa only [Term.rename] using (TermApplications.bvar (i := r _))
  | parameter => simpa only [Term.rename] using (TermApplications.parameter (i := _))
  | succ => simpa only [Term.rename] using TermApplications.succ
  | app f ih => simpa only [Term.rename] using (TermApplications.app ih)

mutual

/-- Numerical syntax with all beta/delta/zeta/recursor redexes removed and all arities expanded. -/
inductive TermNormal : Arity → Term → Prop where
  | zero : TermNormal 0 .zero
  | bvar : TermNormal 0 (.bvar i)
  | parameter : TermNormal 0 (.parameter i)
  | app (function : TermNeutral f) (argument : TermNormal 0 a) : TermNormal 0 (.app f a)
  | primrec (base : TermNormal 0 b) (step : TermNormal 2 s) (argument : TermNormal 0 a)
      (blocked : TermBlocked a) : TermNormal 0 (.primrec b s a)
  | lam (body : TermNormal k t) : TermNormal (k + 1) (.lam .anonymous t)

/-- A term application chain headed by a local, a function parameter, or successor. -/
inductive TermNeutral : Term → Prop where
  | bvar : TermNeutral (.bvar i)
  | parameter : TermNeutral (.parameter i)
  | succ : TermNeutral .succ
  | app (function : TermNeutral f) (argument : TermNormal 0 a) : TermNeutral (.app f a)

end

/-- Weak-head predicate syntax; only the function of an application is inspected. -/
inductive PredicateWhnf : Predicate → Prop where
  | false : PredicateWhnf .false
  | true : PredicateWhnf .true
  | equal : PredicateWhnf (.equal a b)
  | imp : PredicateWhnf (.imp A B)
  | and : PredicateWhnf (.and A B)
  | or : PredicateWhnf (.or A B)
  | all : PredicateWhnf (.all P)
  | ex : PredicateWhnf (.ex P)
  | parameter : PredicateWhnf (.parameter i)
  | lam : PredicateWhnf (.lam binderName P)
  | app (function : PredicateWhnf P) (notLam : ∀ Q n, P ≠ .lam n Q) :
      PredicateWhnf (.app P a)

/-- A predicate parameter followed by possibly unreduced numerical arguments. -/
inductive PredicateApplications : Predicate → Prop where
  | parameter : PredicateApplications (.parameter i)
  | app (function : PredicateApplications P) : PredicateApplications (.app P a)

private theorem predicate_applications_not_lam {P} (h : PredicateApplications P) :
    ∀ Q n, P ≠ .lam n Q := by
  cases h <;> intro Q n heq <;> cases heq

/-- Applications of a predicate parameter are in weak-head form. -/
public theorem PredicateApplications.whnf {P} (h : PredicateApplications P) : PredicateWhnf P := by
  induction h with
  | parameter => exact .parameter
  | app P ih => exact .app ih (predicate_applications_not_lam P)

/-- Renaming keeps the predicate parameter and the number of applications. -/
public theorem PredicateApplications.rename {P} (h : PredicateApplications P) (r : Renaming) :
    PredicateApplications (P.rename r) := by
  induction h with
  | parameter => simpa only [Predicate.rename] using (PredicateApplications.parameter (i := _))
  | app P ih => simpa only [Predicate.rename] using (PredicateApplications.app ih)

mutual

/-- Beta-normal, eta-long predicate syntax, with normal numerical subexpressions. -/
inductive PredicateNormal : Arity → Predicate → Prop where
  | false : PredicateNormal 0 .false
  | true : PredicateNormal 0 .true
  | equal (left : TermNormal 0 a) (right : TermNormal 0 b) : PredicateNormal 0 (.equal a b)
  | imp (left : PredicateNormal 0 A) (right : PredicateNormal 0 B) : PredicateNormal 0 (.imp A B)
  | and (left : PredicateNormal 0 A) (right : PredicateNormal 0 B) : PredicateNormal 0 (.and A B)
  | or (left : PredicateNormal 0 A) (right : PredicateNormal 0 B) : PredicateNormal 0 (.or A B)
  | all (body : PredicateNormal 1 P) : PredicateNormal 0 (.all P)
  | ex (body : PredicateNormal 1 P) : PredicateNormal 0 (.ex P)
  | parameter : PredicateNormal 0 (.parameter i)
  | app (function : PredicateNeutral P) (argument : TermNormal 0 a) :
      PredicateNormal 0 (.app P a)
  | lam (body : PredicateNormal k P) : PredicateNormal (k + 1) (.lam .anonymous P)

/-- A predicate application chain headed by a predicate parameter. -/
inductive PredicateNeutral : Predicate → Prop where
  | parameter : PredicateNeutral (.parameter i)
  | app (function : PredicateNeutral P) (argument : TermNormal 0 a) :
      PredicateNeutral (.app P a)

end

end LeanPRA.Core.Theory
