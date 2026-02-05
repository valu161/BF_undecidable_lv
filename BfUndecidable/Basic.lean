import Mathlib.Data.List.Basic

-- Silence the overly eager linter
-- TBD: Once for all files?
set_option linter.style.cdot false
set_option linter.style.longLine false
set_option linter.style.emptyLine false

/--
Axiomatic characterization of a model of computation that is rich enough
that one can prove by diagonalization that it can't solve its own halting problem.

Comments below indicate the intended semantics of the various fields.
-/
class DiagModel where
  /--
  Type used both for programs and their input. (Think of an "interpreted"
  language).
  -/
  Data : Type

  /-- Proposition asserting that running `prog` on `input` will halt -/
  halts (prog input : Data) : Prop

  /--
  Obtain the return value of `prog` running on `input`, given a proof that it halts.
  (We assume that any return value can be cast into a `Bool`)
  -/
  eval (prog input : Data) (h : halts prog input) : Bool

  /-- Given a program `cond`, construct the program "if cond(input) then run_forver else halt" -/
  if_run_else_halt : Data → Data

  /-- Assert that `if_run_else_halt` has the right semantics if `cond(input)` returns `true` -/
  ireh_runs_of_true (cond : Data) (input : Data) (h : halts cond input) :
      eval cond input h = true → ¬ (halts (if_run_else_halt cond) input)

  /-- Assert that `if_run_else_halt` has the right semantics if `cond(input)` returns `false` -/
  ireh_halts_of_false (cond : Data) (input : Data) (h : halts cond input) :
      eval cond input h = false → halts (if_run_else_halt cond) input


variable {Model : DiagModel}

open DiagModel

/--
A *total program* is one that halts on every input.

The structure `TotalProgram` bundles a program with a proof of totality.
-/
structure TotalProgram where
  prog : Data
  htotal : ∀ input, halts prog input

def eval_total (p : TotalProgram) (input : Data) := eval p.prog input (p.htotal input)

/--
Main result. The model can't decide its own halting problem:
There is no total program that maps exactly those `prog input : Data` to `true`
for which running `prog` with input `input` halts.

In fact, we will show that this problem fails already "on the diagonal" in the
sense that there isn't even a total program that maps exactly those `prog : Data`
to `true` for which running `prog` with input `prog` halts.

Strategy:

Given a candidate for such a decider, we construct a program `spoiler` such that:
- if `candidate spoiler` is true, then `spoiler spoiler` runs forever
- if `candidate spoiler` is false, then `spoiler spoiler` halts
This means that whatever it is that `candidate` does, it certainly doesn't solve
the halting problem, as it gives the wrong answer at least on `spoiler`.

This formalization emphasizes the constructive nature of the proof. For its
(equivalent) formulation as a negation, see below.
-/
theorem halting_undecidable : ∀ candidate, ∃ spoiler,
  (eval_total candidate spoiler = true ∧ ¬halts spoiler spoiler)
  ∨
  (eval_total candidate spoiler = false ∧ halts spoiler spoiler) := by

  intro candidate
  let spoiler := if_run_else_halt candidate.prog
  use spoiler

  by_cases (eval_total candidate spoiler = true)
  ·

    sorry
  ·

    sorry


/-- The more classical formulation of the result as a negation. -/
theorem halting_undecidable_neg_formulation :
  ¬ ∃ decider, ∀ prog, eval_total decider prog = true ↔ halts prog prog := by

  sorry

/-

  Remarks
  =======

-/

/-
The main theorem quantifies over total programs. There are total programs for
which the computational fragment of Lean cannot prove that they are total. ("If
Lean's logic is sound halt, else loop forever", see
https://en.wikipedia.org/wiki/G%C3%B6del%27s_incompleteness_theorems#Second_incompleteness_theorem).
But we can still instantiate an object of type `TotalProgram` for such a
program, by setting `htotal := sorry`. Then `halting_undecidable` applied to the
resulting object will typecheck just fine. Running `#print axioms` on the proof
term will show that it depends on the generic "sorry axiom" `sorryAx`. Hence the
proof should be interpreted as saying that the program doesn't solve the halting
problem, assuming axiomatically that it halts.
-/
