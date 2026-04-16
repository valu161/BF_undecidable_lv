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
  (We assume that any return value can be cast into a `Bool` we just use programms in our proove,
  that return `true` or `false`. any other programm can just randomly be mapped to true or false
  )
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


variable {Model : DiagModel} -- everything takes diag modell as implicit input (we are working conditional on having such a model)

open DiagModel

/--
A *total program* is one that halts on every input.

The structure `TotalProgram` bundles a program with a proof of totality.
-/
structure TotalProgram where
  prog : Data
  htotal : ∀ input, halts prog input

def eval_total (p : TotalProgram) (input : Data) := eval p.prog input (p.htotal input)
/- hier ist input nicht teil der struktur, weil es darum geht, dass in der struktur nur das programm
beschrieben wird. Es soll eben für alle inputs halten nicht für ein spezifisches.
 Diagmodell bleibt offen, darum weiß lean den Type von input und was halts ist, man muss input nicht in
 struture spezifizieren-/
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
(equivalent) formulation as a negation, see below. -/




theorem halting_undecidable : ∀ candidate, ∃ spoiler,
  (eval_total candidate spoiler = true ∧ ¬halts spoiler spoiler)
  ∨
  (eval_total candidate spoiler = false ∧ halts spoiler spoiler) := by
intro candidate
let spoiler := if_run_else_halt candidate.prog --this is the name of the programm from the tot. programm sturcture
use spoiler
by_cases hctrue : (eval_total candidate spoiler = true) --split the proof into two cases
--either eval total is true or it is not true, now we can use the ireh_runs... and ireh_halts
--instances because we have all of their arguments.
· have hnothalts : ¬ halts spoiler spoiler :=
    ireh_runs_of_true candidate.prog spoiler (candidate.htotal spoiler) hctrue --the ireh_... instances
    --give us terms of the type we are searching
  exact Or.inl ⟨hctrue, hnothalts⟩ --we construct an And-therm out of hctrue and hnothalts
  --and use it as an argument for the Or- constructor

· have hfalse : eval_total candidate spoiler = false :=
    by simp [hctrue] --at first we have to bring it to the correct form using ¬ true = false
  have hhalts :  halts spoiler spoiler :=
   ireh_halts_of_false candidate.prog spoiler (candidate.htotal spoiler) hfalse
  exact Or.inr ⟨hfalse, hhalts⟩ --samae as before


lemma evalistureorfalse (cond : Data) (input : Data) (h : halts cond input) : eval cond input h = true ∨ eval cond input h = false := by
--if we don´t want to use by cases: (It does not really matter but I think in the
--previous proof we used LEM using by_cases, which we don´t need to)
have trueorfalse (b:Bool) : b = true ∨ b = false := by
  cases b
  · exact Or.inr rfl
  · exact Or.inl rfl
exact trueorfalse (eval cond input h)

theorem halting_undecidable_without_bycases : ∀ candidate, ∃ spoiler,
  (eval_total candidate spoiler = true ∧ ¬halts spoiler spoiler)
  ∨
  (eval_total candidate spoiler = false ∧ halts spoiler spoiler) := by
intro candidate
let spoiler := if_run_else_halt candidate.prog --this is the name of the programm from the tot. programm sturcture
use spoiler
have trueorfalse :  eval_total candidate spoiler = true ∨ eval_total candidate spoiler = false :=
 evalistureorfalse candidate.prog spoiler (candidate.htotal spoiler) --construct an Or-therm on which we
 --can do a case analysis, therest stays the same as above
cases trueorfalse with
| inl htrue =>
  have hnothalts : ¬ halts spoiler spoiler :=
    ireh_runs_of_true candidate.prog spoiler (candidate.htotal spoiler) htrue
  exact Or.inl ⟨htrue, hnothalts⟩
| inr hfalse =>
  have hhalts :  halts spoiler spoiler :=
   ireh_halts_of_false candidate.prog spoiler (candidate.htotal spoiler) hfalse
  exact Or.inr ⟨hfalse, hhalts⟩



/-- The more classical formulation of the result as a negation. -/
theorem halting_undecidable_neg_formulation :
  ¬ ∃ decider, ∀ prog, eval_total decider prog = true ↔ halts prog prog := by
  intro (h :  ∃ decider, ∀ prog, eval_total decider prog = true ↔ halts prog prog)
  match h with
  | ⟨decider, hdecider⟩ => --Exist constructor has two arguments
  let spoiler := if_run_else_halt decider.prog --as above
  have trueorfalse :  eval_total decider spoiler = true ∨ eval_total decider spoiler = false :=
   evalistureorfalse decider.prog spoiler (decider.htotal spoiler)
   -- I wanted to do it the same way as the previous proof but it turned out to be unnecessary
   --complicated... but it works
  cases trueorfalse with
  | inl htrue =>
    have hneghalts : eval_total decider spoiler = true -> ¬ halts spoiler spoiler :=
    ireh_runs_of_true decider.prog spoiler (decider.htotal spoiler)
    -- use ireh_... to get a not halts hypothesis (with htrue a scondition)
    --
    have hhalts : eval_total decider spoiler = true -> halts spoiler spoiler := by
     cases (hdecider spoiler) with --eliminate the <-> to get the halts hypothesis
     | intro hpq hqp => exact (hpq)
    --
    --
    have hnothalts : ¬ halts spoiler spoiler := hneghalts htrue
    have hhalts : halts spoiler spoiler := hhalts htrue
    exact hnothalts hhalts
  | inr hfalse =>
  --we have to construct a contradiction again
  have hnottrue: ¬ eval_total decider spoiler = true := by
   simp_all --if its false it is not true
   --
   --now I use the other argument (<-) of the '<->'constructor to construct a contradiction
  have hactuallytrue : eval_total decider spoiler = true := by
   cases (hdecider spoiler) with
   | intro hpq hqp => exact (hqp (ireh_halts_of_false decider.prog spoiler (decider.htotal spoiler) hfalse))
  exact hnottrue hactuallytrue





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
