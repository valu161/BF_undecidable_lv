/-
Copyright (c) 2025 David Gross, Davood Therani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross, Davood Therani
-/
import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Find
import BfUndecidable.Interpreter

lemma step_execute {p d n} : execute p d (n + 1) = step (execute p d n) := by
  simp [execute, Function.iterate_succ_apply']

/-
  `prog` is immutable.
-/

lemma prog_immutable_step {b} : (step b).prog = b.prog := by
  sorry

lemma prog_immutable_steps {b k} : (step^[k] b).prog = b.prog := by
  sorry

@[simp]
lemma prog_immutable_execute (p a n) : (execute p a n).prog = p := by
  sorry

/-
  Matching brackets lie within `prog`.
-/

lemma matchingOpen_lt (p : Data) (pos : Nat) (depth : Nat) (c : Nat) (h : pos < p.length) :
  matchingOpen p pos depth = some c → c < p.length := by
    sorry

lemma matchingClose_lt (p : Data) (pos : Nat) (depth : Nat) (c : Nat) :
  matchingClose p pos depth = some c → c <  p.length := by
    sorry


/--
The instruction pointer moves at most one place beyond `prog`.
-/
lemma progPos_le (p a) (n) : (execute p a n).progPos ≤ p.length := by
  sorry

/--
Before the program has halted, the instruction pointer stays within `prog`
-/
lemma progPos_lt_find {p d : Data} {n : ℕ} (h : halts p d) (hn : n < Nat.find h) :
    (execute p d n).progPos < p.length := by
  sorry

/-

  A program that has halted will remain halted.

-/

lemma halts_step {p a n} (h : halted_at p a n) : halted_at p a (n + 1) := by
  sorry

lemma halts_gt {p a n m} (hm : n < m) (h : halted_at p a n) : halted_at p a m := by
  sorry

/--
BF allows for a simple construction that turns a program `cond` into

  if (cond) then loop forever else halt

Just append "[]" to cond.
-/
abbrev ireh_extend (cond : Data) : Data := cond ++ ['[',']']

/-
We now need to prove that the extension doesn't interfere with the execution
of the original program.
-/

lemma extension_body_irrelevance (prog : Data) (pos : Nat) (hpos : pos < prog.length := by omega) :
  prog.get ⟨pos, hpos⟩ = (ireh_extend prog).get ⟨pos, by simp; omega⟩ := by sorry

lemma extension_matching_open_irrelevance
    (prog : Data) (pos : Nat) (depth : Nat) (hpos : pos < prog.length) :
    matchingOpen prog pos depth hpos =
    matchingOpen (ireh_extend prog) pos depth (by simp; omega) := by
  sorry

-- simp_all [matchingClose] introduces Classica.choice. TBD. reduceIte, reduceDIte?
--
-- Interesting:
-- https://proofassistants.stackexchange.com/questions/1115/how-usable-is-lean-for-constructive-mathematics
lemma extension_matching_close_irrelevance
    (prog : Data) (pos : Nat) (depth : Nat) (hpos : pos ≤ prog.length) :
    matchingClose prog pos depth
    =
    matchingClose (ireh_extend prog) pos depth := by
  sorry

/-
  Executing a program commutes with extending it.
-/

lemma step_extend_commute {b : BrainState}
    (hb : b.progPos < b.prog.length) :
    { (step b) with prog := ireh_extend b.prog } =
    step { b with prog := ireh_extend b.prog } := by
  sorry

/-
TBD: Feels a bit too long, given that it's just inducting over `step_comm`.
-/
lemma execute_extend_commute {p d : Data} {n : ℕ}
     (h : halts p d) (hn : n ≤ Nat.find h) :
     {execute p d n with prog := ireh_extend p} = execute (ireh_extend p) d n := by
  sorry

/--
State of `if cond(input) then loop_forever else halt` after executing `cond(input)`.
-/
lemma ireh_cond_state
    (cond : Data) (input : Data) (h : halts cond input) (b : BrainState)
    (hb : b = execute (ireh_extend cond) (input) (Nat.find h)) :
    (b.progPos = cond.length) ∧ ((b.mem[b.memPos]? != some 0) = eval h) :=
  by
    sorry

/--
If `cond input` evaluates to `false`, then

  `if cond(input) then loop_forever else halt`

will halt.
-/
theorem ireh_halts_of_false
    (cond : Data) (input : Data) (h : halts cond input)
    (hret : eval h = false) : halts (ireh_extend cond) input := by
  sorry


/--
If `cond input` evaluates to `true`, then

  `if cond(input) then run_forever else halt`

will not halt.
-/
theorem ireh_runs_of_true (cond : Data) (input : Data) (h : halts cond input)
    (hret : eval h = true) : ¬ halts (ireh_extend cond) input := by
  sorry

  have hm : matchingOpen (ireh_extend cond) (cond.length) 0 (by simp) = some (cond.length) := by
    sorry


/-

  BF is undecidable
  =================

  We now show that BF is an instance of `DiagModel`. We have proven before that
  a computational model that satisfies these properties cannot decide its own
  halting problem.

  Also, because it is known that BF is Turing complete, the Church-Turing thesis
  implies that *no* computational process that is physically realizable can
  decide the halting problem of BF. (We do not prove Turing completeness here).

-/

instance BrainFuck : DiagModel where
  Data := Data
  halts := halts
  eval := @eval
  if_run_else_halt := ireh_extend
  ireh_halts_of_false := ireh_halts_of_false
  ireh_runs_of_true := ireh_runs_of_true
