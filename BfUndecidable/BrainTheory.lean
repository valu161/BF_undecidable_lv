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
 unfold step --at first replace step with its def.
 by_cases hpos : b.progPos < b.prog.length --then 'undo' the if condition
 · simp [hpos] ; split  --after 'undoing' split the function into
                       --its match branches, because '[', ']' are too complex for tactics
   · rfl  --rfl works here, because its def. equality
   · rfl
   · rfl
   · rfl
   · split <;> rfl --after spliting into cases its the same here
   · split <;> rfl
   · simp
   · simp
   · simp
 ·simp [hpos]




lemma prog_immutable_steps {b k} : (step^[k] b).prog = b.prog := by
  induction k with
  | zero =>rfl
  | succ k ih =>
    have h1:  step^[k + 1] b = step (step^[k] b) := by simp [Function.iterate_succ_apply']
    have h2: (step (step^[k] b)).prog = (step^[k] b).prog := by simp [prog_immutable_step]
    have h3 : (step^[k] b).prog = b.prog := ih
    rw [h1, h2, h3]



lemma prog_immutable_execute (p a n) : (execute p a n).prog = p := by
  unfold execute
  use prog_immutable_steps

/-
  Matching brackets lie within `prog`.
-/

lemma matchingOpen_lt (p : Data) (pos : Nat) (depth : Nat) (c : Nat) (h : pos < p.length) :
  matchingOpen p pos depth = some c → c < p.length := by
    unfold matchingOpen -- Substitute matchingOpen with it's definition
    split -- split the if pos = 0…
    · split -- Now the if prog[p] = '[' || depth = 0
      · intro c_eq_0 -- Get the assumption about c from the inference
        -- Apply injectivity of some (soma a = some b <=> a = b) to all goals and hypotheses.
        simp_all only [Option.some.injEq]
        subst c_eq_0 -- substitute c with 0 since they're equal
        simp_all -- simplify everthing to make lean believe we proved this subgoal
      · intro a
        -- ^ a stands for 'absurd' :P
        --   (But really this does the same as the intro above only with a different outcome)
        exfalso -- Let's us prove anything as long as we can construct false
        simp_all -- make lean see that we can construct false out of none = some
    · split -- split the match 
      ·  apply matchingOpen_lt -- Recursion, yay!
      ·  split -- Split the if depth = 0
         · intro pos_eq_c -- This is mostly parallel to something above
           simp_all only [Option.some.injEq]
           subst pos_eq_c
           apply h -- Our goal matches h, so we can just apply it
         · apply matchingOpen_lt -- Recursion, again…
      ·  apply matchingOpen_lt -- …and again!

lemma matchingClose_lt (p : Data) (pos : Nat) (depth : Nat) (c : Nat) :
  matchingClose p pos depth = some c → c <  p.length := by
    unfold matchingClose
    split -- Here, we can get h from the definition (kinda, see below)
    ·  split -- match…
       · apply matchingClose_lt -- Recursion, yet again, I'll stop saying it now
       · split -- if depth = 0…
         · intro pos_eq_c
           simp_all only [Option.some.injEq] -- This has been explained in matchingOpen_lt
           subst pos_eq_c
           rename_i h _ _ _ -- This is where we *really* get h!
           apply h
         · apply matchingClose_lt
       · apply matchingClose_lt
    · intro a -- again, some = none so a for absurd…
      exfalso
      simp_all


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
