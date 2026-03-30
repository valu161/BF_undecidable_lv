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
   · rfl
   · rfl
   · rfl
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
  induction n with  --induction over n
  | zero =>
   unfold execute ; simp --if we do nothing, then the instruction pointer is at 0,
                          --which is less than or equal to the length of the program
  | succ n ih => /-show that step does not move the instruction pointer more than one
  place beyond the program extract step becase we have to show what it does-/
  have h1: (execute p a (n + 1)) = step (execute p a (n))
  := by unfold execute ; simp [Function.iterate_succ_apply'] --execute is defined by iterate
  rw [h1] --extract step
  unfold step --okay, lets go 0`_´0
  by_cases hpos : (execute p a (n)).progPos < (execute p a (n)).prog.length --undo if condition
  · simp? [hpos]
    have h2 : (execute p a (n)).prog.length = p.length :=
     by simp [prog_immutable_execute p a (n)] --use it rewrite goal to be able to use hpos
    split
    ·simp? ; rw [← h2] ; exact Nat.succ_le_of_lt hpos
    /- if I forget what the lemma does, swipe over it -/
    ·simp? ; rw [← h2] ; exact Nat.succ_le_of_lt hpos
    ·simp? ; rw [← h2] ; exact Nat.succ_le_of_lt hpos
    ·simp? ; rw [← h2] ; exact Nat.succ_le_of_lt hpos
    ·split   --damn. the brackets again
     case h_1 x_1 x_2 x_3 x_4 x_5 x_6  => --give the new hypotheses names
      simp? ; rw [← h2]
      have almost : x_4 < List.length (execute p a n).prog :=
      --thats not elegant but it works. (bec. matching close_lt gives <, but we need ≤)
      matchingClose_lt (execute p a (n)).prog ((execute p a n).progPos+1) 0 x_4 x_5
      exact Nat.succ_le_of_lt almost
     case h_2 x_1 x_2 x_3 x_4 => rw [← h2] ;exact Nat.succ_le_of_lt hpos
     --(case h2 just does progpos +1)
    ·split --now kind of the same for matching open
     case h_1 x_1 x_2 x_3 x_4 x_5  =>
      simp? ; rw [<- h2]
      have ih01: (execute p a n).progPos - 1 < (execute p a n).prog.length := by omega
      --(no idea why omega works, who tells lean that prog.length is not 0? but ok)
      have almost : x_3 < List.length (execute p a n).prog :=
                   matchingOpen_lt (execute p a n).prog ((execute p a n).progPos-1 ) 0 x_3 ih01 x_4
      exact Nat.succ_le_of_lt almost
     case h_2 x_1 x_2 x_3 x_4 => rw [← h2] ;exact Nat.succ_le_of_lt hpos
    ·  simp? ; rw [← h2] ; exact Nat.succ_le_of_lt hpos
    ·  simp? ; rw [← h2] ; exact Nat.succ_le_of_lt hpos
    ·  simp? ; rw [← h2] ; exact Nat.succ_le_of_lt hpos
  · simp? [hpos]
    exact ih --step does nothing, so we can use the induction hypothesis



/-
Before the program has halted, the instruction pointer stays within `prog`
-/
lemma progPos_lt_find {p d : Data} {n : ℕ} (h : halts p d) (hn : n < Nat.find h) :
    (execute p d n).progPos < p.length := by
  have hprogpos : (execute p d n).progPos ≤ p.length := progPos_le p d n
  by_cases hpos : (execute p d n).progPos < p.length
  · exact hpos
  · have hprogpos_eq : halted_at p d n := by omega
    have contra : ¬ halted_at p d n := Nat.find_min h hn
    contradiction


/-

  A program that has halted will remain halted.

-/

lemma halts_step {p a n} (h : halted_at p a n) : halted_at p a (n + 1) := by
  unfold halted_at at h ⊢
  have h1: (execute p a (n + 1)) = step (execute p a (n))
  := by unfold execute ; simp [Function.iterate_succ_apply'] --execute is defined by iterate
  rw [h1] --extract step
  unfold step
  have hcomeon : ¬ (execute p a n).progPos < (execute p a n).prog.length := by
      have hsimp : List.length p = List.length (execute p a n).prog :=
        by simp [prog_immutable_execute p a n]
      simp [hsimp] at h
      intro contra
      omega
  simp?[hcomeon]
  exact h




lemma halts_gt {p a n m} (hm : n < m) (h : halted_at p a n) : halted_at p a m := by
  -- This makes for a more useful start for the induction
  let k := m - n - 1; let hk : k = m - n - 1 := by rfl
  have hkm : m = (n + k).succ := by omega
  rw [hkm] -- rewrite in terms of k
  induction k with -- This isn't too complicated…
  | zero =>
    simp only [Nat.add_zero, Nat.succ_eq_add_one]
    apply halts_step
    exact h
  | succ =>
    simp only [Nat.succ_eq_add_one]
    rename_i halted_before
    rw [<- Nat.add_assoc]
    apply halts_step
    exact halted_before

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
  prog.get ⟨pos, hpos⟩ = (ireh_extend prog).get ⟨pos, by simp; omega⟩ := by
  simp_all

lemma extension_matching_open_irrelevance
    (prog : Data) (pos : Nat) (depth : Nat) (hpos : pos < prog.length) :
    matchingOpen prog pos depth hpos =
    matchingOpen (ireh_extend prog) pos depth (by simp; omega) := by
    unfold matchingOpen -- replace by definition

    -- Simplify all goals and hypotheses using just the facts that:
    -- list.get i = list[i] and for any i < listA.length: listA[i] = (listA + listB)[i]
    simp_all only [List.get_eq_getElem, List.getElem_append_left]
    split -- Split if pos = 0 on both sides of the equality
    · simp_all -- Simplify to make lean see the equality we get here is true…
    · split -- Split the match on the left side
      · simp_all only -- As it turns out, all cases evaluate to the same here…

        -- …so we can talk to our old friend recursion again
        apply extension_matching_open_irrelevance
      · simp_all only -- Here again, the cases are all the same…
        split -- …but we end up with an 'if' to split
        · simp_all only -- Simp the some pos = some pos so lean gets it
        · apply extension_matching_open_irrelevance -- And now recurse, recurse, recurse!
      · apply extension_matching_open_irrelevance

-- simp_all [matchingClose] introduces Classica.choice. TBD. reduceIte, reduceDIte?
--
-- Interesting:
-- https://proofassistants.stackexchange.com/questions/1115/how-usable-is-lean-for-constructive-mathematics
lemma extension_matching_close_irrelevance
    (prog : Data) (pos : Nat) (depth : Nat) (hpos : pos ≤ prog.length) :
    matchingClose prog pos depth
    =
    matchingClose (ireh_extend prog) pos depth := by
    -- Ok, so this one is a bit lengthy… Sorry in advance!
    -- I have an inkling that I could have shortened at least the first part
    -- using matchingclose_lt, but I didn't see the way to tell lean…
    unfold ireh_extend
    unfold matchingClose
    -- Honestly, this is the result of followng what `simp_all?` told me…
    -- I don't really like it but the linter insisted on doing it this way
    -- and I want my context to be as readable as possible!
    simp_all only [List.get_eq_getElem, ↓Char.isValue, List.pure_def, List.bind_eq_flatMap,
      List.flatMap_cons, Char.reduceToNat, List.flatMap_nil, List.append_nil, List.cons_append,
      List.nil_append, List.length_append, List.length_cons, List.length_nil, Nat.zero_add,
      Nat.reduceAdd]
    -- End of first terrible simp_all
    split -- if pos < prog.length…
    · simp_all only [List.getElem_append_left, dite_eq_ite] -- Just makes things more readable…
      split -- match …
      · simp_all only -- Reduce redundant cases
        split -- if pos < prog.length (but this time on the rhs)
        · apply extension_matching_close_irrelevance -- recures for goal one…
          rename_i h _ _ _ -- The h we know and love (pos < prog.length)
          exact h -- …and goal two is just as easy
        · simp_all only [not_lt] -- Get a prog.length + 2 <= pos from !pos < prog.length + 2…
          rename_i h _ _ anti_h -- Name our two contradictory hypotheses
          -- Rewrite so lean can understand what we want
          replace anti_h := Nat.le_of_add_right_le anti_h
          rw [<- Nat.not_lt] at anti_h -- Rewrite some more…
          exfalso
          contradiction -- … tada!
      · simp_all only
        -- This is the same as above, except for the first block, which is kinda involved
        -- so only that one is commented on.
        split
        · simp_all only [left_eq_ite_iff, not_lt]
          simp_all only [reduceCtorEq]
          simp_all only [imp_false, not_le]
          /- ^ This one does quite a few things! The most interesting ones are:
               · left_eq_ite_iff, which rewrites an if-else-statement into an inference
               · reduceCtorEq, which is kind of a shortcut to reduce a `some x = none` on the rhs
                 (it's intentionally on it's own line so
                  it's visible what it does since it's kind of a black box…)
               · imp_false, which turns a statement like `a -> False` into `!a` -/
          rename_i h _ _ _
          simp_all only [Nat.lt_succ_of_lt] -- remove the +2
        · split
          · apply extension_matching_close_irrelevance
            rename_i h _ _ _ _
            exact h
          · simp_all only [not_lt]
            rename_i h _ _ anti_h
            replace anti_h := Nat.le_of_add_right_le anti_h
            rw [<- Nat.not_lt] at anti_h
            exfalso
            contradiction
      · simp_all only [imp_false]
        split -- Same again, so no comments here, look above!
        · apply extension_matching_close_irrelevance
          rename_i h _ _ _ _
          exact h
        · simp_all only [not_lt]
          rename_i h _ _ anti_h
          replace anti_h := Nat.le_of_add_right_le anti_h
          rw [<- Nat.not_lt] at anti_h
          exfalso
          contradiction
    · simp_all only [not_lt, List.getElem_append_right, Nat.sub_eq_zero_of_le,
      List.getElem_cons_zero, dite_eq_ite, right_eq_ite_iff]
      /- This one was the most "fun" branch…
         Which makes sence, since this is the interesting case, where, on the lhs,
         we have reached the end of the program in search for a matching ']' and
         now need to show that we won't find it in the added "[]" either.
         Anyways, we start with a little clean-up to keep everthing readable -/
      intro _ -- We don't need this hypothesis but its good to have it out of the way
      rename_i posh _ -- `posh` is a wordplay (it's hpos "backwards")
      have p_eq_len := And.intro hpos posh
      /- ^ Okay. This one caused me some headaches and cost a lot of time. As it turns out, `and`
           and therefore the ∧ symbol are `Prop`-valued
           and can therefore not be applied to hypotheses.
           Sadly, that is not documented anywhere I checked so I essentially had to guess
           until I arrived at `And.into` and after some web searches,
           I'm still not sure what exactly the `.intro` does here. Please, someone explain! -/
      rw [<- Nat.eq_iff_le_and_ge] at p_eq_len -- Construct an equality for p out of hpos and posh
      subst p_eq_len -- and use that equality!
      rw [Eq.comm] -- swap the equality in the goal
      unfold matchingClose
      -- Ah shit, here we go again!
      simp_all only [le_refl, Nat.lt_add_right_iff_pos, Nat.zero_lt_succ, List.length_append,
        List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.lt_add_one, ↓reduceDIte,
        List.get_eq_getElem, Nat.le_add_right, List.getElem_append_right, Nat.add_sub_cancel_left,
        List.getElem_cons_succ, List.getElem_cons_zero, Nat.add_eq_zero_iff, Nat.succ_ne_self,
        and_false, ↓reduceIte, Nat.add_one_sub_one]
      /- End of the second terrible simp_all.
         Which sadly undid the unfold above, but also needs it there to simplify properly.
         Too bad! https://youtu.be/k238XpMMn38?t=83
         (Can you tell this one drove me a little crazy?)
         However, this also does a lot of the work for this part of the proof,
         mostly with all the `List.length_*`, `List.*append*` and `Nat.*add*` lemmas.
         With these, this call manages to tell lean that the "[]" grafted onto prog
         would actually be skipped and we'd end up with `pos + 2`! Cool. -/
      unfold matchingClose -- Well, we'll just unfold it again I guess…
      split -- a final if on pos and prog.length, with a +2 and the added brackets.
      · rename_i wrong
        exfalso
        -- I named the hypothesis "wrong" because I saw it was wrong
        -- but lean wants me to be more specific…
        simp_all only [List.length_append, List.length_cons, List.length_nil, Nat.lt_irrefl]
      · simp_all only -- at least this one was easy :)

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
