/-
Copyright (c) 2025 David Gross, Davood Therani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross, Davood Therani
-/
import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Find
import BfUndecidable.Interpreter
import BfUndecidable.Basic

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
    rw [h1, h2, h3] --self explanatory



lemma prog_immutable_execute (p a n) : (execute p a n).prog = p := by
  unfold execute
  use prog_immutable_steps --wow I didn´t expect that to work...

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
  have hprogpos : (execute p d n).progPos ≤ p.length := progPos_le p d n --use the lemma from above
  by_cases hpos : (execute p d n).progPos < p.length --split in the two cases: < and =
  · exact hpos --if <, then we are done
  · have hprogpos_eq : halted_at p d n := by omega
    --if not <, then we have = so we can use the definition of halts
    have contra : ¬ halted_at p d n := Nat.find_min h hn
    --nat.find comes with this lemma, which says that n is the smallest number
    -- for which halted_at p d n
    contradiction --proof by contradiction of the hypotheses


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
      intro contra --contra is the hypothesis without /neg, simp contradicts it so we can
      --construct false with omega
      omega
--i called it hcomeon because I was hoping that simp[h] would be sufficient
--after replacing halted_at with its definitions, but lean did not see that progPos=prog.length
--means ¬ progPos < prog.length
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
  simp_all only [List.get_eq_getElem, List.getElem_append_left]

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

@[simp] theorem matchingOpen_proof_irrel --had to include this for a later proof, explanation s.b.
  (prog : Data) (pos : Nat)
  (h₁ h₂ : pos < prog.length) :
  matchingOpen prog pos 0 h₁ = matchingOpen prog pos 0 h₂ := by
  have : h₁ = h₂ := Subsingleton.elim _ _
  cases this
  rfl
-- simp_all [matchingClose] introduces Classica.choice. TBD. reduceIte, reduceDIte? -/
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
    have h1 : (step { b with prog := ireh_extend b.prog }).prog =
    { step b with prog := ireh_extend b.prog }.prog
    := by
     apply prog_immutable_step -- to show later that the prog instance is equal
    have hb2 : b.progPos < b.prog.length + 2 := by omega
    have hb1 : b.progPos -1 < b.prog.length := by omega
    dsimp
    --dsimp: undo a 'let' that appears in the goal and does not let me use h1 for the prog equallity
    ext progpos progchar
     --instead of showing it for the whole structure we show it separately for its instances
    · simp[h1] --yaaaaay
    · unfold step ; simp only [extension_body_irrelevance b.prog b.progPos hb] ; simp [hb, hb2]
      split
      · simp
      · simp
      · simp
      · simp
      · simp[extension_matching_close_irrelevance b.prog (b.progPos+1) 0 hb]
        split
        · simp
        · simp
      · split
        --actually I dont need the matching open irrelevance here, I can just split twice and simp.
        -- I do it that way because simp with matching_open irrelevance,
        --does not reduce the two if conditions in the goal to the same,
        -- because of the implicit argument (proof of pos < prog.length)
        -- but, as I said, we can just split and simp seperately
        · split <;> simp
        · split <;> simp
      · simp
      · simp
      · simp
    --now I just do the same thing over and over again, until it does not work anymore
    · unfold step ; simp only [extension_body_irrelevance b.prog b.progPos hb] ; simp [hb, hb2]
      split
      · simp
      · simp
      · simp
      · simp
      · simp[extension_matching_close_irrelevance b.prog (b.progPos+1) 0 hb]
        split
        · simp
        · simp
      · split
        · split <;> simp
        · split <;> simp
      · simp
      · simp
      · simp
    · unfold step ; simp only [extension_body_irrelevance b.prog b.progPos hb] ; simp [hb, hb2]
      split
      · simp
      · simp
      · simp
      · simp
      · simp[extension_matching_close_irrelevance b.prog (b.progPos+1) 0 hb]
        split
        · simp
        · simp
      · split
        · split <;> simp
        · split <;> simp
      · simp
      · simp
      · simp
    /-okay here we are, now matching open will cause problems for me, because I now have to show
    that target for the two matching opens will be the same by using the lemma and fighting against
    the implicit argument. The Problem was:
    lean does not recognize: matchingOpen ireh_extend b.prog b.progPos 0 h:(by simp; omga) =
    matchingOpen ireh_extend b.prog b.progPos 0 (h:by omga) which is a bit crazy,
    but when I let lean show me the proofs they were clearely different.
    so my solution was a proof irrelevance lemma and
    I used the symmetry of the equallity to get rid of the ireh_extend b.prog instead
    of the b.prog, because then the simplification was easier.-/
    · unfold step ; simp only [extension_body_irrelevance b.prog b.progPos hb] ; simp? [hb, hb2]
      split
      · simp
      · simp
      · simp
      · simp
      · simp[extension_matching_close_irrelevance b.prog (b.progPos+1) 0 hb]
        split
        · simp
        · simp
      · have symm (prog : Data) (pos : Nat) (depth : Nat) (hpos : pos < prog.length):
         matchingOpen (ireh_extend prog) pos depth (by simp; omega) =
         matchingOpen prog pos depth hpos := by
         simp [(extension_matching_open_irrelevance prog pos depth hpos)]
--just the symmetry of the equallity to get rid of the ireh_extend
        simp? [symm b.prog (b.progPos-1) 0 hb1]
        let homega : b.progPos - 1 < b.prog.length := by omega
--this is the implicit argument for matching open in the first case
        simp only [matchingOpen_proof_irrel b.prog (b.progPos-1) homega hb1]
--proof irrelevance for the h-arguments in the matching open expression
        split <;> simp --now split works :)
      · simp
      · simp
      · simp
    · unfold step
      simp only [extension_body_irrelevance b.prog b.progPos hb] ; simp [hb, hb2]
      split
      · simp
      · simp
      · simp
      · simp
      · simp[extension_matching_close_irrelevance b.prog (b.progPos+1) 0 hb]
        split
        · simp
        · simp
      · split
        · split <;> simp
        · split <;> simp
      · simp
      · simp
      · simp





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
    apply And.intro -- Split the And
    case left =>
      subst hb
      -- get an obvious truth from the library… (h is true for (Nat.find h)
      have h_spec := Nat.find_spec h
      -- this step is not strictly necessary but makes the state easier to read…
      unfold halted_at at h_spec
      rw [<- h_spec] -- combine our hypotheses
      rw [<- execute_extend_commute] -- and use the previous lemma to show the two sides are equal.
      -- execute_extend_commute wants h and hn, which are provided with the bullet points below
      · exact h
      · simp_all
    case right =>
      unfold eval -- This is essentially what the goal wants
      simp_all only [beq_iff_eq, Bool.if_true_right, Bool.or_false]
      rw [<- execute_extend_commute] -- again, show some equalities of ireh_extend
      · grind only -- This isn't really transparent but it's just boring case checks from here on…
      -- execute_extend_commute wants h and hn, which are provided with the bullet points below
      · exact h
      · simp_all

-- a little helper for later…
lemma execute_def (p a : Data) (n : ℕ) :
  execute p a n = step^[n] { prog := p, input := a } := rfl

/--
If `cond input` evaluates to `false`, then

  `if cond(input) then loop_forever else halt`

will halt.
-/
theorem ireh_halts_of_false
    (cond : Data) (input : Data) (h : halts cond input)
    (hret : eval h = false) : halts (ireh_extend cond) input := by
  -- construct a brainstate that is like the one in ireh_cond_state
  let b := execute (ireh_extend cond) input (Nat.find h)
  have hb : b = execute (ireh_extend cond) input (Nat.find h) := by rfl
  have hstate := ireh_cond_state cond input h b hb -- get the state hypotheses
  obtain ⟨hsleft, hsright⟩ := hstate
  rw [hret] at hsright
  simp only [bne_eq_false_iff_eq] at hsright
  -- After we have our state(-hypotheses) in a convenient form, we can start doing the actual proof…
  -- First, we get a little helper hypothesis that makes omega behave a bit nicer
  have hlen : b.prog.length = cond.length + 2 := by
    unfold b
    simp only [prog_immutable_execute]
    unfold ireh_extend
    simp
  -- Then, we prove some simple hypotheses about indexing to prepare the next step
  have hind  : cond.length     < b.prog.length := by omega
  have hind' : cond.length + 1 < b.prog.length := by omega
  -- Now, we show what the second-to-last and last characters are
  have hchar  : b.prog.get ⟨cond.length, hind⟩      = '[' := by
    unfold b
    simp [prog_immutable_execute]
  have hchar' : b.prog.get ⟨cond.length + 1, hind'⟩ = ']' := by
    unfold b
    simp [prog_immutable_execute]
  -- Almost at the end already!
  -- Here we construct our example, i.e. (step b) and show that it halts
  -- In case you wondered: (step b) is just b as defined above but with steps.succ ;)
  have hbhalts : halted_at (ireh_extend cond) input (Nat.find h).succ := by
    unfold halted_at
    unfold execute -- Now we have everything in terms of step^[…]
    -- Rewrite step^[N.succ] as step step^[N] so we can turn the latter into step b…
    simp only [Function.iterate_succ_apply']
    rw [<- execute_def, <- hb]
    unfold step -- This messes up the goal a bit but we can go through it quite quickly!
    -- Go straight to the matchingClose call in step. It goes like this:
    --
    --            /------------------ b.progPos = cond.length            (first if/else)
    --            |      /----------- cond.length < b.prog.length = True (first if/else)
    --            |      |     /----- b.prog.get ⟨b.progPos, h⟩ = '['     (match)
    --            V      V     V
    simp only [hsleft, hind, hchar]
    unfold matchingClose
    simp only [hind', hchar'] -- Similar to the simp only above, this goes through matchingClose
    simp_all -- Now we know that progPos = prog.length, so the rest is trivial :)
  -- And with this last hypothesis the actual proof is quite easy!
  unfold halts
  apply Exists.intro -- We need to find a witness
  exact hbhalts      -- Turns out it's (Nat.find h).succ!

/--
If `cond input` evaluates to `true`, then

  `if cond(input) then run_forever else halt`

will not halt.
-/
theorem ireh_runs_of_true (cond : Data) (input : Data) (h : halts cond input)
--I used the same beginning as in the previous proof,
-- because many of the hypotheses will come handy.
    (hret : eval h = true) : ¬ halts (ireh_extend cond) input := by
  -- construct a brainstate that is like the one in ireh_cond_state
  let b := execute (ireh_extend cond) input (Nat.find h)
  have hb : b = execute (ireh_extend cond) input (Nat.find h) := by rfl
  have hstate := ireh_cond_state cond input h b hb -- get the state hypotheses
  obtain ⟨hsleft, hsright⟩ := hstate
  simp?[hret] at hsright
  -- After we have our state(-hypotheses) in a convenient form, we can start doing the actual proof…
  -- First, we get a little helper hypothesis that makes omega behave a bit nicer
  have hlen : b.prog.length = cond.length + 2 := by
    unfold b
    simp only [prog_immutable_execute]
    unfold ireh_extend
    simp
  -- Then, we prove some simple hypotheses about indexing to prepare the next step
  have hind  : cond.length     < b.prog.length := by omega
  have hind' : cond.length + 1 < b.prog.length := by omega
  -- Now, we show what the second-to-last and last characters are
  have hchar  : b.prog.get ⟨cond.length, hind⟩      = '[' := by
    unfold b
    simp [prog_immutable_execute]
  have hchar' : b.prog.get ⟨cond.length + 1, hind'⟩ = ']' := by
    unfold b
    simp [prog_immutable_execute]
--here the differences start
  intro contra --we want to show neg so we want to create false out of contra
  --the idea:
  --hrun says that it does not matter how long the programm runs,after having
  --reached b, it will never reach its end. to make the induction work we dont only
  --want hrun to say something about progpos, but also about mem[mempos] because we need
  --that information from the induction hypothesis
  -- to resolve the matching open in the step function
  have hrun : ∀ n,
  ((step^[n+1] b).progPos = cond.length + 1) ∧
   (¬((step^[n+1] b).mem[(step^[n+1] b).memPos]? = some 0)) := by
   intro n
   induction n with
   | zero => simp? ; unfold step ; simp only [hsleft, hind, hchar] ; simp [hsright]
   --this is like the proof above, just unfold step and then get rid of step
   | succ m ih =>
     obtain ⟨ihleft, ihright⟩ := ih
     have hstep: (step^[m + 1 + 1] b) = (step (step^[m + 1] b)) :=
     by simp only [Function.iterate_succ_apply']
      --same as always, rewrite step^[N.succ] as step step^[N]
     rw [hstep]
     let b' := (step^[m + 1] b)
     have hb' :  (step^[m + 1] b) = b' := by rfl --dont know how to unfold just one step mor elegant
     rw [hb'] -- this all is for unfolding just one step
     unfold step
     rw [<- hb'] --okay lets continue
     have hind'' : List.length (step^[m + 1] b).prog = List.length cond + 2 := by
      simp [prog_immutable_steps,prog_immutable_step, hlen ]
       --using prog_immutable steps to simplify
      -- the left hand side will be replaced by right hand side in the iff cond
     simp only [hind'', ihleft] ; simp? -- undo the if condition, the simp just says 1<2
     have h_im_prog : (step^[m] (step b)).prog = b.prog := by
      simp[prog_immutable_steps,prog_immutable_step]
    --again, we want to get rid of the m´s where we can
     simp only [h_im_prog]
     have helpp :
      b.prog[List.length cond + 1] = List.get b.prog ⟨List.length cond + 1, hind'⟩ := by simp
  --its ugly but simp didnt recognize that the two sides are the same,
  --so I had to introduce this helper hypothesis
     rw [helpp] ; simp only [hchar']; simp?
     -- this undoes the match so we are left with matching open

     -- the namings follow this principle: matching open matches 2 characters, so h1 is for
     -- the first and h2 is for the second and hstep2 just adds a step to the iteration like hstep
     have hstep2 : (step^[m] (step b)).mem[(step^[m] (step b)).memPos]?
     = (step^[m+1] b).mem[(step^[m+1] b).memPos]? := by rfl
     have h2 : ¬ ( (step^[m] (step b)).mem[(step^[m] (step b)).memPos]? == some 0) := by
       simp [hstep2, ihright]
     have h1 : matchingOpen b.prog (List.length cond) = some (List.length cond) := by
      unfold matchingOpen ; simp only [hchar] ;simp? ; intro h ;rw [h] ; simp
     simp? [h1,h2]
     simp?[hstep2]
     --now we got rid of the matching therm and finally we can use th induction hypothesis
     -- to solve the goal
     exact ihright --hallelujah

     /- so this was a bit confusing but the essence was: start at b -> do step once ->
     show that progpos, mem and mempos did not change -> do induction: if the tree did not change
     after m steps, then they will never change. (this obviously is not always true,
     but in our case it is true) (as the proof says)-/
--
  rw [halts] at contra
  obtain ⟨n, hn⟩ := contra --now we cook our contradiction: we say it halted after n steps,
  --but then it also should stay halted, but we just showed that the programm will never
  --reach its end so if we find a number, where hn says: it has halted, but hrun says, it has
  --not halted (because progpos is not proglength) we are done
  --this is what happens next: the number I chose is (Nat.find h + n+ 1) so everything
  --from nowon is just the idea from above and rewriting so that lean sees this too
  have hn' : n  <  n + 1 + Nat.find h := by omega --helping lemma
  have hn'' : halted_at (ireh_extend cond) input ( n + 1 + Nat.find h ) := by
   exact halts_gt hn' hn
   --halting is preserved by halts_gt:
   -- we can use it to show that it also halts after n+1+Nat.find h steps
  have hrun' := (hrun  n).left
  rw [halted_at, execute] at hn''
  let x := Nat.find h
  let hx := x= Nat.find h
  rw [hb, execute] at hrun'
  have hjungeistdasnervig : --I was annoyed that lean does not recognize this by its own
  --and it took me pretty long to figure out how to show that, although its trivial
   (step^[n + 1] (step^[Nat.find h] { prog := ireh_extend cond, input := input })).progPos =
   (step^[ n + 1 + Nat.find h] { prog := ireh_extend cond, input := input }).progPos := by
    simp only [ Function.iterate_add]; simp
  rw [hjungeistdasnervig] at hrun'
  simp [hn''] at hrun' --Tadaaaaa no computer can decide the bf halting problem!



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
