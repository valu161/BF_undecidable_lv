/-
Copyright (c) 2025 David Gross, Davood Therani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross, Davood Therani
-/
import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Find

/-!
# Interpreter

An interpreter for the BF language.

Specific design decisions compared with standard references (see below) are:

- Data (programs, memory, input, output) is of type `Data`, which abbreviates `List Nat`
- Finite number of memory cells / finite capacity per cell can be emulated by
modifying the `+` and `>` commands.
- Decrementing leaves `0` invariant
- Ill-formed jumps, i.e. `[` / `]` with no matching `]` / `[`, are ignored.

## Main definitions

- `BrainState`: A structure holding the state of a BF machine
- `step`: Updates the state under one step of the computation

This file also contains a `main` routine, which can be compiled into executable code.

## References

https://esolangs.org/wiki/Brainfuck
https://www.iwriteiam.nl/Ha_BF.html
https://copy.sh/brainfuck/
https://en.wikipedia.org/wiki/Brainfuck
-/


/-Code, memory, input, and output are all represented by `List Nat`-/
abbrev Data := List Nat

/-Coercion from `Char` to `Nat`, to input `Data` symbolically.-/
instance : Coe Char Nat where
  coe := Char.toNat

instance : Coe (List Char) (List Nat) where
  coe := List.map Char.toNat


/-

  The BF interpreter
  ==================

-/


/-- BrainState is the data structure that represents the state of the interpreter. -/
@[ext]
structure BrainState where
  /-- `prog : List Nat`: Contains the program. It is immutable. -/
  prog : Data
  /- `input : List Nat`: The input is supplied to the program at the beginning.
  Characters are read from the head of this list and then removed from it.-/
  input : Data := []
  /- `output : List Nat`: Any output is appended to this list. -/
  output: Data := []
  /-- `mem  : List Nat`: The memory. -/
  mem : Data := [0]
  /-- `progPos : Nat`: The instruction pointer.  If between `0` and `prog.length-1`,
  it is the index within `prog` of the next instruction to be processed. If equal
  to `prog.length`, the program has terminated.  No other values must be attained. -/
  progPos : ℕ := 0
  /-- `memPos : Nat`: The data pointer: The index within `mem` of the memory cell
  that can be accessed by the next command. The interpreter will grow `mem` by one
  cell whenever the data pointer increments. This way, the machine can use an
  unbounded amount of memory, and `memPos` will always lie in the range `0 ...
  prog.length-1`. -/
  memPos : ℕ := 0

/-
*Example* (c.f. `reversi5` below)

prog:   ",>,>,>,>,.<.<.<.<."
                        ^
                         \ progPos

mem:    "Hello"...
            ^
             \ memPos

input:  "!"

output: "oll"
-/

/--
Assuming that `prog[pos+1]='['`, return `some pos` where `pos` is the position
of the matching closing bracket, or `none` if none exists.
-/
def matchingClose (prog : Data) (pos : Nat) (depth : Nat := 0) : Option Nat :=
  if h: pos < prog.length then
    match prog.get ⟨pos, h⟩ with
    | '[' => matchingClose prog (pos + 1) (depth + 1)
    | ']' => if depth = 0 then some pos else matchingClose prog (pos + 1) (depth - 1)
    | _   => matchingClose prog (pos + 1) depth
  else
    none

/--
The mirror image of `matchingClose`.

Note: Also works in the edge case where `pos=0`, so that `pos-1` equals `0`
too, and thus points to the closing bracket itself rather than to the character
to the left of it. (That's a bit hacky, but changing the interface to accept
`pos` rather than `pos-1` comes with other downsides...).
-/
def matchingOpen
  (prog : Data) (pos : Nat) (depth : Nat := 0) (h : pos < prog.length := by omega) : Option Nat :=
  if pos = 0 then
    if prog.get ⟨pos, h⟩ = '[' ∧ depth = 0 then some 0 else none
  else
    match prog.get ⟨pos, h⟩ with
    | ']'  => matchingOpen prog (pos-1) (depth + 1)
    | '['  => if depth = 0 then some pos else matchingOpen prog (pos-1) (depth - 1)
    | _    => matchingOpen prog (pos-1) depth


/--
The core of the interpreter: Interpret one instruction and update the state accordingly.

The constants `memSize` and `cellSize` are the number of memory cells, and the
number of states per memory cell, respectively. Set both to `0` for unlimited size.
-/
def step (b : BrainState) : BrainState :=
  let memSize : Nat := 0
  let cellSize : Nat := 0
  if h: b.progPos < b.prog.length then
    match b.prog.get ⟨b.progPos, h⟩ with
      | '>' => {b with
        progPos := b.progPos + 1,
        memPos := (b.memPos + 1) % memSize
        mem := b.mem ++ [0]}
      | '<' => {b with
        progPos := b.progPos + 1,
        memPos := b.memPos - 1}
      | '+' => {b with
        progPos := b.progPos + 1,
        mem := b.mem.modify b.memPos (fun n => (n+1) % cellSize)}
      | '-' => {b with
        progPos := b.progPos + 1,
        mem := b.mem.modify b.memPos Nat.pred}
      | '[' =>
        match matchingClose b.prog (b.progPos+1), b.mem[b.memPos]? == some 0 with
          | some target, true => {b with progPos := target + 1}
          | _, _              => {b with progPos := b.progPos + 1}
      | ']' =>
        -- Below is the easier-to-parse semantics as described in the lecture notes...
        -- match matchingOpen b.prog (b.progPos-1) with
        --   | some target => {b with progPos := target}
        --   | _           => {b with progPos := b.progPos + 1}
        -- ...but we actually implement this, equivalent one:
        match matchingOpen b.prog (b.progPos-1), b.mem[b.memPos]? == some 0 with
          | some target, false => {b with progPos := target + 1}
          | _, _               => {b with progPos := b.progPos + 1}
        -- If the flag is no longer set, it avoids jumping back to the opening
        -- bracket. That's a minor run-time optimization, but more importantly,
        -- makes the if-run-else-halt construction easier to reason about,
        -- because in the 'halt' branch, the steady state will be reached earlier.
      | '.' => {b with
        progPos := b.progPos + 1,
        output := b.output ++ [b.mem[b.memPos]?.getD 0]}
      | ',' => {b with
          progPos := b.progPos + 1,
          mem := b.mem.set b.memPos (b.input[0]?.getD 0),
          input := b.input.tail}
      | _ => {b with progPos := b.progPos + 1}
  else
    b

/-

  Running BF programs
  ===================

-/

def execute (p a : Data) (n : ℕ) : BrainState :=
  step^[n] { prog := p, input := a }

/- Useful for demonstration purposes -/
def outputStr (p a : String) (n : ℕ) : String :=
  String.mk ((execute p.toList a.toList n).output.map Char.ofNat)

/-
  A program halts when its instruction pointer moves past the last instruction.
-/

/-- the property that when running `p` on `a`, it will have halted after `n` steps -/
abbrev halted_at (p a : Data) (n : ℕ) := (execute p a n).progPos = p.length

-- -- Type class resolution doesn't "look through definitional equivalence"?!
-- -- TBD: Understand better
-- instance (p a : Data) : DecidablePred (halted_at p a) :=
--   fun n => inferInstance

-- abbrev halted_at (p a : Data) (n : ℕ) :=
--   (execute p a n).progPos = p.length
-- set_option trace.Meta.synthInstance true in
-- #check (fun p a => (inferInstance : DecidablePred (fun n => halted_at p a n)))

instance (p a : Data) : DecidablePred (halted_at p a) := fun n => by
  unfold halted_at
  apply inferInstance

def halts (p a : Data) : Prop :=
  ∃ n, halted_at p a n

/--
"Evaluate" a program:

Given a proof that it does terminate, run it and return `true` / `false`
depending on whether the current memory cell isn't / is `0` when the program
halts.
-/
def eval {p a} (h : halts p a) :=
  let b := execute p a (Nat.find h)
  if b.mem[b.memPos]? == some 0 then false else true


/-

  `eval` requires a proof of termination.

  But, due to proof irrelevance, the details of the proof cannot influence the
  runtime behavior. It thus becomes possible to supply `sorry` as a proof and
  make Lean execute it using the `#eval!` command.

-/

def brief_halting_prog : Data := "[]".toList

-- #eval @eval brief_halting_prog [] sorry
-- aborting evaluation since the
-- expression depends on the 'sorry' axiom, which can lead to runtime
-- instability and crashes.

set_option warn.sorry false in
def brief_halting_result := (@eval brief_halting_prog [] sorry)
#print axioms brief_halting_result -- ...sorryAx....

set_option warn.sorry false in
#eval! @eval brief_halting_prog [] sorry -- `false`

def brief_looping_prog : Data := "+[]".toList

-- #eval @eval brief_looping_prog [] sorry
-- aborting evaluation since the expression depends on the 'sorry' axiom, which
-- can lead to runtime instability and crashes.
-- Warning! The next command might crash Lean. Uncomment at your own risk.
-- #eval! @eval brief_looping_prog [] sorry
-- Server process [...] crashed, likely due to a stack overflow or a bug.

/--
Partial version of `eval`. Does not require a proof of termination.
-/
partial def partial_eval (prog input : Data) : Bool :=
  let rec go (b : BrainState) : Bool :=
    if b.progPos = b.prog.length then
      b.mem[b.memPos]? == some 0
    else
      go (step b)

  go { prog := prog, input := input }

/-

  Some BF programs
  ================

-/

/-- Reverse five letter input -/
def reversi5 := "I will reverse any five letter input -- let's go! ,>,>,>,>,.<.<.<.<."

#eval outputStr reversi5 "hello" 80

-- set_option diagnostics true in
-- set_option maxRecDepth 10000 in
-- #reduce (outputStr reversi5 "hello" 80)

/-- Read a zero-terminated string (including the trailing zero) -/
def read_zero_terminated := ",[>,]"
/-- Reverse a zero-terminated string -/
def reversi := "Give me input to reverse!  " ++ ">" ++ read_zero_terminated ++ "<[.<]"

#eval outputStr reversi "desrever ma I \x00" 200

/-- Count up in an esthetically pleasing way

    From https://esolangs.org/wiki/Brainfuck
-/
def looping_counter := ">>++++++++++[[->+<<++++>]<++[<]>[.>]>.]"
#eval IO.println (outputStr looping_counter "" 1000)

/-- echo the input until the first 0 -/
-- def echo := ">" ++ read_zero_terminated ++ "<[<]" ++ ">[.>]"
def echo := ",.[,.]"
def echo' := "
  ,         // read first input character into memory
  .         // output it
  [         // as long as first memory cell isn't 0
    ,.      //  read and print the next character
  ]         // exit. "

#eval outputStr echo "Hi!" 10
#eval outputStr echo "Hi!" 10

/-- ROT13 cipher, because we can!

    From https://github.com/bonomat/rot13-brainfuck
-/
def rot13 :=
  "-,+[-[>>++++[>++++++++<-]<+<-[>+>+>-[>>>]<[[>+<-]>>+>]<<<<<-]]>>>[-]+>--[-[<->[-
  ]]]<[++++++++++++<[>-[>+>>]>[+[<+>-]>+>>]<<<<<-]>>[<+>-]>[-[-<<[-]>>]<<[<<->>-]>
  >]<<[<<+>>-]]<[-]<.[-]<-,+]"

#eval outputStr rot13 "a" 10000

/-- Hello world!

    From Wikipedia: https://en.wikipedia.org/wiki/Brainfuck#Hello_World!
-/
def hello_world :=
  "++++++++[>++++[>++>+++>+++>+<<<<-]>+>+>->>+[<]<-]>>.>---.+++++++..+++.>>.
  <-.<.+++.------.--------.>>+.>++."

#eval outputStr hello_world "" 1000

/-- Bubblesort

    From https://brainfuck.org/ works on both letters and numbers
-/
def bubble_sort :=
  ">>,[>>,]<<[[<<]>>>>[<<[>+<<+>-]>>[>+<<<<[->]>[<]>>-]<<<[[-]>>[>+<-]>>[<<<+>>>-]]
  >>[[<+>-]>>]<]<<[>>+<<-]<<]>>>>[.>>]"

#eval outputStr bubble_sort "2shpic1" 300000

/-

  Runtime
  =======

  A minimal interactive wrapper around the interpreter. Can be invoked with

   `lake exe LeanSeminar.Interpreter`

  At the moment, the BF code, its arguments, and the terminal's width are
  hardcoded and have to be changed here. If someone feels ambitious, this could
  be changed easily (c.f. "Functional Programming in Lean").

-/

-- TBD: clean this up
abbrev String.toData : String → Data := fun s => s.toList
def dataToString : Data → String := fun d => String.ofList (d.map Char.ofNat)

/-- Helper: concatenates the string `s` with itself `n` times -/
def repeatStr (s : String) (n : Nat) : String :=
  String.join (List.replicate n s)

/--
Hacky routine that maps a character to a length-three string representation,
starting with a space. Special-cases '\x00'.

TBD: Broke after Mathlib update. Fix.
-/
def toShortString (c : Nat) : String :=
  if c = 0 then
    " · "
  else
    match (Char.ofNat c).toString.quote.length with
    | 3 => " " ++ (Char.ofNat c).toString ++ " "
--    | 6 => " " ++ (Char.ofNat c).toString.quote.extract ⟨3⟩ ⟨5⟩
    | 6 => " " ++ (Char.ofNat c).toString.quote.extract
            ((Char.ofNat c).toString.quote.pos? ⟨3⟩).get!
            ((Char.ofNat c).toString.quote.pos? ⟨5⟩).get!
    | _ => " ??"



def midpointMarker (tokens : Nat) : String := (repeatStr "   " (tokens / 2)) ++ " ↑ "
def clearScreen : String := '\x1b'.toString ++ "c"

partial def centerList (tokens : Nat) (l : List Nat) (mid : Nat) : String :=
  let leftDelta : Int := mid - tokens / 2
  if leftDelta < 0 then -- too few elements to the left
    centerList tokens ((List.replicate leftDelta.natAbs ' '.toNat) ++ l) (mid + leftDelta.natAbs)
  else if leftDelta > 0 then -- too many elements to the left
    centerList tokens (l.drop leftDelta.toNat) (tokens/2)
  else if l.length > tokens then -- too many to the right
    centerList tokens (l.take tokens) mid
  else
    l.foldl (· ++ toShortString ·) ""

unsafe def main : IO Unit := do
  -- let mut b : BrainState := { prog := bubble_sort.toList , input := "scphi".toList }
  -- let mut b : BrainState := { prog := reversi5.toList , input := "Hallo".toList }
  let mut b : BrainState := { prog := hello_world.toList  }
  -- let mut b : BrainState := { prog := reversi.toList , input := "Hallo!?".toList }
  -- let mut b : BrainState := { prog := echo'.toList , input := "Hallo!?".toList }
  let stdin <- IO.getStdin
  let mut i : Nat := 0
  -- /- get terminal width.-/
  -- let out ← IO.Process.output { cmd := "tput", args := #["cols"] }
  -- let tokens : Nat :=
  --   match out.exitCode with
  --   | 0 => out.stdout.trim.toNat!/3
  --   | _ => 26 -- 80/3
  /- TBD: Above doesn't work; `tput` seems to return 80, always, when invoked via `lake exe`. -/
  let tokens := 26
  while true do
    IO.print clearScreen
    IO.println (centerList tokens b.prog b.progPos)
    IO.println (midpointMarker tokens)
    IO.println "\n"
    IO.println (centerList tokens b.mem b.memPos)
    IO.println (midpointMarker tokens)
    IO.println "\n"
    IO.println ("Input : " ++ (dataToString b.input))
    IO.println ("Output: " ++ (dataToString b.output))
    IO.println "\n"
    IO.print ("Prog pos: " ++ (Nat.repr b.progPos) ++ ",")
    IO.print ("  Mem pos: " ++ (Nat.repr b.memPos) ++ ",")
    IO.println ("  step #: " ++ (Nat.repr i) ++ ".")
    IO.println "\nPress return to progress one step, <i>+return for 2^i steps. Ctrl-c to abort."
    let inp ← stdin.getLine
    let c := String.Pos.Raw.get! inp 0
    let nr := if c.isDigit then (Nat.pow 2 (c.toNat - '0'.toNat)) else 1
    i := i+nr
    b := step^[nr] b
