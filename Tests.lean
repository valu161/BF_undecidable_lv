/-
Copyright (c) 2025 David Gross, Davood Therani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross, Davood Therani
-/
import BfUndecidable.Interpreter

-- Silence the overly eager linter
set_option linter.style.cdot false
set_option linter.style.longLine false

/-

  Tests
  =====

  If you get an error here, you broke the BF machine.

-/


/--
Filter out zero's
-/
def cleanOutput (d : Data) : Data := d.filter (· != 0)

section

set_option linter.hashCommand false

#guard dataToString (execute hello_world.toList [] 1000).output = "Hello World!\n"
#guard dataToString (execute reversi5.toList "Hello".toList 100).output = "olleH"
#guard dataToString (execute reversi.toList ("Reversi!".toList ++ ['\x00']) 200).output = "!isreveR"
-- #guard cleanOutput (execute bubble_sort.toList "scphi".toList 50000).mem = "chips"
#guard (dataToString ((execute rot13.toList "ABCNOPabcnop".toList 40000).output.take 12)) = "NOPABCnopabc"
#guard (dataToString (execute looping_counter.toList "A".toList 500).output) = "*\n**\n***\n"
-- At some point, there was a bug that made it so that '['-jumps wouldn't work.
-- But still, all tests at the time executed correctly!
-- So let's add a dedicated unit test that actually uses jump-on-`[`.
def jump_right_test := "[,.],."
#guard dataToString (execute jump_right_test.toList "ABC".toList 10).output = "A"

end -- `linter.hasCommand false`
