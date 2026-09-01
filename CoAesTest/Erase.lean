/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import CoAes

set_option coaes.check.all true
set_option coaes.smallErrorMessages true

@[coaes [10% cases, safe constructors]]
inductive Even : Nat → Prop
  | zero : Even 0
  | plus_two : Even n → Even (n + 2)

example : Even 2 := by
  coaes

-- Removing the CoAes attribute erases all rules associated with the identifier
-- from all rule sets.
attribute [-coaes] Even

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : Even 2 := by
  coaes (config := { terminal := true })

example : Even 2 := by
  coaes (add safe Even)

-- We can also selectively remove rules in a certain phase or with a certain
-- builder.
attribute [coaes [unsafe 10% cases, safe constructors]] Even

erase_coaes_rules [ unsafe Even ]

example : Even 2 := by
  coaes

erase_coaes_rules [ constructors Even ]

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : Even 2 := by
  coaes (config := { terminal := true })

example : Even 2 := by
  coaes (add safe constructors Even)
