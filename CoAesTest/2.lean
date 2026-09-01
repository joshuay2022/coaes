/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import CoAes

-- This option would make CoAes time out.
set_option coaes.check.all false

inductive Even : Nat → Prop
| zero : Even Nat.zero
| plus_two {n} : Even n → Even (n + 2)

attribute [coaes safe] Even.zero Even.plus_two

example : Even 500 := by
  coaes (config := { maxRuleApplications := 0, maxRuleApplicationDepth := 0 })
