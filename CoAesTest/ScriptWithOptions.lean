/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import CoAes

-- CoAes note: the builtin closing rules would prove this file's goals with a
-- bare `simp`, hiding the simp configuration that this file is about. They
-- are erased for this file.
erase_coaes_rules
  [CoAes.BuiltinRules.closeSimp, CoAes.BuiltinRules.closeSimpAll,
   CoAes.BuiltinRules.closeOmega, CoAes.BuiltinRules.closeDecide,
   CoAes.BuiltinRules.closeGrind]


set_option coaes.check.all true

/--
info: Try this:

  [apply]   simp_all (config := { })
-/
#guard_msgs in
example : True := by
  coaes? (config := {}) (simp_config := {})
