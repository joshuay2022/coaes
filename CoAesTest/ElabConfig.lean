/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import CoAes

set_option coaes.check.all true

/-- error: `noSuchOption` is not a field of structure `CoAes.Options` -/
#guard_msgs in
example : True := by
  coaes (config := { noSuchOption := true })

/-- error: `noSuchOption` is not a field of structure `Lean.Meta.Simp.ConfigCtx` -/
#guard_msgs in
example : True := by
  coaes (simp_config := { noSuchOption := true })
