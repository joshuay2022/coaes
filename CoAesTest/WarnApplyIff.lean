/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import CoAes

set_option coaes.check.all true

/--
warning: Apply builder was used for a theorem with conclusion A ↔ B.
You probably want to use the simp builder or create an alias that applies the theorem in one direction.
Use `set_option coaes.warn.applyIff false` to disable this warning.
-/
#guard_msgs in
@[coaes safe apply]
axiom foo : True ↔ True

@[coaes simp]
axiom bar : True ↔ True

set_option coaes.warn.applyIff false in
@[coaes 1% apply]
axiom baz : True ↔ True
