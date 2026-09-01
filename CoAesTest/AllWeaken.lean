/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Asta H. From
-/

import CoAes

set_option coaes.check.all true
set_option coaes.smallErrorMessages true

inductive All (P : α → Prop) : List α → Prop where
  | none : All P []
  | more {x xs} : P x → All P xs → All P (x :: xs)

@[coaes unsafe]
axiom weaken {α} (P Q : α → Prop) (wk : ∀ x, P x → Q x) (xs : List α)
  (h : All P xs) : All Q xs

/--
error: tactic 'coaes' failed, maximum number of rule applications (50) reached. Set the 'maxRuleApplications' option to increase the limit.
-/
#guard_msgs in
example : All (· ∈ []) (@List.nil α) := by
  coaes (config := { maxRuleApplications := 50, terminal := true })
