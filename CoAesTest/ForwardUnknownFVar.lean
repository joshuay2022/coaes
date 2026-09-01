/-
Copyright (c) 2025 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, Jannis Limperg
-/

import CoAes

attribute [coaes safe forward 1] Nat.le_trans
attribute [-coaes] CoAes.BuiltinRules.applyHyps

variable (a b c d e f : Nat)

/-- error: tactic 'coaes' failed, failed to prove the goal after exhaustive search. -/
#guard_msgs in
set_option coaes.smallErrorMessages true in
example (h₃ : c ≤ d) (h₄ : d ≤ e) (h₅ : e ≤ f) (h : a = f) : False := by
  coaes (config := { terminal := true })
