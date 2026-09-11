/-
Tests for CoAes's handling of resource limits (`maxHeartbeats`).

A rule that exceeds a resource limit counts as a failed rule: the search
continues with the other rules and reports the progress it made, rather than
failing the whole tactic with a heartbeat error. Rules that were cut off this
way are reported in a warning, so that a user of `coaes?` knows that the script
was found without them.
-/
import CoAes

set_option coaes.check.all true

-- A definition that is expensive to evaluate, used to make rules run out of
-- heartbeats.
def slow (n : Nat) : Nat := (List.range n).foldl (· + ·) 0

-- § 1. Rules that exceed their budget do not fail the tactic. ---------------

-- With a per-rule budget of 1000 heartbeats, `unfold`, `simp` and `simp_all`
-- all run out, but `omega` still closes the goal. The script reports `omega`
-- and a warning names the rules that were cut off.
/--
info: Try this:

  [apply]   omega
---
warning: coaes: the following rules were treated as failed because they exceeded a resource limit (e.g. 'maxHeartbeats'): <norm unfold>, CoAes.BuiltinRules.closeSimp, CoAes.BuiltinRules.closeSimpAll
The search continued without them, so the result may be incomplete. Set option 'maxRuleHeartbeats' to give each rule more time.
-/
#guard_msgs in
example (h : slow 5000 = 12497500) : slow 5000 = 12497500 := by
  coaes? (defs := [slow]) (config := { maxRuleHeartbeats := 1 })

-- The same call without a script request succeeds quietly: nothing is left
-- for the user to act on.
#guard_msgs in
example (h : slow 5000 = 12497500) : slow 5000 = 12497500 := by
  coaes (config := { maxRuleHeartbeats := 1 })

-- § 2. Without the budget, the goal is proved by the usual rules. -----------

/--
info: Try this:

  [apply]     unfold slow
    unfold slow at h
    simp_all
-/
#guard_msgs in
example (h : slow 5000 = 12497500) : slow 5000 = 12497500 := by
  coaes? (defs := [slow])
