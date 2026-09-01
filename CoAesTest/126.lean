import CoAes

set_option coaes.check.all true

-- TODO simp_all introduces spurious metavariables in this example
set_option coaes.check.rules false
set_option coaes.check.tree false

theorem foo {a : Nat → Nat} (ha : a 0 = 37) :
    (match h : a 0 with | 42 => by simp_all | n => n) = 37 := by
  coaes
