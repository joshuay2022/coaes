import CoAes

set_option coaes.check.all true
set_option coaes.smallErrorMessages true

@[coaes 90%]
def myTacGen : CoAes.TacGen := fun _ => do
  return #[("exact ⟨val - f { val := val, property := property }, fun a ha => by simpa⟩",
            0.9)]

/-- error: tactic 'coaes' failed, made no progress -/
#guard_msgs in
theorem foo (f : { x // 0 < x } → { x // 0 < x }) (val : Nat)
    (property : 0 < val) :
    ∃ w x, ∀ (a : Nat) (b : 0 < a), ↑(f { val := a, property := b }) = w * a + x := by
  constructor
  coaes
