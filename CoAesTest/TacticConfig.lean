/-
Copyright (c) 2021 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import CoAes

set_option coaes.check.all true
set_option coaes.smallErrorMessages true

inductive Even : Nat → Prop
| zero : Even 0
| plus_two {n} : Even n → Even (n + 2)

inductive Odd : Nat → Prop
| one : Odd 1
| plus_two {n} : Odd n → Odd (n + 2)

inductive EvenOrOdd : Nat → Prop
| even {n} : Even n → EvenOrOdd n
| odd {n} : Odd n → EvenOrOdd n

-- We can add constants as rules.
example : EvenOrOdd 3 := by
  coaes
    (add safe [Even.zero, Even.plus_two, Odd.one, Odd.plus_two],
         unsafe [apply 50% EvenOrOdd.even, 50% EvenOrOdd.odd])

-- Same with local hypotheses, or a mix.
example : EvenOrOdd 3 := by
  have h : ∀ n, Odd n → EvenOrOdd n := λ _ p => EvenOrOdd.odd p
  coaes
    (add safe [Odd.one, Odd.plus_two], unsafe [EvenOrOdd.even 50%, h 50%])
    (erase CoAes.BuiltinRules.applyHyps) -- This rule subsumes h.

attribute [coaes 50%] Even.zero Even.plus_two

-- We can also erase global rules...

/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : EvenOrOdd 2 := by
  coaes (add safe EvenOrOdd.even) (erase Even.zero)
    (config := { terminal := true })

example : EvenOrOdd 2 := by
  coaes (add safe EvenOrOdd.even)

-- ... as well as local ones (but what for?).


/--
error: tactic 'coaes' failed, failed to prove the goal after exhaustive search.
-/
#guard_msgs in
example : EvenOrOdd 2 := by
  have h : ∀ n, Even n → EvenOrOdd n := λ _ p => EvenOrOdd.even p
  coaes (add safe h) (erase CoAes.BuiltinRules.applyHyps, h)
    (config := { terminal := true })

example : EvenOrOdd 2 := by
  have h : ∀ n, Even n → EvenOrOdd n := λ _ p => EvenOrOdd.even p
  coaes (add safe h) (erase CoAes.BuiltinRules.applyHyps)
