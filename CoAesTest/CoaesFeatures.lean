/-
Tests for the CoAes extensions over Aesop:

1. `unfold` via `(defs := [...])` has the highest priority of all rules and
   supports recursive definitions (each definition is unfolded at most once
   per goal).
2. `(no_unfold := [...])` blocks definitions from being unfolded.
3. Standalone closing tactics (`simp`, `simp_all`, `omega`, `decide`, `grind`)
   run before `intro` and are recorded in `coaes?` scripts as their bare
   names.
4. `coaes?` prints scripts in standard Lean format (indentation, `·` bullets)
   and prefers simple tactics (`simp_all`) over decorated ones
   (`simp_all only [...]`).
-/
import CoAes

set_option coaes.check.all true

-- § 1. Standalone closers close goals and are reported as bare tactics. ------

example (a b : Nat) (h : a ≤ b) : a ≤ b + 1 := by
  coaes

/--
info: Try this:

  [apply]   omega
-/
#guard_msgs in
example (a b : Nat) (h : a ≤ b) : a ≤ b + 1 := by
  coaes? -- expect: omega

-- Closers have higher priority than `intro`: the whole quantified goal is
-- closed by a single `simp`, not by `intro n` followed by `simp`.
/--
info: Try this:

  [apply]   simp
-/
#guard_msgs in
example : ∀ n : Nat, n + 0 = n := by
  coaes? -- expect: simp

/--
info: Try this:

  [apply]   simp
-/
#guard_msgs in
example : (2 : Nat) + 2 = 4 := by
  coaes? -- expect: simp (or decide)

-- § 2. Simple `simp_all` is preferred over `simp_all only [...]`. ------------

opaque P : Nat → Prop

/--
info: Try this:

  [apply]   simp_all
-/
#guard_msgs in
example (n : Nat) (h : P (n + 0)) : P n := by
  coaes? -- expect: simp_all

-- § 3. `(defs := [...])`: unfold with highest priority. ----------------------

def myMin (a b : Nat) : Nat :=
  if a ≤ b then a else b

-- Not provable while `myMin` stays folded.
example (a b : Nat) : myMin a b ≤ a ∨ myMin a b ≤ b := by
  fail_if_success coaes
  coaes (defs := [myMin])

/--
info: Try this:

  [apply]     unfold myMin
    grind
-/
#guard_msgs in
example (a b : Nat) : myMin a b ≤ a ∨ myMin a b ≤ b := by
  coaes? (defs := [myMin]) -- expect: unfold myMin; ...

-- § 4. Recursive definitions are allowed in `(defs := [...])` ----------------
-- (the attribute-based unfold rule rejects them). Each definition is unfolded
-- at most once per goal, so the search terminates.

def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => n + 1 + sumTo n

example : sumTo 3 = 6 := by
  coaes (defs := [sumTo])

/--
info: Try this:

  [apply]     unfold sumTo
    simp
-/
#guard_msgs in
example : sumTo 0 = 0 := by
  coaes? (defs := [sumTo])

-- § 5. `(no_unfold := [...])` blocks unfolding. ------------------------------

example (a b : Nat) : myMin a b ≤ a ∨ myMin a b ≤ b := by
  fail_if_success coaes (defs := [myMin]) (no_unfold := [myMin])
  coaes (defs := [myMin])

-- `no_unfold` also blocks globally registered unfold rules.
@[coaes norm unfold]
def myMax (a b : Nat) : Nat :=
  if a ≤ b then b else a

example (a b : Nat) : a ≤ myMax a b := by
  fail_if_success coaes (no_unfold := [myMax])
  coaes

-- § 6. Structured script output with `·` bullets. ----------------------------

axiom p0 : P 0

opaque Q : Prop

axiom q0 : Q

example : P 0 ∧ Q := by
  coaes (add safe apply p0) (add safe apply q0)

/--
info: Try this:

  [apply]     apply And.intro
    · apply p0
    · apply q0
-/
#guard_msgs in
example : P 0 ∧ Q := by
  coaes? (add safe apply p0) (add safe apply q0) -- expect: bullets
