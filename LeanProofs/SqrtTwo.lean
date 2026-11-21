/-
# Exercise 4 — √2 is irrational (number-theory core)

The heart of the classical proof: there are no natural numbers `a, b` with `b ≠ 0`
and `a² = 2b²`.

Informal proof (infinite descent): if `a² = 2b²` then `a²` is even, so `a` is even,
say `a = 2c`. Then `4c² = 2b²`, i.e. `b² = 2c²` — a smaller solution, since `b < a`.
Strong induction on `a` turns "smaller solution" into a contradiction.

Hints:
* Start with `induction a using Nat.strong_induction_on generalizing b with | _ a ih => ...`
* `Nat.even_pow : Even (m ^ n) ↔ Even m ∧ n ≠ 0`
* `obtain ⟨c, rfl⟩ := ha` replaces `a` by `c + c` once you know `Even a`.
* `nlinarith` proves the nonlinear (in)equalities like `b ^ 2 = 2 * c ^ 2` and `b < c + c`.

Stretch goal: derive `Irrational (Real.sqrt 2)` from this lemma (Mathlib's own proof is
`irrational_sqrt_two` — again, try it yourself first).
-/
import Mathlib

namespace LeanProofs.SqrtTwo

theorem sq_ne_two_mul_sq (a b : ℕ) (hb : b ≠ 0) : a ^ 2 ≠ 2 * b ^ 2 := by
  induction a using Nat.strong_induction_on generalizing b with
  | _ a ih =>
    intro h
    have ha : Even a := by
      have : Even (a ^ 2) := ⟨b ^ 2, by rw [h]; ring⟩
      exact (Nat.even_pow.mp this).1
    obtain ⟨c, rfl⟩ := ha
    have hb2 : b ^ 2 = 2 * c ^ 2 := by nlinarith
    have hc : c ≠ 0 := by rintro rfl; simp at hb2; exact hb hb2
    have hlt : b < c + c := by nlinarith [Nat.pos_of_ne_zero hb, Nat.pos_of_ne_zero hc]
    exact ih b hlt c hc hb2

end LeanProofs.SqrtTwo
