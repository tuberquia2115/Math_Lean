/-
# Exercise 2 — Induction on ℕ

Pattern for an induction proof:

  induction n with
  | zero => ...           -- base case
  | succ k ih => ...      -- `ih` is the statement for `k`; prove it for `k + 1`

Useful tactics: `simp`, `simp only [sumTo]` (unfolds the definition), `rw [ih]`, `ring`.
-/
import Mathlib

open Finset

namespace LeanProofs.Induction

/-- `sumTo n = 0 + 1 + ⋯ + n`, defined by recursion. -/
def sumTo : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumTo n + (n + 1)

/-- Gauss's formula, stated without division: `2 · (0 + ⋯ + n) = n(n + 1)`.
Hint for the step: unfold `sumTo`, distribute with `mul_add`, rewrite with `ih`, finish with `ring`. -/
theorem two_mul_sumTo (n : ℕ) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => simp [sumTo]
  | succ k ih => simp only [sumTo]; rw [mul_add, ih]; ring

/-- The sum of the first `n` odd numbers is `n²`.
Hint: `Finset.sum_range_succ` splits off the last term of the sum. -/
theorem sum_odds (n : ℕ) : ∑ i ∈ range n, (2 * i + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ k ih => simp [Finset.sum_range_succ]; rw [ih]; ring

end LeanProofs.Induction
