/-
# Exercise 3 — Euclid: there are infinitely many primes

Informal proof: let `m = n! + 1` and let `p` be its smallest prime factor.
If `p ≤ n` then `p ∣ n!`, and since `p ∣ n! + 1` we get `p ∣ 1` — impossible.
So `p > n`.

Rule: do NOT just call Mathlib's `Nat.exists_infinite_primes` — the point is to
formalize the argument yourself.

Lemmas you will need (check them with `#check` to see their exact statements):
* `Nat.minFac_prime : n ≠ 1 → (Nat.minFac n).Prime`
* `Nat.minFac_dvd   : Nat.minFac n ∣ n`
* `Nat.factorial_pos : 0 < n !`
* `Nat.dvd_factorial : 0 < m → m ≤ n → m ∣ n !`
* `Nat.dvd_add_right : a ∣ b → (a ∣ b + c ↔ a ∣ c)`
* `Nat.Prime.pos`, `Nat.Prime.one_lt`, `Nat.le_of_dvd`

Useful tactics: `set`, `refine ⟨_, ?_, _⟩`, `by_contra h`, `push Not at h`, `omega`.
-/
import Mathlib

namespace LeanProofs.InfinitePrimes

theorem exists_prime_gt (n : ℕ) : ∃ p, n < p ∧ p.Prime := by
  set m := n.factorial + 1 with hm_def
  have hm : m ≠ 1 := by
    have := Nat.factorial_pos n
    omega
  have hp : m.minFac.Prime := Nat.minFac_prime hm
  refine ⟨m.minFac, ?_, hp⟩
  -- Goal: n < m.minFac. Suppose not.
  by_contra h
  push Not at h                                      -- h : m.minFac ≤ n
  -- p ≤ n, so p divides n!
  have h1 : m.minFac ∣ n.factorial := Nat.dvd_factorial hp.pos h
  -- p divides n! and n! + 1, so p divides 1
  have h2 : m.minFac ∣ 1 := (Nat.dvd_add_right h1).mp (Nat.minFac_dvd m)
  -- p ∣ 1 forces p ≤ 1 ...
  have h3 : m.minFac ≤ 1 := Nat.le_of_dvd one_pos h2
  -- ... but primes are > 1
  have h4 : 1 < m.minFac := hp.one_lt                  -- (C) your turn
  omega

end LeanProofs.InfinitePrimes
