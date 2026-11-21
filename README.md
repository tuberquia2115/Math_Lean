# Math_lean

Classic theorems formalized in **Lean 4** with **Mathlib**.

| File | Result | Topics |
|---|---|---|
| [`LeanProofs/Logic.lean`](LeanProofs/Logic.lean) | Basic propositional logic | `intro`, `exact`, `rcases`, anonymous constructors |
| [`LeanProofs/Induction.lean`](LeanProofs/Induction.lean) | Gauss's sum formula; sum of odd numbers = n² | recursion, induction, `Finset` sums, `ring` |
| [`LeanProofs/InfinitePrimes.lean`](LeanProofs/InfinitePrimes.lean) | Euclid: for every n there is a prime p > n | `Nat.minFac`, factorials, divisibility, proof by contradiction |
| [`LeanProofs/SqrtTwo.lean`](LeanProofs/SqrtTwo.lean) | No naturals with a² = 2b², b ≠ 0 (core of √2 ∉ ℚ) | strong induction, infinite descent, parity, `nlinarith` |
| [`LeanProofs/GroupExercise.lean`](LeanProofs/GroupExercise.lean) | A group where every x² = 1 is abelian | type classes, group lemmas, `calc` |

## Build

```sh
lake exe cache get   # download precompiled Mathlib (first time only)
lake build
```
