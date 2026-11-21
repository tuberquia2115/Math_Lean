/-
# Exercise 5 — Abstract algebra

Classic textbook exercise: if every element of a group squares to the identity,
the group is abelian.

Informal proof: `x * x = 1` means `x⁻¹ = x` for every `x`. Then
`a * b = (a * b)⁻¹ = b⁻¹ * a⁻¹ = b * a`.

Lemmas:
* `inv_eq_of_mul_eq_one_right : a * b = 1 → a⁻¹ = b`
* `mul_inv_rev : (a * b)⁻¹ = b⁻¹ * a⁻¹`

Tip: a `calc` block mirrors the informal chain of equalities exactly:

  calc a * b = (a * b)⁻¹ := ...
    _ = b⁻¹ * a⁻¹ := ...
    _ = b * a := ...
-/
import Mathlib

namespace LeanProofs.GroupExercise

theorem comm_of_sq_one {G : Type*} [Group G] (h : ∀ x : G, x * x = 1) (a b : G) :
    a * b = b * a := by
  have inv_self : ∀ x : G, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (h x)
  calc
    a * b = (a * b)⁻¹ := (inv_self (a * b)).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [inv_self a, inv_self b]
end LeanProofs.GroupExercise
