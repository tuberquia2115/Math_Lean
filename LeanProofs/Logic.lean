/-
# Exercise 1 — Propositional logic (warm-up)

Replace every `sorry` with a proof. Put your cursor inside a proof in VS Code:
the "Lean Infoview" panel shows the current goal (after `⊢`) and your hypotheses.

Useful tactics: `intro`, `exact`, `constructor`, `rcases`, `left`, `right`, `apply`.
Term-mode tip: `⟨x, y⟩` builds an `∧`; `h.1` / `h.2` take it apart.
-/
import Mathlib

namespace LeanProofs.Logic

/-- `∧` is commutative. Hint: `exact ⟨h.2, h.1⟩` style, or `constructor`. -/
theorem and_swap (p q : Prop) (h : p ∧ q) : q ∧ p := by
  exact ⟨h.2, h.1⟩

/-- `∨` is commutative. Hint: `rcases h with hp | hq`, then `right` / `left`. -/
theorem or_swap (p q : Prop) (h : p ∨ q) : q ∨ p := by
  rcases h with hp | hq
  · right; exact hp
  · left; exact hq

/-- Implication is transitive. Hint: `intro hp`, then `exact hqr (hpq hp)`. -/
theorem imp_trans (p q r : Prop) (hpq : p → q) (hqr : q → r) : p → r := by
  intro hp
  exact hqr (hpq hp)

/-- Double-negation introduction. `¬p` *means* `p → False`, so start with `intro hn`. -/
theorem not_not_intro (p : Prop) (hp : p) : ¬¬p := by
  intro hn
  exact hn hp

end LeanProofs.Logic
