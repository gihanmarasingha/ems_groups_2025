/-
# Cosets
-/
import Mathlib.Tactic

variable {G : Type*} {a b c : G} [Group G]

variable (H : Subgroup G)

def leftCoset [Mul G] (a : G) (H : Set G) : Set G :=
  (fun x => a * x) '' H

infixl:70 " • " => leftCoset

example : (1 : G) • (H : Set G) = H := by
  simp [leftCoset]


example : a • (H : Set G) = b • H ↔ a⁻¹ * b ∈ H := by
  constructor
  ·  sorry
  · sorry
