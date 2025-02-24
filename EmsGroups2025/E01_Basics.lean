import Mathlib.Tactic

variable (G : Type*) (a b c d : G) [Group G]

example : a * 1 = a := by rw [mul_one a]
example : 1 * a = a := by rw [one_mul a]
example : (a * b) * c = a * (b * c) := by rw [mul_assoc a b c]
example : a⁻¹ * a = 1 := by rw [inv_mul_cancel a]

namespace ems

example : a * (b * (1 * c)) = (a * b) * c :=
  calc
    a * (b * (1 * c))
    _ = a * (b *  c)  := by rw [one_mul c]
    _ = (a * b) * c   := by rw [mul_assoc a b c]

example : a * (b * (1 * c)) = (a * b) * c :=
  calc
    a * (b * (1 * c))
    _ = a * (b *  c)  := by rw [one_mul]
    _ = (a * b) * c   := by rw [mul_assoc]

/-
Fill in the sorry's in the example below!
-/

example : a * (b * (d * c)) = (a * b) * (d * c) :=
  calc
    a * (b * (d * c))
    _ = a * ((b * d) * c)  := by rw [mul_assoc b d c]
    _ = (a * (b * d)) * c  := by rw [mul_assoc a (b * d) c]
    _ = ((a * b) * d) * c  := by sorry
    _ = (a * b) * (d * c)  := by sorry

/-
Below, type `⁻¹` as `\⁻¹`, followed by a space (if needed).

You'll need to add an additional line of calculation to complete the proof.
-/

example : a⁻¹ * (a * b) = b :=
  calc
    a⁻¹ * (a * b)
    _ = (a⁻¹ * a) * b  := by rw [mul_assoc]
    _ = b              := by sorry

/-
In the example below, you'll need to add many lines of calculation!
-/

example : (b⁻¹ * a⁻¹) * (a * b) = 1 :=
  calc
    (b⁻¹ * a⁻¹) * (a * b)
    _ = 1                       := by sorry

/-
We can rewrite using a hypothesis via `rw [h]` where `h` is the hypothesis.
-/

example (h : a * b = c) : a * (b * a) = c * a :=
  calc
    a * (b * a)
    _ = (a * b) * a  := by sorry
    _ = c * a        := by rw [h]

/-
The following proof is a bit more challenging!
-/

lemma mul_left_cancel  (h : a * b = a * c) : b = c :=
  calc
    b
    _ = c              := by sorry

end ems
