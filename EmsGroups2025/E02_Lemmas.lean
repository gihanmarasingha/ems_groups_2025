import EmsGroups2025.E01_Basics


variable {G : Type*} {a b c d : G} [Group G]

example : a * 1 = a := by rw [mul_one a]
example : 1 * a = a := by rw [one_mul a]
example : (a * b) * c = a * (b * c) := by rw [mul_assoc a b c]
example : a⁻¹ * a = 1 := by rw [inv_mul_cancel a]

namespace ems

open ems

example (h : a * b = a * c) : b = c := by
  apply mul_left_cancel  h

lemma mul_inv_self : b * b⁻¹ = 1 := by
  sorry

lemma inv_eq_of_mul_eq_one (h : a * b = 1) : a⁻¹ = b := by
  sorry

end ems
