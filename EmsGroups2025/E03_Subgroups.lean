/-
# Subgroups

Let `G` be a group. A subset `H` of `G` is called a subgroup if it is nonempty
and closed under multiplication and taking inverses.

Let `H` be a subgroup of `G`. Then we have

`one_mem : (1 : G) ∈ H`
`mul_mum:  a ∈ H → b ∈ H → a * b ∈ H`
`inv_mul : a ∈ H → a⁻¹ ∈ H`

For example, suppose `G` is a group, and `H` is a subgroup of `G`.
-/
import Mathlib.Tactic


variable {G : Type*} {a b c : G} [Group G]

variable (H : Subgroup G)

example : (1 : G) ∈ H := by
  exact H.one_mem

example (h1 : a ∈ H) (h2 : b ∈ H) : a * b ∈ H := by
  exact H.mul_mem h1 h2


example (h1 : a ∈ H) : a⁻¹ ∈ H := by
  exact H.inv_mem h1

/-
We'll try using 'backward proof' for the next example. Use the `apply` tactic together with an
appropriate result. For example `apply H.inv_mem`. Use `apply` multiple times if necessary.
-/

example (h1 : a ∈ H) (h2 : b  ∈ H) : (a * b) * a⁻¹ ∈ H := by
  apply sorry


/-
Now we try a foward proof. We'll start by using the `have` tactic to introduce a new hypothesis,
`h3`, which states that `a * b ∈ H`.

The last line closes the goal by combining the results proved so far.
-/

example (h1 : a ∈ H) (h2 : b  ∈ H) : (a * b) * a⁻¹ ∈ H := by
  have h3 : a * b ∈ H := H.mul_mem h1 h2
  -- add another line here.
  exact H.mul_mem h3 sorry

namespace ems

variable (K : Subgroup G)

/-
The following result states that the intersection of two subgroups of `G` is a subgroup of `G`.
-/
instance : Min (Subgroup G) where
  min := fun
    | .mk H inv_mem' => fun
      | .mk K inv_mem' => {
        carrier := H.carrier ∩ K.carrier,
        mul_mem' := by
          sorry
        one_mem' := by
          sorry
        inv_mem' := by
          sorry
      }

end ems
