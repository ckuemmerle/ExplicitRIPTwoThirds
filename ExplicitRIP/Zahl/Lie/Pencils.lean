/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Lie.Pencils.Families
public import ExplicitRIP.Zahl.Elementary

/-!
# Maximal pencils of contacting spheres

Affine null lines characterize contact pencils. The point and direction
families supply maximal pencils, with distinct indices, and the direction
richness count satisfies the elementary division bound.
-/

public section

namespace ExplicitRIP.Zahl

variable {F : Type*} [Field F]

set_option linter.unusedFintypeInType false in
/-- Rich direction fibers are bounded by the number of spheres divided by richness. -/
theorem parallelRichCount_le_div [Fintype F]
    (S : Finset (Sphere F)) (k : ℕ) (hk : 1 ≤ k) :
    (parallelRichCount S k : ℝ) ≤ (S.card : ℝ) / (k : ℝ) := by
  apply (le_div_iff₀ (Nat.cast_pos.mpr hk : (0 : ℝ) < k)).2
  rw [mul_comm]
  exact_mod_cast parallelRichCount_mul_le_card S k

end ExplicitRIP.Zahl
