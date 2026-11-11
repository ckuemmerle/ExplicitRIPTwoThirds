/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib

/-!
# Power scales and bounded factors

Elementary real asymptotic tools for the scales in [KM, Lemma 5].
-/

public section

open Filter Asymptotics
open scoped Topology

namespace ExplicitRIP.SrgScaling

/-- A bounded factor times a sequence tending to zero tends to zero. -/
theorem bounded_mul_zero {f g : ℕ → ℝ}
    (hf : f =O[atTop] (fun _ => (1 : ℝ))) (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto (fun j => f j * g j) atTop (𝓝 0) := by
  have h := hf.mul_isLittleO ((isLittleO_one_iff ℝ).mpr hg : g =o[atTop] (fun _ => (1 : ℝ)))
  simpa only [Pi.mul_apply, mul_one, isLittleO_one_iff] using h

/-- Signs of absolute value one are uniformly bounded. -/
theorem signs_bounded (ε : ℕ → ℝ) (hε : ∀ j, ε j = 1 ∨ ε j = -1) :
    ε =O[atTop] (fun _ => (1 : ℝ)) := by
  apply IsBigO.of_bound 1
  exact Eventually.of_forall fun j => by rcases hε j with h | h <;> simp [h]

/-- The reciprocal cube root has cube equal to the reciprocal. -/
theorem scale_cube {m : ℝ} (hm : 0 < m) : m * (m ^ (-(1 / 3 : ℝ))) ^ 3 = 1 := by
  rw [← Real.rpow_mul_natCast hm.le]
  norm_num
  rw [Real.rpow_neg_one, mul_inv_cancel₀ hm.ne']

/-- The reciprocal of the dimension times the squared cube-root scale is that scale. -/
theorem scale_reciprocal_square {m : ℝ} (hm : 0 < m) :
    (m * (m ^ (-(1 / 3 : ℝ))) ^ 2)⁻¹ = m ^ (-(1 / 3 : ℝ)) := by
  apply inv_eq_of_mul_eq_one_right
  calc
    (m * (m ^ (-(1 / 3 : ℝ))) ^ 2) * m ^ (-(1 / 3 : ℝ)) =
        m * (m ^ (-(1 / 3 : ℝ))) ^ 3 := by ring
    _ = 1 := scale_cube hm

/-- Dividing the reciprocal dimension by the cube-root scale gives exponent `-2/3`. -/
theorem scale_reciprocal {m : ℝ} (hm : 0 < m) :
    1 / (m * m ^ (-(1 / 3 : ℝ))) = m ^ (-(2 / 3 : ℝ)) := by
  rw [one_div, mul_inv, ← Real.rpow_neg_one, ← Real.rpow_neg hm.le,
    ← Real.rpow_add hm]
  norm_num

/-- Cubic coherence is comparable with a constant. -/
theorem cubic_isTheta (m μ : ℕ → ℝ) (hm : ∀ j, 0 < m j)
    (hμ : μ =Θ[atTop] (fun j => m j ^ (-(1 / 3 : ℝ)))) :
    (fun j => m j * μ j ^ 3) =Θ[atTop] (fun _ => (1 : ℝ)) := by
  have h := (isTheta_refl m atTop).mul (hμ.pow 3)
  exact h.trans_eventuallyEq (Eventually.of_forall fun j => scale_cube (hm j))

/-- The reciprocal quadratic coherence scale has exponent `-1/3`. -/
theorem quadratic_reciprocal_isTheta (m μ : ℕ → ℝ) (hm : ∀ j, 0 < m j)
    (hμ : μ =Θ[atTop] (fun j => m j ^ (-(1 / 3 : ℝ)))) :
    (fun j => 1 / (m j * μ j ^ 2)) =Θ[atTop]
      (fun j => m j ^ (-(1 / 3 : ℝ))) := by
  have h := ((isTheta_refl m atTop).mul (hμ.pow 2)).inv
  simpa only [one_div] using h.trans_eventuallyEq
    (Eventually.of_forall fun j => scale_reciprocal_square (hm j))

/-- The reciprocal linear coherence scale has exponent `-2/3`. -/
theorem linear_reciprocal_isTheta (m μ : ℕ → ℝ) (hm : ∀ j, 0 < m j)
    (hμ : μ =Θ[atTop] (fun j => m j ^ (-(1 / 3 : ℝ)))) :
    (fun j => 1 / (m j * μ j)) =Θ[atTop] (fun j => m j ^ (-(2 / 3 : ℝ))) := by
  have h := ((isTheta_refl m atTop).mul hμ).inv
  simpa only [one_div] using h.trans_eventuallyEq
    (Eventually.of_forall fun j => by simpa only [one_div] using scale_reciprocal (hm j))

/-- Comparability with a reciprocal cube root forces vanishing coherence. -/
theorem coherence_zero (m μ : ℕ → ℝ) (hm : Tendsto m atTop atTop)
    (hμ : μ =Θ[atTop] (fun j => m j ^ (-(1 / 3 : ℝ)))) :
    Tendsto μ atTop (𝓝 0) := by
  exact hμ.tendsto_zero_iff.mpr
    ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp hm)

end ExplicitRIP.SrgScaling
