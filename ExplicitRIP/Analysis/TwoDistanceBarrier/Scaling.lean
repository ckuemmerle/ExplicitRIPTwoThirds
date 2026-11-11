/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib

/-!
# Coherence and the two-thirds sparsity scale

Squaring a coherence-weighted square-root bound controls normalized sparsity.
When the dimension diverges and distortion vanishes, this gives a little-o bound.

Source: [KM, Proposition 10].
-/

public section

open Filter Asymptotics
open scoped Topology

namespace ExplicitRIP.TwoDistanceBarrier

/-- Squaring the coherence estimate controls normalized sparsity. -/
theorem normalized_sparsity_le (m : ℝ) (k : ℕ) (C δ : ℝ)
    (hm : 0 < m) (hk : 1 ≤ k) (hC : 0 < C) (hδ : 0 ≤ δ)
    (h : C * m ^ (-(1 / 3 : ℝ)) * Real.sqrt ((k : ℝ) - 1) ≤ δ) :
    (k : ℝ) / m ^ (2 / 3 : ℝ) ≤ (m ^ (2 / 3 : ℝ))⁻¹ + δ ^ 2 / C ^ 2 := by
  have ht : 0 < m ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hm _
  have hpow : (m ^ (-(1 / 3 : ℝ))) ^ 2 * m ^ (2 / 3 : ℝ) = 1 := by
    rw [← Real.rpow_mul_natCast hm.le, ← Real.rpow_add hm]
    norm_num
  have hsqrt : Real.sqrt ((k : ℝ) - 1) ^ 2 = (k : ℝ) - 1 :=
    Real.sq_sqrt (sub_nonneg.mpr (by exact_mod_cast hk))
  have hsq := (sq_le_sq₀ (by positivity) hδ).mpr h
  rw [mul_pow, mul_pow, hsqrt] at hsq
  have hmul := mul_le_mul_of_nonneg_right hsq ht.le
  have hleft : C ^ 2 * (k - 1 : ℝ) ≤ δ ^ 2 * m ^ (2 / 3 : ℝ) := by
    calc
      _ = C ^ 2 * (m ^ (-(1 / 3 : ℝ))) ^ 2 * ((k : ℝ) - 1) *
          m ^ (2 / 3 : ℝ) := by rw [show C ^ 2 * (m ^ (-(1 / 3 : ℝ))) ^ 2 *
            ((k : ℝ) - 1) * m ^ (2 / 3 : ℝ) =
            C ^ 2 * ((k : ℝ) - 1) *
              ((m ^ (-(1 / 3 : ℝ))) ^ 2 * m ^ (2 / 3 : ℝ)) by ring, hpow, mul_one]
      _ ≤ _ := hmul
  apply (div_le_iff₀ ht).mpr
  have hc2 : 0 < C ^ 2 := sq_pos_of_pos hC
  have hdiv : (k : ℝ) - 1 ≤ δ ^ 2 * m ^ (2 / 3 : ℝ) / C ^ 2 := by
    apply (le_div_iff₀ hc2).mpr
    nlinarith only [hleft]
  calc
    (k : ℝ) ≤ 1 + δ ^ 2 * m ^ (2 / 3 : ℝ) / C ^ 2 := by linarith only [hdiv]
    _ = ((m ^ (2 / 3 : ℝ))⁻¹ + δ ^ 2 / C ^ 2) * m ^ (2 / 3 : ℝ) := by
      rw [add_mul, inv_mul_cancel₀ ht.ne']
      ring

/-- An eventually vanishing coherence-weighted star norm implies the two-thirds little-o bound. -/
theorem sparsity_isLittleO (m k : ℕ → ℕ) (δ : ℕ → ℝ) (C : ℝ) (hC : 0 < C)
    (hm : Tendsto (fun j => (m j : ℝ)) atTop atTop)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hbound : ∀ᶠ j in atTop, 1 ≤ k j ∧ 0 ≤ δ j ∧
      C * (m j : ℝ) ^ (-(1 / 3 : ℝ)) * Real.sqrt ((k j : ℝ) - 1) ≤ δ j) :
    (fun j => (k j : ℝ)) =o[atTop] (fun j => (m j : ℝ) ^ (2 / 3 : ℝ)) := by
  have hscale : Tendsto (fun j => (m j : ℝ) ^ (2 / 3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hm
  have hmajor : Tendsto
      (fun j => ((m j : ℝ) ^ (2 / 3 : ℝ))⁻¹ + δ j ^ 2 / C ^ 2) atTop (𝓝 0) := by
    simpa only [Pi.inv_apply, zero_pow (by decide : 2 ≠ 0), zero_div, add_zero] using
      hscale.inv_tendsto_atTop.add ((hδ.pow 2).div_const (C ^ 2))
  have hrow := hm.eventually_gt_atTop 0
  have hquot : Tendsto (fun j => (k j : ℝ) / (m j : ℝ) ^ (2 / 3 : ℝ))
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun j => by positivity) ?_ hmajor
    filter_upwards [hbound, hrow] with j hj hmj
    exact normalized_sparsity_le (m j) (k j) C (δ j) hmj hj.1 hC hj.2.1 hj.2.2
  apply isLittleO_of_tendsto' ?_ hquot
  filter_upwards [hrow] with j hj
  exact fun h => False.elim ((Real.rpow_pos_of_pos hj (2 / 3 : ℝ)).ne' h)

end ExplicitRIP.TwoDistanceBarrier
