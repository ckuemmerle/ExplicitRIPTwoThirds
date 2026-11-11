/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.UnsignedBarrier.AllSparsity.Finite

/-!
# The asymptotic unsigned barrier without a sparsity window

For a sequence with eventually unit-norm columns, `n > 0` and `k ≥ 1`, assume `m/n → 0` and
vanishing unsigned distortion. The finite inequality then gives `k - 1 = o(m^(2/3))`. The endpoint
`k = 1` requires no growth of the number of rows.
-/

public section

open scoped BigOperators Matrix Topology
open Filter Asymptotics

namespace ExplicitRIP.AllSparsity

theorem eventually_sparsity_sub_one_le
    (m n k : ℕ → ℕ) (Φ : ∀ j, Matrix (Fin (m j)) (Fin (n j)) ℂ)
    (hdata : ∀ᶠ j in atTop,
      (∀ c, ∑ i, ‖Φ j i c‖ ^ 2 = 1) ∧ 1 ≤ k j ∧ 0 < n j)
    (hratio : Tendsto (fun j => (m j : ℝ) / n j) atTop (nhds 0))
    (hbound : ∀ᶠ j in atTop, unsignedRIPConstant (Φ j) (k j) ≤ 1) :
    ∀ᶠ j in atTop, (k j : ℝ) - 1 ≤
      (2 * unsignedRIPConstant (Φ j) (k j) ^ 2) ^ (2 / 3 : ℝ) *
        (m j : ℝ) ^ (2 / 3 : ℝ) := by
  have hsmall := hratio.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 4)
  filter_upwards [hdata, hbound, hsmall] with j hj hD hs
  obtain ⟨hunit, hk, hnN⟩ := hj
  have hmN : 0 < m j := Absbar.rows_pos_of_unit_columns (m j) (n j) (Φ j) hunit hnN
  have hm : (0 : ℝ) < m j := by exact_mod_cast hmN
  have hm1 : (1 : ℝ) ≤ m j := by exact_mod_cast (show 1 ≤ m j by omega)
  have hn0 : (0 : ℝ) < n j := by exact_mod_cast hnN
  have hreg1 : 4 * (m j : ℝ) ≤ n j := by
    have h := (div_le_iff₀ hn0).mp hs
    linarith only [h]
  have hn : (1 : ℝ) < n j := by linarith only [hm1, hreg1]
  have hsq : unsignedRIPConstant (Φ j) (k j) ^ 2 ≤ 1 := by
    simpa only [one_pow] using
      pow_le_pow_left₀ (Absbar.unsignedRIPConstant_nonneg (Φ j) (k j)) hD 2
  have hreg : 2 * (1 + unsignedRIPConstant (Φ j) (k j) ^ 2) * (m j : ℝ) ≤ n j := by
    have h := mul_le_mul_of_nonneg_right hsq hm.le
    nlinarith only [hreg1, h]
  by_cases hk1 : k j = 1
  · simp only [hk1, Nat.cast_one, sub_self]
    positivity
  have hr : (0 : ℝ) < (k j : ℝ) - 1 := by
    have hk2 : (2 : ℝ) ≤ k j := by exact_mod_cast (show 2 ≤ k j by omega)
    linarith only [hk2]
  have hp := Absbar.power_le_of_barrier (m j) (n j) ((k j : ℝ) - 1)
    (unsignedRIPConstant (Φ j) (k j)) hm hn hr hreg
    (unsigned_barrier_finite (m j) (n j) (Φ j) hunit (k j) hk)
  have hp' := Real.rpow_le_rpow (Real.rpow_nonneg hr.le _) hp
    (by norm_num : (0 : ℝ) ≤ 2 / 3)
  rw [← Real.rpow_mul hr.le, show (3 / 2 : ℝ) * (2 / 3) = 1 by norm_num,
    Real.rpow_one, Real.mul_rpow (by positivity :
      0 ≤ 2 * unsignedRIPConstant (Φ j) (k j) ^ 2) hm.le] at hp'
  exact hp'

theorem unsigned_barrier_littleO
    (m n k : ℕ → ℕ) (Φ : ∀ j, Matrix (Fin (m j)) (Fin (n j)) ℂ)
    (hdata : ∀ᶠ j in atTop,
      (∀ c, ∑ i, ‖Φ j i c‖ ^ 2 = 1) ∧ 1 ≤ k j ∧ 0 < n j)
    (hratio : Tendsto (fun j => (m j : ℝ) / n j) atTop (nhds 0))
    (hzero : Tendsto (fun j => unsignedRIPConstant (Φ j) (k j)) atTop (nhds 0)) :
    (fun j => (k j : ℝ) - 1) =o[atTop] (fun j => (m j : ℝ) ^ (2 / 3 : ℝ)) := by
  have hp := eventually_sparsity_sub_one_le m n k Φ hdata hratio
    (hzero.eventually_le_const (by norm_num : (0 : ℝ) < 1))
  have hsq : Tendsto (fun j => 2 * unsignedRIPConstant (Φ j) (k j) ^ 2)
      atTop (nhds 0) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero] using (hzero.pow 2).const_mul 2
  have hcoef : Tendsto
      (fun j => (2 * unsignedRIPConstant (Φ j) (k j) ^ 2) ^ (2 / 3 : ℝ))
      atTop (nhds 0) := hsq.rpow_const_nhds_zero (by norm_num : (0 : ℝ) < 2 / 3)
  apply isLittleO_iff.mpr
  intro c hc
  filter_upwards [hdata, hp, hcoef.eventually_le_const hc] with j hj hkj hC
  have hk : (0 : ℝ) ≤ (k j : ℝ) - 1 := by
    exact sub_nonneg.mpr (by exact_mod_cast hj.2.1)
  rw [Real.norm_of_nonneg hk,
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  exact hkj.trans (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (Nat.cast_nonneg _) _))

end ExplicitRIP.AllSparsity
