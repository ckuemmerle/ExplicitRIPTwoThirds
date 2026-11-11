/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.UnsignedBarrier.Basic
public import ExplicitRIP.Analysis.UnsignedBarrier.FiniteSums
public import ExplicitRIP.Analysis.UnsignedBarrier.Algebra
public import ExplicitRIP.Frozen.FramePotential

/-!
# The unsigned barrier for every sparsity

The window estimate extends to `k ≥ 1`. Beyond the number of columns,
the coordinate-vector tests bound the full Gram-error energy by `n Δ_k²`.
-/

public section

open scoped BigOperators Matrix
open Finset

namespace ExplicitRIP.AllSparsity

theorem unsigned_barrier_finite (m n : ℕ) (Φ : Matrix (Fin m) (Fin n) ℂ)
    (hunit : ∀ j, ∑ i, ‖Φ i j‖ ^ 2 = 1) (k : ℕ) (hk : 1 ≤ k) :
    ((n : ℝ) - m) * ((k : ℝ) - 1) ^ (3 / 2 : ℝ) /
      ((m : ℝ) * ((n : ℝ) - 1 + ((k : ℝ) - 1) ^ (3 / 2 : ℝ))) ≤
        unsignedRIPConstant Φ k ^ 2 := by
  by_cases hk1 : k = 1
  · subst k
    simp only [Nat.cast_one, sub_self,
      Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0), mul_zero, zero_div]
    exact sq_nonneg _
  have hk2 : 2 ≤ k := by omega
  have hkR : (1 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    linarith only [this]
  have hpow : 1 ≤ ((k : ℝ) - 1) ^ (3 / 2 : ℝ) :=
    Real.one_le_rpow hkR (by norm_num)
  by_cases hmn : m < n
  · by_cases hkn : k ≤ n
    · have hk : 2 ≤ k := hk2
      let D := unsignedRIPConstant Φ k
      let H : Fin n → Fin n → ℝ := fun i j => ‖(Φᴴ * Φ - (1 : Matrix (Fin n) (Fin n) ℂ)) i j‖
      have hD : 0 ≤ D := Absbar.unsignedRIPConstant_nonneg Φ k
      have hm : (0 : ℝ) < m := by
        exact_mod_cast Absbar.rows_pos_of_unit_columns m n Φ hunit (by omega)
      have hn : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
      have hr : 0 < k - 1 := by omega
      have hrR : (0 : ℝ) < (k : ℝ) - 1 := by
        have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
        linarith
      have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
      have hmass : (∑ i, ∑ j, H i j) ≤
          (n : ℝ) * ((n : ℝ) - 1) / ((k : ℝ) - 1) * D := by
        have h := Absbar.total_mass_le H
          (fun i => by simp only [H, ExplicitRIP.Flat.gram_error_diag Φ hunit, norm_zero]) D k hk
          (by simpa only [Fintype.card_fin] using hkn)
          (fun S hS => by simpa only [hS] using Absbar.support_mass_le Φ k S hS.le)
        simpa only [Fintype.card_fin] using h
      have hrow (i : Fin n) :
          (∑ j, H j i ^ 2) ≤ D ^ 2 + D / Real.sqrt ((k : ℝ) - 1) * ∑ j, H j i := by
        rw [← hcast]
        apply Absbar.sum_sq_le_of_support_bound (fun j => H j i) (fun j => norm_nonneg _) D hD
          (k - 1) hr
        intro S hS
        exact Absbar.support_column_sq_le Φ k i S (by omega)
      have henergy : (∑ i, ∑ j, H i j ^ 2) ≤
          (n : ℝ) * D ^ 2 + D / Real.sqrt ((k : ℝ) - 1) *
            ((n : ℝ) * ((n : ℝ) - 1) / ((k : ℝ) - 1) * D) := by
        calc
          _ = ∑ i, ∑ j, H j i ^ 2 := sum_comm
          _ ≤ ∑ i, (D ^ 2 + D / Real.sqrt ((k : ℝ) - 1) * ∑ j, H j i) :=
            sum_le_sum fun i _ => hrow i
          _ = (n : ℝ) * D ^ 2 + D / Real.sqrt ((k : ℝ) - 1) * ∑ i, ∑ j, H i j := by
            rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
              ← mul_sum, sum_comm]
          _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hmass
            (div_nonneg hD (Real.sqrt_nonneg _)))
      exact Absbar.barrier_of_energy_bound m n ((k : ℝ) - 1) D hm hn hrR
        ((ExplicitRIP.frame_potential_bound m n Φ hunit).2.trans henergy)
    have hmN : 0 < m := Absbar.rows_pos_of_unit_columns m n Φ hunit (by omega)
    have hm : (0 : ℝ) < m := by exact_mod_cast hmN
    have hn : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have hn0 : (0 : ℝ) < n := lt_trans zero_lt_one hn
    have hnm : (0 : ℝ) ≤ (n : ℝ) - m := by
      exact sub_nonneg.mpr (by exact_mod_cast hmn.le)
    let D := unsignedRIPConstant Φ k
    let H : Fin n → Fin n → ℝ := fun i j =>
      ‖(Φᴴ * Φ - (1 : Matrix (Fin n) (Fin n) ℂ)) i j‖
    have hcol (i : Fin n) : (∑ j, H j i ^ 2) ≤ D ^ 2 := by
      exact Absbar.support_column_sq_le Φ k i univ
        (by simpa only [card_univ, Fintype.card_fin] using (show n + 1 ≤ k by omega))
    have henergy : (∑ i, ∑ j, H i j ^ 2) ≤ (n : ℝ) * D ^ 2 := by
      calc
        _ = ∑ i, ∑ j, H j i ^ 2 := sum_comm
        _ ≤ ∑ i : Fin n, D ^ 2 := sum_le_sum fun i _ => hcol i
        _ = _ := by simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hfull : ((n : ℝ) - m) / m ≤ D ^ 2 := by
      apply (mul_le_mul_iff_right₀ hn0).mp
      simpa only [mul_div_assoc] using
        (ExplicitRIP.frame_potential_bound m n Φ hunit).2.trans henergy
    have hden : 0 < (n : ℝ) - 1 + ((k : ℝ) - 1) ^ (3 / 2 : ℝ) := by
      linarith only [hn, hpow]
    calc
      _ = (((n : ℝ) - m) / m) *
          (((k : ℝ) - 1) ^ (3 / 2 : ℝ) /
            ((n : ℝ) - 1 + ((k : ℝ) - 1) ^ (3 / 2 : ℝ))) := by
          rw [div_mul_div_comm]
      _ ≤ (((n : ℝ) - m) / m) * 1 := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg hnm hm.le)
        apply (div_le_one hden).mpr
        linarith only [hn]
      _ ≤ D ^ 2 := by simpa only [mul_one] using hfull
  · have hnm : (n : ℝ) - m ≤ 0 := by
      exact sub_nonpos.mpr (by exact_mod_cast (show n ≤ m by omega))
    have hden : 0 ≤ (m : ℝ) * ((n : ℝ) - 1 + ((k : ℝ) - 1) ^ (3 / 2 : ℝ)) := by
      apply mul_nonneg (Nat.cast_nonneg _)
      linarith only [Nat.cast_nonneg (α := ℝ) n, hpow]
    exact (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg hnm (le_trans zero_le_one hpow)) hden).trans
      (sq_nonneg _)

end ExplicitRIP.AllSparsity
