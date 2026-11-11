/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.ConstructionBarrier.Star

/-!
# Equal-magnitude star supports

Testing a Gram error on a coordinate vector gives a sparsity bound from any
column containing many entries of equal absolute value.

Source: [KM, proof of Proposition 10].
-/

public section

open scoped Matrix BigOperators

namespace ExplicitRIP.TwoDistanceBarrier

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]

/-- A star detects the squared magnitudes of its leaves regardless of their signs. -/
theorem star_abs_energy_le (Φ : Matrix I J ℝ) (v : J) (T : Finset J) (μ : ℝ)
    (hv : v ∉ T) (hT : ∀ i ∈ T, |(Φᴴ * Φ - 1 : Matrix J J ℝ) i v| = μ)
    (k : ℕ) (hk : 1 ≤ k) :
    ((min (k - 1) T.card : ℕ) : ℝ) * μ ^ 2 ≤ ripConstant Φ k ^ 2 := by
  classical
  obtain ⟨U, hUT, hUc⟩ := Finset.exists_subset_card_eq (min_le_right (k - 1) T.card)
  have hvU : v ∉ U := fun h => hv (hUT h)
  let S := insert v U
  have hSc : S.card ≤ k := by
    rw [Finset.card_insert_of_notMem hvU, hUc]
    have := min_le_left (k - 1) T.card
    omega
  have h := Actbar.principal_column_energy_le Φ S k hSc ⟨v, Finset.mem_insert_self v U⟩
  have hsum : (∑ i : S, ((Φᴴ * Φ - 1 : Matrix J J ℝ) i.val v) ^ 2) =
      ∑ i ∈ S, ((Φᴴ * Φ - 1 : Matrix J J ℝ) i v) ^ 2 := by
    exact (Finset.sum_subtype (p := fun i : J => i ∈ S) S (fun _ => Iff.rfl)
      (fun i : J => ((Φᴴ * Φ - 1 : Matrix J J ℝ) i v) ^ 2)).symm
  rw [hsum] at h
  have hU : (∑ i ∈ U, ((Φᴴ * Φ - 1 : Matrix J J ℝ) i v) ^ 2) =
      ((min (k - 1) T.card : ℕ) : ℝ) * μ ^ 2 := by
    have he (i : J) (hi : i ∈ U) : ((Φᴴ * Φ - 1 : Matrix J J ℝ) i v) ^ 2 = μ ^ 2 := by
      rw [← hT i (hUT hi), sq_abs]
    simp only [Finset.sum_congr rfl he, Finset.sum_const, nsmul_eq_mul, hUc]
  rw [← hU]
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_insert v U)
    (fun i _ _ => sq_nonneg _)).trans h

/-- A star of energy at least one gives the uniform lower restricted-isometry bound. -/
theorem min_sqrt_le_ripConstant (Φ : Matrix I J ℝ) (v : J) (T : Finset J) (μ : ℝ)
    (hμ : 0 ≤ μ) (hv : v ∉ T)
    (hT : ∀ i ∈ T, |(Φᴴ * Φ - 1 : Matrix J J ℝ) i v| = μ)
    (hlarge : 1 ≤ (T.card : ℝ) * μ ^ 2) (k : ℕ) (hk : 1 ≤ k) :
    min (μ * Real.sqrt ((k : ℝ) - 1)) 1 ≤ ripConstant Φ k := by
  have hstar := star_abs_energy_le Φ v T μ hv hT k hk
  have hsq : min (μ * Real.sqrt ((k : ℝ) - 1)) 1 ^ 2 ≤ ripConstant Φ k ^ 2 := by
    by_cases hkt : k - 1 ≤ T.card
    · rw [min_eq_left hkt, Nat.cast_sub hk, Nat.cast_one] at hstar
      have hsqrt : Real.sqrt ((k : ℝ) - 1) ^ 2 = (k : ℝ) - 1 :=
        Real.sq_sqrt (sub_nonneg.mpr (by exact_mod_cast hk))
      have hmin : min (μ * Real.sqrt ((k : ℝ) - 1)) 1 ^ 2 ≤
          (μ * Real.sqrt ((k : ℝ) - 1)) ^ 2 := by
        apply pow_le_pow_left₀ (le_min (mul_nonneg hμ (Real.sqrt_nonneg _)) zero_le_one)
        exact min_le_left _ _
      exact hmin.trans (by simpa only [mul_pow, hsqrt, mul_comm] using hstar)
    · rw [min_eq_right (le_of_not_ge hkt)] at hstar
      have hmin : min (μ * Real.sqrt ((k : ℝ) - 1)) 1 ^ 2 ≤ (1 : ℝ) ^ 2 := by
        exact pow_le_pow_left₀
          (le_min (mul_nonneg hμ (Real.sqrt_nonneg _)) zero_le_one) (min_le_right _ _) 2
      exact hmin.trans (by simpa only [one_pow] using hlarge.trans hstar)
  exact (sq_le_sq₀ (le_min (mul_nonneg hμ (Real.sqrt_nonneg _)) zero_le_one)
    (Actbar.rip_nonneg Φ k)).mp hsq

end ExplicitRIP.TwoDistanceBarrier
