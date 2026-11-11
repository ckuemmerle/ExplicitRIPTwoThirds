/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.RIPOneTwo.Basic
public import ExplicitRIP.LinearAlgebra.FramePotential.Basic

/-!
# Coherence bounds the off-diagonal Gram energy

For unit columns, the diagonal Gram error vanishes and the other entries have modulus
at most the coherence. Counting the off-diagonal entries gives the upper half of Welch's bound.
-/

public section

open scoped BigOperators Matrix

namespace ExplicitRIP.Welch

/-- The squared Gram-error energy is at most the number of ordered distinct pairs times `μ²`. -/
theorem sum_norm_sq_gram_error_le (m n : ℕ) (Φ : Matrix (Fin m) (Fin n) ℂ)
    (hunit : ∀ j, ∑ i, ‖Φ i j‖ ^ 2 = 1) (hn : 1 ≤ n) :
    (∑ i, ∑ j, ‖(Φᴴ * Φ - (1 : Matrix (Fin n) (Fin n) ℂ)) i j‖ ^ 2) ≤
      (n : ℝ) * ((n : ℝ) - 1) * coherence Φ ^ 2 := by
  have hdiag (i : Fin n) : (Φᴴ * Φ - (1 : Matrix (Fin n) (Fin n) ℂ)) i i = 0 := by
    rw [Matrix.sub_apply, Framepot.conjTranspose_mul_diag, hunit i,
      RCLike.ofReal_one, Matrix.one_apply_eq, sub_self]
  have hrow (i : Fin n) :
      (∑ j, ‖(Φᴴ * Φ - (1 : Matrix (Fin n) (Fin n) ℂ)) i j‖ ^ 2) ≤
        ((n : ℝ) - 1) * coherence Φ ^ 2 := by
    calc
      _ = ∑ j ∈ Finset.univ.erase i,
          ‖(Φᴴ * Φ - (1 : Matrix (Fin n) (Fin n) ℂ)) i j‖ ^ 2 := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
        simp only [hdiag, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
      _ ≤ ∑ _j ∈ Finset.univ.erase i, coherence Φ ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
        rw [Matrix.sub_apply, Matrix.one_apply_ne hij, sub_zero]
        exact pow_le_pow_left₀ (norm_nonneg _)
          (RIPOneTwo.gram_norm_le_coherence Φ i j hij) 2
      _ = ((n : ℝ) - 1) * coherence Φ ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul,
          Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
          Fintype.card_fin, Nat.cast_sub hn, Nat.cast_one]
  calc
    _ ≤ ∑ _i : Fin n, ((n : ℝ) - 1) * coherence Φ ^ 2 :=
      Finset.sum_le_sum fun i _ => hrow i
    _ = (n : ℝ) * ((n : ℝ) - 1) * coherence Φ ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

end ExplicitRIP.Welch
