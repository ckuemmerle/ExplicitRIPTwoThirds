/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.LinearAlgebra.FramePotential.Basic

/-!
# Rank and energy of a shifted Gram matrix

Cauchy–Schwarz on the nonzero eigenvalues bounds the squared trace by the rank
times the squared Frobenius norm. A constant shift of a Gram matrix has rank
at most one more than the number of rows of the frame.

Source: [KM, proof of Proposition 10].
-/

public section

open scoped Matrix BigOperators

namespace ExplicitRIP.TwoDistanceBarrier

variable {J : Type*} [Fintype J]

/-- Cauchy–Schwarz restricted to the nonzero eigenvalues of a real symmetric matrix. -/
theorem trace_sq_le_rank_mul_energy (A : Matrix J J ℝ) (hA : A.IsHermitian) :
    A.trace ^ 2 ≤ (A.rank : ℝ) * ∑ i, ∑ j, A i j ^ 2 := by
  classical
  let s := Finset.univ.filter fun i => hA.eigenvalues i ≠ 0
  have hsum : ∑ i ∈ s, hA.eigenvalues i = ∑ i, hA.eigenvalues i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hi
  have hcard : s.card = A.rank := by
    rw [hA.rank_eq_card_non_zero_eigs]
    simp only [s, Fintype.card_subtype]
  have henergy : ∑ i, ∑ j, A i j ^ 2 = ∑ i, hA.eigenvalues i ^ 2 := by
    have h := Framepot.sum_norm_sq_eq_re_trace_sq A hA
    simp only [Real.norm_eq_abs, sq_abs, RCLike.re_to_real] at h
    rw [h]
    let D : Matrix J J ℝ := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)
    have he : A * A = Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary (D * D) := by
      rw [map_mul]
      exact congrArg₂ (· * ·) hA.spectral_theorem hA.spectral_theorem
    rw [he, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
      Unitary.coe_star_mul_self, one_mul]
    dsimp only [D]
    rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    simp only [Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq, pow_two]
  have htr : A.trace = ∑ i, hA.eigenvalues i := by
    simpa only [RCLike.ofReal_real_eq_id, id_eq] using hA.trace_eq_sum_eigenvalues
  rw [htr, ← hsum, ← hcard, henergy]
  exact (sq_sum_le_card_mul_sum_sq (s := s) (f := hA.eigenvalues)).trans
    (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => sq_nonneg _)) (Nat.cast_nonneg _))

/-- Subtracting a constant matrix increases the Gram rank by at most one. -/
theorem shifted_gram_rank_le (m : ℕ) (Φ : Matrix (Fin m) J ℝ) (η : ℝ) :
    (Φᵀ * Φ - Matrix.of (fun _ _ => η)).rank ≤ m + 1 := by
  let A : Matrix J (Fin m ⊕ Unit) ℝ :=
    Matrix.fromCols Φᵀ (Matrix.of fun _ _ => (1 : ℝ))
  let B : Matrix (Fin m ⊕ Unit) J ℝ :=
    Matrix.fromRows Φ (Matrix.of fun _ _ => -η)
  have he : Φᵀ * Φ - Matrix.of (fun _ _ => η) = A * B := by
    rw [Matrix.fromCols_mul_fromRows]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, Matrix.of_apply,
      Fintype.sum_unique, one_mul, sub_eq_add_neg]
  rw [he]
  exact (Matrix.rank_mul_le_left A B).trans (by
    simpa only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unique] using
      Matrix.rank_le_card_width A)

end ExplicitRIP.TwoDistanceBarrier
