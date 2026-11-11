/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Order.Chebyshev

/-!
# Finite-sum frame-potential identities

The squared entry norms are related to traces without a choice of matrix norm.
-/

public section

open scoped BigOperators Matrix ComplexConjugate

namespace ExplicitRIP.Framepot

variable {𝕜 I J : Type*} [RCLike 𝕜]

/-- The entrywise squared norm sum is the real trace of the row Gram matrix. -/
theorem sum_norm_sq_eq_re_trace_mul_conjTranspose [Fintype I] [Fintype J]
    (A : Matrix I J 𝕜) :
    (∑ i, ∑ j, ‖A i j‖ ^ 2) = RCLike.re (Matrix.trace (A * Aᴴ)) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    map_sum, RCLike.star_def, RCLike.mul_conj, ← RCLike.ofReal_pow, RCLike.ofReal_re]

/-- For a Hermitian matrix the same sum is the real trace of its square. -/
theorem sum_norm_sq_eq_re_trace_sq [Fintype I] (A : Matrix I I 𝕜) (hA : A.IsHermitian) :
    (∑ i, ∑ j, ‖A i j‖ ^ 2) = RCLike.re (Matrix.trace (A * A)) := by
  simpa only [hA.eq] using sum_norm_sq_eq_re_trace_mul_conjTranspose A

/-- A row-Gram diagonal entry is the real sum of squared row-entry norms. -/
theorem mul_conjTranspose_diag [Fintype J] (A : Matrix I J 𝕜) (i : I) :
    (A * Aᴴ) i i = ((∑ j, ‖A i j‖ ^ 2 : ℝ) : 𝕜) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def,
    RCLike.mul_conj, ← RCLike.ofReal_pow, RCLike.ofReal_sum]

/-- A column-Gram diagonal entry is the real sum of squared column-entry norms. -/
theorem conjTranspose_mul_diag [Fintype I] (A : Matrix I J 𝕜) (j : J) :
    (Aᴴ * A) j j = ((∑ i, ‖A i j‖ ^ 2 : ℝ) : 𝕜) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def,
    RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_sum]

/-- Row and column Gram matrices have equal frame potentials. -/
theorem frame_potential_transpose [Fintype I] [Fintype J] (A : Matrix I J 𝕜) :
    (∑ j, ∑ k, ‖(Aᴴ * A) j k‖ ^ 2) = ∑ i, ∑ k, ‖(A * Aᴴ) i k‖ ^ 2 := by
  rw [sum_norm_sq_eq_re_trace_sq _ (Matrix.isHermitian_conjTranspose_mul_self A),
    sum_norm_sq_eq_re_trace_sq _ (Matrix.isHermitian_mul_conjTranspose_self A)]
  congr 1
  calc
    Matrix.trace ((Aᴴ * A) * (Aᴴ * A)) =
        Matrix.trace (Aᴴ * (A * Aᴴ * A)) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((A * Aᴴ * A) * Aᴴ) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((A * Aᴴ) * (A * Aᴴ)) := by
      simp only [Matrix.mul_assoc]

/-- Removing a unit diagonal removes exactly one squared norm per index. -/
theorem sum_norm_sq_sub_one_add_card [Fintype I] [DecidableEq I] (A : Matrix I I 𝕜)
    (hdiag : ∀ i, A i i = 1) :
    (∑ i, ∑ j, ‖(A - 1) i j‖ ^ 2) + Fintype.card I = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  have hentry (i j : I) :
      ‖(A - 1) i j‖ ^ 2 + (if i = j then (1 : ℝ) else 0) = ‖A i j‖ ^ 2 := by
    by_cases hij : i = j
    · subst j
      simp only [Matrix.sub_apply, Matrix.one_apply_eq, hdiag, sub_self, norm_zero,
        zero_pow (by decide : 2 ≠ 0), ite_true, zero_add, norm_one, one_pow]
    · simp only [Matrix.sub_apply, Matrix.one_apply_ne hij, sub_zero, ite_eq_right hij, add_zero]
  calc
    (∑ i, ∑ j, ‖(A - 1) i j‖ ^ 2) + Fintype.card I =
        ∑ i, ∑ j, (‖(A - 1) i j‖ ^ 2 + if i = j then (1 : ℝ) else 0) := by
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ,
        ite_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    _ = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by simp only [hentry]

/-- Finite-sum Cauchy–Schwarz gives the unit-column frame-potential lower bound.

The row-diagonal argument works over `RCLike` scalars and allows zero dimensions.
-/
theorem unit_frame_potential_lower (m n : ℕ) (A : Matrix (Fin m) (Fin n) 𝕜)
    (hunit : ∀ j, ∑ i, ‖A i j‖ ^ 2 = 1) :
    (n : ℝ) ^ 2 ≤ (m : ℝ) * ∑ j, ∑ k, ‖(Aᴴ * A) j k‖ ^ 2 := by
  have hmass : (∑ i, ∑ j, ‖A i j‖ ^ 2) = (n : ℝ) := by
    rw [Finset.sum_comm]
    simp only [hunit, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  have hdiag (i : Fin m) : ‖(A * Aᴴ) i i‖ ^ 2 = (∑ j, ‖A i j‖ ^ 2) ^ 2 := by
    rw [mul_conjTranspose_diag, RCLike.norm_ofReal, sq_abs]
  have hrow (i : Fin m) :
      (∑ j, ‖A i j‖ ^ 2) ^ 2 ≤ ∑ k, ‖(A * Aᴴ) i k‖ ^ 2 := by
    rw [← hdiag]
    exact Finset.single_le_sum (fun k _ => sq_nonneg ‖(A * Aᴴ) i k‖) (Finset.mem_univ i)
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := Finset.univ) (f := fun i : Fin m => ∑ j, ‖A i j‖ ^ 2)
  rw [hmass] at hcs
  simp only [Finset.card_univ, Fintype.card_fin] at hcs
  calc
    (n : ℝ) ^ 2 ≤ (m : ℝ) * ∑ i, (∑ j, ‖A i j‖ ^ 2) ^ 2 := hcs
    _ ≤ (m : ℝ) * ∑ i, ∑ k, ‖(A * Aᴴ) i k‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hrow i))
        (Nat.cast_nonneg m)
    _ = (m : ℝ) * ∑ j, ∑ k, ‖(Aᴴ * A) j k‖ ^ 2 := by
      rw [frame_potential_transpose A]

end ExplicitRIP.Framepot
