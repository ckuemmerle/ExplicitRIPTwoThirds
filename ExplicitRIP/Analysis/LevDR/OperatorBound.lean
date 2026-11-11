/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.LevDR.ComplexRectangle
public import ExplicitRIP.Analysis.LevDR.RectangleBound
public import ExplicitRIP.Frozen.Defs.OpNorm

/-!
# From discrete rectangle estimates to the Euclidean operator norm

Finite Abel summation and the complex coordinate decomposition prove the logarithmic discrete
Rayleigh comparison.

Source: [KM, Section 2.1, (5)].
-/

public section

open scoped BigOperators Matrix

namespace ExplicitRIP.Lev

theorem one_add_log_nat_nonneg (n : ℕ) : 0 ≤ 1 + Real.log (n : ℝ) := by
  by_cases hn : n = 0
  · simp only [hn, Nat.cast_zero, Real.log_zero, add_zero, zero_le_one]
  · exact add_nonneg zero_le_one
      (Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn))

theorem bilinear_sum_le_dr_norm {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℂ) (a b : ι → ℂ) :
    ‖∑ i, ∑ j, a i * b j * M i j‖ ≤
      16 * ExplicitRIP.drNorm M * (1 + Real.log (Fintype.card ι : ℝ)) *
        Real.sqrt (∑ i, Complex.normSq (a i)) *
        Real.sqrt (∑ j, Complex.normSq (b j)) := by
  classical
  have h := complex_weighted_rectangle_log M (ExplicitRIP.drNorm M)
    (dr_norm_nonneg M) Finset.univ Finset.univ
    (fun u _ v _ => rectangle_sum_le_dr_norm M u v) a b
  simp only [Finset.card_univ] at h
  calc
    _ ≤ 16 * ExplicitRIP.drNorm M * Real.sqrt (1 + Real.log (Fintype.card ι : ℝ)) *
        Real.sqrt (1 + Real.log (Fintype.card ι : ℝ)) *
        Real.sqrt (∑ i, Complex.normSq (a i)) *
        Real.sqrt (∑ j, Complex.normSq (b j)) := h
    _ = _ := by
      rw [mul_assoc (16 * ExplicitRIP.drNorm M),
        Real.mul_self_sqrt (one_add_log_nat_nonneg (Fintype.card ι))]

theorem sqrt_sum_norm_sq {ι : Type*} [Fintype ι] (x : EuclideanSpace ℂ ι) :
    Real.sqrt (∑ i, Complex.normSq (x.ofLp i)) = ‖x‖ := by
  simp only [Complex.normSq_eq_norm_sq, EuclideanSpace.norm_eq]

theorem inner_matrix_eq_bilinear {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (x y : EuclideanSpace ℂ ι) :
    inner ℂ y (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M x) =
      ∑ i, ∑ j, star (y.ofLp i) * x.ofLp j * M i j := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanCLM]
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem inner_matrix_le_dr_norm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (x y : EuclideanSpace ℂ ι) :
    ‖inner ℂ y (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M x)‖ ≤
      (16 * ExplicitRIP.drNorm M * (1 + Real.log (Fintype.card ι : ℝ))) * ‖x‖ * ‖y‖ := by
  rw [inner_matrix_eq_bilinear]
  have h := bilinear_sum_le_dr_norm M (fun i => star (y.ofLp i)) x.ofLp
  simpa only [Complex.star_def, Complex.normSq_conj, sqrt_sum_norm_sq,
    mul_right_comm _ ‖y‖ ‖x‖] using h

theorem op_norm_le_dr_norm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) :
    ExplicitRIP.opNorm M ≤
      16 * ExplicitRIP.drNorm M * (1 + Real.log (Fintype.card ι : ℝ)) := by
  let T : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
    Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M
  have hC : 0 ≤ 16 * ExplicitRIP.drNorm M * (1 + Real.log (Fintype.card ι : ℝ)) :=
    mul_nonneg (mul_nonneg (by norm_num) (dr_norm_nonneg M))
      (one_add_log_nat_nonneg (Fintype.card ι))
  change ‖T‖ ≤ _
  apply T.opNorm_le_bound hC
  intro x
  by_cases hx : ‖T x‖ = 0
  · rw [hx]
    exact mul_nonneg hC (norm_nonneg _)
  · have hxpos : 0 < ‖T x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
    have h := inner_matrix_le_dr_norm M x (T x)
    change ‖inner ℂ (T x) (T x)‖ ≤ _ at h
    rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
      abs_of_nonneg (norm_nonneg _)] at h
    rw [pow_two] at h
    exact (mul_le_mul_iff_left₀ hxpos).mp h

end ExplicitRIP.Lev
