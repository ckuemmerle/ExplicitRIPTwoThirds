/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Frozen.Defs.OpNorm

/-!
# Quadratic forms and Euclidean operator norms

The Rayleigh-quotient bridge identifies the sparse-vector distortion with the principal-Gram
norm formula. All matrix norms use the Euclidean operator norm.

Source: [KM, Section 1].
-/

public section

namespace ExplicitRIP.Ripc

open Matrix
open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]

theorem opNorm_eq_norm_toEuclideanCLM {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n 𝕜) : ExplicitRIP.opNorm A = ‖Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := n) A‖ := rfl

theorem abs_re_inner_le_norm_mul_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (T : E →L[𝕜] E) (x : E) :
    |RCLike.re (inner 𝕜 (T x) x)| ≤ ‖T‖ * ‖x‖ ^ 2 := by
  calc
    |RCLike.re (inner 𝕜 (T x) x)| ≤ ‖inner 𝕜 (T x) x‖ := RCLike.abs_re_le_norm _
    _ ≤ ‖T x‖ * ‖x‖ := norm_inner_le_norm _ _
    _ ≤ (‖T‖ * ‖x‖) * ‖x‖ := mul_le_mul_of_nonneg_right (T.le_opNorm x) (norm_nonneg x)
    _ = ‖T‖ * ‖x‖ ^ 2 := by ring

theorem norm_le_of_abs_re_inner_le_mul_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (T : E →L[𝕜] E) (hT : T.IsSymmetric)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ x, |RCLike.re (inner 𝕜 (T x) x)| ≤ δ * ‖x‖ ^ 2) : ‖T‖ ≤ δ := by
  rw [T.norm_eq_iSup_rayleighQuotient hT]
  refine ciSup_le fun x ↦ ?_
  by_cases hx : x = 0
  · simpa only [hx, ContinuousLinearMap.rayleighQuotient_apply_zero, abs_zero] using hδ
  · have hx' : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx) 2
    simpa only [ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply, abs_div, abs_sq, div_le_iff₀ hx'] using h x

theorem gram_error_re_inner {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (B : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n) :
    RCLike.re (inner 𝕜 (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := n) (Bᴴ * B - 1) x) x) =
      ‖(WithLp.toLp 2 (B *ᵥ x.ofLp) : EuclideanSpace 𝕜 m)‖ ^ 2 - ‖x‖ ^ 2 := by
  rw [inner_re_symm, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.ofLp_toEuclideanCLM, dotProduct_comm, Matrix.sub_mulVec, Matrix.one_mulVec,
    dotProduct_sub, map_sub, ← Matrix.mulVec_mulVec, dotProduct_mulVec,
    Matrix.vecMul_conjTranspose, star_star]
  rw [dotProduct_comm (star (B *ᵥ x.ofLp)) (B *ᵥ x.ofLp),
    dotProduct_comm (star x.ofLp) x.ofLp,
    ← EuclideanSpace.inner_eq_star_dotProduct
    (WithLp.toLp 2 (B *ᵥ x.ofLp) : EuclideanSpace 𝕜 m)
    (WithLp.toLp 2 (B *ᵥ x.ofLp) : EuclideanSpace 𝕜 m),
    ← EuclideanSpace.inner_eq_star_dotProduct x x]
  simp only [← norm_sq_eq_re_inner]

theorem gram_error_opNorm_le_iff {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (B : Matrix m n 𝕜) {δ : ℝ} (hδ : 0 ≤ δ) :
    ExplicitRIP.opNorm (Bᴴ * B - 1) ≤ δ ↔
      ∀ x : n → 𝕜,
        |(∑ i, ‖(B *ᵥ x) i‖ ^ 2) - ∑ j, ‖x j‖ ^ 2| ≤ δ * ∑ j, ‖x j‖ ^ 2 := by
  rw [opNorm_eq_norm_toEuclideanCLM]
  constructor
  · intro h x
    have hx := (abs_re_inner_le_norm_mul_sq (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := n) (Bᴴ * B - 1))
      (WithLp.toLp 2 x)).trans (mul_le_mul_of_nonneg_right h (sq_nonneg _))
    simpa only [gram_error_re_inner, EuclideanSpace.norm_sq_eq, WithLp.ofLp_toLp] using hx
  · intro h
    refine norm_le_of_abs_re_inner_le_mul_sq
      (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := n) (Bᴴ * B - 1)) ?_ hδ ?_
    · change (Matrix.toEuclideanLin (𝕜 := 𝕜) (m := n) (n := n) (Bᴴ * B - 1)).IsSymmetric
      exact Matrix.isSymmetric_toEuclideanLin_iff.mpr
        ((Matrix.isHermitian_conjTranspose_mul_self B).sub Matrix.isHermitian_one)
    · intro x
      simpa only [gram_error_re_inner, EuclideanSpace.norm_sq_eq] using h x.ofLp

end ExplicitRIP.Ripc
