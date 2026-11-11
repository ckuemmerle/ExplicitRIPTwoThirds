/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.HybridSplit.Basic
public import ExplicitRIP.Frozen.Defs.DRNorm
public import ExplicitRIP.Frozen.Defs.OneToOneNorm

/-!
# Entrywise domination and changes of scalar field

These bridges compare Euclidean matrix norms with entrywise moduli and complex scalar extension,
including empty index types.

Source: [KM, Section 2.3].
-/

public section

open scoped Matrix

namespace ExplicitRIP.UnsignedHybrid

/-- A nonnegative real majorant controls the Euclidean norm over either scalar field. -/
theorem opNorm_le_opNorm_of_norm_le {𝕜 𝕜' : Type*} [RCLike 𝕜] [RCLike 𝕜']
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : Matrix ι ι 𝕜) (P : Matrix ι ι ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hNP : ∀ i j, ‖N i j‖ ≤ P i j) :
    opNorm N ≤ opNorm (P.map fun r => (r : 𝕜')) := by
  let T := Matrix.toEuclideanCLM (n := ι) (𝕜 := 𝕜) N
  let U := Matrix.toEuclideanCLM (n := ι) (𝕜 := 𝕜') (P.map fun r => (r : 𝕜'))
  change ‖T‖ ≤ ‖U‖
  refine T.opNorm_le_bound (norm_nonneg _) fun x => ?_
  let y : EuclideanSpace 𝕜' ι := WithLp.toLp 2 (fun j => ((‖x.ofLp j‖ : ℝ) : 𝕜'))
  have hy : ‖y‖ = ‖x‖ := by
    simp only [EuclideanSpace.norm_eq, y, RCLike.norm_ofReal, abs_norm]
  have hout (i : ι) :
      ‖((P.map fun r => (r : 𝕜')) *ᵥ y.ofLp) i‖ = ∑ j, P i j * ‖x.ofLp j‖ := by
    change ‖∑ j, (P i j : 𝕜') * ((‖x.ofLp j‖ : ℝ) : 𝕜')‖ = _
    simp only [← RCLike.ofReal_mul, ← RCLike.ofReal_sum, RCLike.norm_ofReal]
    exact abs_of_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (hP i j) (norm_nonneg _))
  have hcoord (i : ι) : ‖(N *ᵥ x.ofLp) i‖ ≤
      ‖((P.map fun r => (r : 𝕜')) *ᵥ y.ofLp) i‖ := by
    rw [hout]
    calc
      ‖(N *ᵥ x.ofLp) i‖ ≤ ∑ j, ‖N i j * x.ofLp j‖ := norm_sum_le _ _
      _ = ∑ j, ‖N i j‖ * ‖x.ofLp j‖ := by simp only [norm_mul]
      _ ≤ ∑ j, P i j * ‖x.ofLp j‖ := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_right (hNP i j) (norm_nonneg _)
  calc
    ‖T x‖ ≤ ‖U y‖ := by
      rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
      apply Real.sqrt_le_sqrt
      apply Finset.sum_le_sum
      intro i _
      change ‖(N *ᵥ x.ofLp) i‖ ^ 2 ≤ ‖((P.map fun r => (r : 𝕜')) *ᵥ y.ofLp) i‖ ^ 2
      exact pow_le_pow_left₀ (norm_nonneg _) (hcoord i) 2
    _ ≤ ‖U‖ * ‖y‖ := U.le_opNorm y
    _ = ‖U‖ * ‖x‖ := by rw [hy]

/-- Entrywise modulus can only increase the Euclidean operator norm. -/
theorem opNorm_le_opNorm_map_norm {𝕜 : Type*} [RCLike 𝕜]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (N : Matrix ι ι 𝕜) :
    opNorm N ≤ opNorm (N.map fun z => ‖z‖) := by
  have h := opNorm_le_opNorm_of_norm_le (𝕜' := ℝ) N (N.map fun z => ‖z‖)
    (fun i j => show 0 ≤ ‖N i j‖ from norm_nonneg _) (fun _ _ => le_rfl)
  simpa only [RCLike.ofReal_real_eq_id, Matrix.map_id] using h

/-- Real scalar extension does not decrease the Euclidean operator norm. -/
theorem opNorm_real_le_opNorm_complex {q : Type*} [Fintype q] [DecidableEq q] (M : Matrix q q ℝ) :
    opNorm M ≤ opNorm (M.map Complex.ofReal) := by
  let T := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := q) M
  let U := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := q) (M.map Complex.ofReal)
  change ‖T‖ ≤ ‖U‖
  refine T.opNorm_le_bound (norm_nonneg _) fun x => ?_
  let y : EuclideanSpace ℂ q := WithLp.toLp 2 (fun i => (x.ofLp i : ℂ))
  have hy : ‖y‖ = ‖x‖ := by
    simp only [y, EuclideanSpace.norm_eq, Complex.norm_real]
  have hrow (i : q) : ((M *ᵥ x.ofLp) i : ℂ) =
      ((M.map Complex.ofReal) *ᵥ y.ofLp) i := by
    simp only [Matrix.mulVec, dotProduct, Complex.ofReal_sum, Complex.ofReal_mul,
      Matrix.map_apply, y]
  have heq : ‖T x‖ = ‖U y‖ := by
    simp only [EuclideanSpace.norm_eq]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    change ‖(M *ᵥ x.ofLp) i‖ ^ 2 =
      ‖((M.map Complex.ofReal) *ᵥ y.ofLp) i‖ ^ 2
    rw [← hrow, Complex.norm_real]
  rw [heq]
  simpa only [hy] using U.le_opNorm y

/-- The discrete Rayleigh norm is unchanged by complex scalar extension. -/
theorem drNorm_map_ofReal {ι : Type*} [Fintype ι] (P : Matrix ι ι ℝ) :
    drNorm (P.map Complex.ofReal) = drNorm P := by
  unfold drNorm
  congr 1
  funext IJ
  simp only [Matrix.map_apply, ← Complex.ofReal_sum, Complex.norm_real]

/-- The column-sum norm of a complexified modulus matrix is the original column-sum norm. -/
theorem oneToOneNorm_map_norm_ofReal {𝕜 : Type*} [RCLike 𝕜]
    {ι : Type*} [Fintype ι] (N : Matrix ι ι 𝕜) :
    oneToOneNorm ((N.map fun z => ‖z‖).map Complex.ofReal) = oneToOneNorm N := by
  unfold oneToOneNorm
  congr 1
  funext j
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.map_apply, Complex.norm_real, norm_norm]

/-- A real symmetric matrix becomes Hermitian after complex scalar extension. -/
theorem isHermitian_map_ofReal_of_symm {ι : Type*} (P : Matrix ι ι ℝ)
    (hP : ∀ i j, P i j = P j i) : (P.map Complex.ofReal).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply, Complex.star_def,
    Complex.conj_ofReal, hP j i]

end ExplicitRIP.UnsignedHybrid
