/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Frozen.Defs.OpNorm

/-!
# The spectral-norm comparison of [KM, Section 2.3]

Source: [KM, Section 2.3, the opening spectral-norm comparison].

The coordinatewise triangle inequality compares the image of a vector with the image of its
coordinatewise modulus, including empty row and column types. This proves
`‖M‖_{2→2} ≤ ‖|M|‖_{2→2}` for every real or complex rectangular matrix.
-/

public section

open scoped Matrix

theorem ExplicitRIP.Provider.opNorm_le_opNorm_abs :
    ∀ {𝕜 : Type} [RCLike 𝕜] {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
      (M : Matrix m n 𝕜),
      ExplicitRIP.opNorm M ≤ ExplicitRIP.opNorm (M.map fun z => ‖z‖) := by
  intro 𝕜 _ m n _ _ _ M
  let A := M.map fun z => ‖z‖
  let T := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)
  let U := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)
  change ‖T‖ ≤ ‖U‖
  refine T.opNorm_le_bound (norm_nonneg _) fun x => ?_
  let y : EuclideanSpace ℝ n := WithLp.toLp 2 (fun j => ‖x.ofLp j‖)
  have hy : ‖y‖ = ‖x‖ := by
    simp only [y, EuclideanSpace.norm_eq, Real.norm_of_nonneg, norm_nonneg]
  have hrow (i : m) : ‖(M *ᵥ x.ofLp) i‖ ≤ (A *ᵥ y.ofLp) i := by
    simpa only [Matrix.mulVec, dotProduct, A, Matrix.map_apply, y,
      WithLp.ofLp_toLp, norm_mul] using
      (norm_sum_le (s := Finset.univ) (f := fun j => M i j * x.ofLp j))
  have hpos (i : m) : 0 ≤ (A *ᵥ y.ofLp) i := (norm_nonneg _).trans (hrow i)
  have hnorm : ‖T x‖ ≤ ‖U y‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro i _
    change ‖(M *ᵥ x.ofLp) i‖ ^ 2 ≤ ‖(A *ᵥ y.ofLp) i‖ ^ 2
    rw [Real.norm_of_nonneg (hpos i)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hrow i) 2
  exact hnorm.trans (by simpa only [hy] using U.le_opNorm y)
