/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.UnsignedHybrid.NormComparison
public import ExplicitRIP.Analysis.FlatRIP.Basic
public import ExplicitRIP.Frozen.Defs.RIPConstant
public import ExplicitRIP.Frozen.Defs.UnsignedRIPConstant

/-!
# Principal Gram errors and unsigned domination

The finite-maxima definitions identify principal Gram errors and show that entrywise moduli
dominate signed restricted isometry.

Source: [KM, Section 2.3].
-/

public section

open scoped Matrix

namespace ExplicitRIP.UnsignedHybrid

/-- Taking a principal submatrix commutes with forming the Gram error. -/
theorem principal_gram_error_eq {𝕜 : Type*} [RCLike 𝕜]
    {m n : Type*} [Fintype m] [DecidableEq n]
    (Φ : Matrix m n 𝕜) (S : Finset n) :
    (Φ.submatrix id (Subtype.val : S → n))ᴴ *
        Φ.submatrix id (Subtype.val : S → n) - 1 =
      (Φᴴ * Φ - 1).submatrix (Subtype.val : S → n) (Subtype.val : S → n) := by
  classical
  ext i j
  simp only [Matrix.sub_apply, Matrix.submatrix_apply, Flat.principal_gram_entry]
  exact congrArg (fun N : Matrix S S 𝕜 => (Φᴴ * Φ) i j - N i j)
    (Matrix.submatrix_one (Subtype.val : S → n) Subtype.val_injective).symm

/-- Every signed restricted Gram norm is bounded by the corresponding unsigned maximum. -/
theorem ripConstant_le_unsignedRIPConstant {𝕜 : Type*} [RCLike 𝕜]
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (Φ : Matrix m n 𝕜) (k : ℕ) : ripConstant Φ k ≤ unsignedRIPConstant Φ k := by
  classical
  unfold ripConstant unsignedRIPConstant
  refine ciSup_mono (Finite.bddAbove_range _) fun S => ?_
  rw [principal_gram_error_eq, Matrix.submatrix_map]
  exact opNorm_le_opNorm_map_norm _

/-- Opposite entries of a Gram error have the same modulus. -/
theorem norm_gram_error_symm {𝕜 : Type*} [RCLike 𝕜]
    {m n : Type*} [Fintype m] [DecidableEq n]
    (Φ : Matrix m n 𝕜) (i j : n) :
    ‖(Φᴴ * Φ - (1 : Matrix n n 𝕜)) i j‖ = ‖(Φᴴ * Φ - (1 : Matrix n n 𝕜)) j i‖ := by
  have hH := (Matrix.isHermitian_conjTranspose_mul_self Φ).sub Matrix.isHermitian_one
  rw [← hH.apply i j, norm_star]

end ExplicitRIP.UnsignedHybrid
