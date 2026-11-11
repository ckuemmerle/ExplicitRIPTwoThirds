/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Frozen.Defs.RIPConstant
public import ExplicitRIP.Frozen.Defs.UnsignedRIPConstant
public import ExplicitRIP.Frozen.Defs.DRNorm
public import ExplicitRIP.Analysis.Gershgorin.HermitianBound
public import ExplicitRIP.Analysis.UnsignedHybrid.Gram

/-!
# Real and complex matrix norm bridges

Entrywise domination, scalar extension, and the absolute Gram comparison transfer real matrix
estimates to the complex operator and discrete Rayleigh norms.

Source: [KM, Section 2.3 and proof of Theorem 1, (16)].
-/

public section

open scoped Matrix Matrix.Norms.L2Operator

namespace ExplicitRIP.Quant

variable {q : Type*} [Fintype q]

/-- The maximal absolute column sum is unchanged by real scalar extension. -/
theorem oneToOneNorm_map_ofReal (M : Matrix q q ℝ) :
    oneToOneNorm (M.map Complex.ofReal) = oneToOneNorm M := by
  simp only [oneToOneNorm, Matrix.map_apply, Complex.norm_real]

/-- Real symmetric matrices satisfy the maximal absolute column sum bound. -/
theorem opNorm_le_oneToOneNorm_of_isSymm [DecidableEq q] (M : Matrix q q ℝ) (hM : M.IsSymm) :
    opNorm M ≤ oneToOneNorm M := by
  have hH : (M.map Complex.ofReal).IsHermitian := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply, Complex.star_def,
      Complex.conj_ofReal]
    exact congrArg Complex.ofReal (hM.apply i j)
  exact (UnsignedHybrid.opNorm_real_le_opNorm_complex M).trans
    ((Gersh.opNorm_le_oneToOneNorm_of_isHermitian hH).trans_eq
      (oneToOneNorm_map_ofReal M))

/-- Triangle inequality for the Euclidean operator norm. -/
theorem opNorm_add_smul_le [DecidableEq q] (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (A B : Matrix q q ℝ) :
    opNorm (a • A + b • B) ≤ a * opNorm A + b * opNorm B := by
  change ‖a • A + b • B‖ ≤ a * ‖A‖ + b * ‖B‖
  simpa only [norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb] using
    norm_add_le (a • A) (b • B)

end ExplicitRIP.Quant
