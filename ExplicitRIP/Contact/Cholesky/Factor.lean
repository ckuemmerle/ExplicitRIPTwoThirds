/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Contact.Cholesky.HostInput
public import ExplicitRIP.Frozen.Defs.CholeskyMatrix
import ExplicitRIP.Frozen.LDLFactorization
import ExplicitRIP.LinearAlgebra.LDL.Rank

/-!
# Dimensions and Gram identity of the selected Cholesky matrix

This proves the row count, unit column norms, and Gram identity for the construction in
[KM, proof of Theorem 1 and footnote 4], with the host dimension given in [KM, (13)].
-/

public section

open scoped Matrix

namespace ExplicitRIP.Contact.Cholesky

/-- The real factor has one independent row for each retained pivot. -/
theorem ldlFactor_rank {v : ℕ} (G : Matrix (Fin v) (Fin v) ℚ) (hG : G.PosSemidef) :
    (ldlFactor G).rank = (ldlPivots G).length := by
  have htri : ((ldlFactor G).submatrix id (ldlPivots G).get).IsUpperTriangular := by
    intro i j hij
    have hz := LDL.rationalRows_pivot_columns_isUpperTriangular G hG (i := i) (j := j) hij
    change LDL.rationalRows G i ((ldlPivots G).get j) = 0 at hz
    change ((LDL.rationalRows G i ((ldlPivots G).get j) : ℚ) : ℝ) / _ = 0
    rw [hz, Rat.cast_zero, zero_div]
  have hdet : ((ldlFactor G).submatrix id (ldlPivots G).get).det ≠ 0 := by
    apply htri.det_ne_zero_iff.mpr
    intro i
    have hd : (0 : ℝ) < (ldlResidual G ((ldlPivots G).get i)
        ((ldlPivots G).get i) ((ldlPivots G).get i) : ℚ) := by
      exact_mod_cast LDL.pivot_pos G hG _ (List.get_mem _ _)
    exact div_ne_zero hd.ne' (Real.sqrt_pos.mpr hd).ne'
  apply le_antisymm (Matrix.rank_le_height _) ?_
  calc
    _ = ((ldlFactor G).submatrix id (ldlPivots G).get).rank := by
      rw [Matrix.rank_of_det_ne_zero hdet, Fintype.card_fin]
    _ ≤ (ldlFactor G).rank := Matrix.rank_submatrix_le _ _ _

variable (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]

/-- The actual number of retained lexicographic pivots is the host dimension. -/
theorem ldlPivots_lexGram_length :
    (ldlPivots (lexGram p)).length = (p - 1) * (p ^ 2 + 1) := by
  have hG := lexGram_posSemidef p
  calc
    (ldlPivots (lexGram p)).length = (ldlFactor (lexGram p)).rank :=
      (ldlFactor_rank (lexGram p) hG).symm
    _ = ((ldlFactor (lexGram p))ᵀ * ldlFactor (lexGram p)).rank :=
      (Matrix.rank_transpose_mul_self _).symm
    _ = ((lexGram p).map (fun q : ℚ => (q : ℝ))).rank :=
      congrArg Matrix.rank (ldl_factorization _ _ hG).2.2
    _ = ((hostGram ℝ p).submatrix (lexEquiv p).symm (lexEquiv p).symm).rank := by
      rw [lexGram_map_ratCast]
    _ = (hostGram ℝ p).rank := Matrix.rank_submatrix _ _ _
    _ = (p - 1) * (p ^ 2 + 1) := HostFrame.hostGram_rank p

/-- Selecting columns of the ordered factor selects exactly the corresponding Gram entries. -/
theorem choleskyMatrix_gram (T : Finset (ZMod p)) :
    (choleskyMatrix p T)ᵀ * choleskyMatrix p T =
      (hostGram ℝ p).submatrix Subtype.val Subtype.val := by
  ext x y
  have h := congrArg
    (fun M => M (lexEquiv p x.1) (lexEquiv p y.1))
    (ldl_factorization _ _ (lexGram_posSemidef p)).2.2
  rw [lexGram_map_ratCast p] at h
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
    choleskyMatrix, Equiv.symm_apply_apply] using h

/-- Every column of the selected Cholesky matrix has squared norm one. -/
theorem choleskyMatrix_column_norm_sq (T : Finset (ZMod p))
    (x : selectedVertices p T) : ∑ r, choleskyMatrix p T r x ^ 2 = 1 := by
  have h := congrArg (fun M => M x x) (choleskyMatrix_gram p T)
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, ← pow_two,
    Matrix.submatrix_apply, HostFrame.hostGram_apply_self] using h

end ExplicitRIP.Contact.Cholesky
