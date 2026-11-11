/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.LinearAlgebra.LDL.Factor

/-!
# The pivot count equals the rational rank

Restricting the rational pivot rows to their pivot columns gives an upper triangular nonsingular
matrix. The weighted rational factorization then has the same rank as the pivot-row matrix.
-/

public section

namespace ExplicitRIP.LDL

open Matrix

variable {v : ℕ} (G : Matrix (Fin v) (Fin v) ℚ)

/-- The submatrix of pivot rows on pivot columns is upper triangular. -/
theorem rationalRows_pivot_columns_isUpperTriangular (hG : G.PosSemidef) :
    ((rationalRows G).submatrix id (ldlPivots G).get).IsUpperTriangular := by
  intro i j hij
  exact residual_column_eq_zero G hG ((ldlPivots G).get i)
    (Nat.le_of_lt ((ldlPivots G).get i).isLt) _ _
    (pivots_get_strictMono G hij)

/-- The rational pivot rows have full row rank. -/
theorem rationalRows_rank (hG : G.PosSemidef) :
    (rationalRows G).rank = (ldlPivots G).length := by
  have hdet : ((rationalRows G).submatrix id (ldlPivots G).get).det ≠ 0 := by
    apply (rationalRows_pivot_columns_isUpperTriangular G hG).det_ne_zero_iff.mpr
    intro i
    exact (mem_pivots_iff G _).mp (List.get_mem _ _)
  apply le_antisymm (Matrix.rank_le_height _) ?_
  calc
    _ = ((rationalRows G).submatrix id (ldlPivots G).get).rank := by
      rw [Matrix.rank_of_det_ne_zero hdet, Fintype.card_fin]
    _ ≤ (rationalRows G).rank := Matrix.rank_submatrix_le _ _ _

/-- Every diagonal weight of a retained pivot is nonzero. -/
theorem pivotWeights_det_ne_zero : (pivotWeights G).det ≠ 0 := by
  rw [pivotWeights, Matrix.det_diagonal]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact inv_ne_zero ((mem_pivots_iff G _).mp (List.get_mem _ _))

/-- The number of retained pivots is the rank over the original rational field. -/
theorem pivots_length_eq_rank (hG : G.PosSemidef) : (ldlPivots G).length = G.rank := by
  have hC := rationalRows_rank G hG
  have hleft : ((rationalRows G)ᵀ * pivotWeights G).rank = (ldlPivots G).length := by
    rw [Matrix.rank_mul_eq_left_of_det_ne_zero (pivotWeights G) _
      (pivotWeights_det_ne_zero G), Matrix.rank_transpose, hC]
  apply le_antisymm
  · have hlo := Matrix.rank_mul_ge ((rationalRows G)ᵀ * pivotWeights G) (rationalRows G)
    rw [rational_factorization G hG, hleft, hC, Fintype.card_fin] at hlo
    omega
  · calc
      G.rank = ((rationalRows G)ᵀ * pivotWeights G * rationalRows G).rank :=
        congrArg Matrix.rank (rational_factorization G hG).symm
      _ ≤ (rationalRows G).rank := Matrix.rank_mul_le_right _ _
      _ = (ldlPivots G).length := hC

end ExplicitRIP.LDL
