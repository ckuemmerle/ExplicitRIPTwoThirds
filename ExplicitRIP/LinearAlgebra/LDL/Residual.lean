/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Frozen.Defs.LDLResidual

/-!
# Invariants of exact semidefinite elimination

The residual stays positive semidefinite, and every processed row and column vanishes.
-/

public section

namespace ExplicitRIP.LDL

open Matrix

variable {n : Type*} [Finite n]

/-- A zero diagonal entry of a rational PSD matrix has a zero column. -/
theorem column_eq_zero_of_diag_eq_zero {R : Matrix n n ℚ} (hR : R.PosSemidef)
    (k : n) (hd : R k k = 0) : ∀ i, R i k = 0 := by
  classical
  let := Fintype.ofFinite n
  have hz : R *ᵥ Pi.single k 1 = 0 := hR.dotProduct_mulVec_zero_iff.mp (by
    simpa only [star_trivial, mulVec_single_one, single_one_dotProduct, col_apply] using hd)
  intro i
  simpa only [mulVec_single_one, col_apply, Pi.zero_apply] using congrFun hz i

/-- The rational Schur update at any nonzero diagonal entry preserves PSD. -/
theorem schur_posSemidef {R : Matrix n n ℚ} (hR : R.PosSemidef)
    (k : n) (hd : R k k ≠ 0) :
    (R - (R k k)⁻¹ • Matrix.of (fun i j => R i k * R k j)).PosSemidef := by
  classical
  let := Fintype.ofFinite n
  have hs (i j : n) : R i j = R j i := hR.isHermitian.isSymm.apply j i
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · rw [Matrix.isHermitian_iff_isSymm]
    ext i j
    simp only [transpose_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, of_apply]
    rw [hs j i, hs j k, hs k i]
    ring
  · intro x
    have hcross : x ⬝ᵥ R.col k = (R *ᵥ x) k := by
      simp only [dotProduct, col_apply, mulVec]
      apply Finset.sum_congr rfl
      intro i _
      rw [hs i k, mul_comm]
    have hopt := hR.dotProduct_mulVec_nonneg
      (x - ((R k k)⁻¹ * (R *ᵥ x) k) • Pi.single k 1)
    simp only [star_trivial, mulVec_sub, mulVec_smul, mulVec_single_one,
      sub_dotProduct, dotProduct_sub, dotProduct_smul, smul_dotProduct,
      single_one_dotProduct, smul_eq_mul, hcross, col_apply] at hopt
    have hquad : star x ⬝ᵥ
        (R - (R k k)⁻¹ • Matrix.of (fun i j => R i k * R k j)) *ᵥ x =
        x ⬝ᵥ R *ᵥ x - (R k k)⁻¹ * (R *ᵥ x) k * (R *ᵥ x) k := by
      change x ⬝ᵥ (R - (R k k)⁻¹ • Matrix.vecMulVec (R.col k) (R.row k)) *ᵥ x = _
      rw [sub_mulVec, smul_mulVec, vecMulVec_mulVec, dotProduct_sub,
        dotProduct_smul, dotProduct_smul, hcross]
      simp only [smul_eq_mul, op_smul_eq_mul]
      change x ⬝ᵥ R *ᵥ x - (R k k)⁻¹ * ((R *ᵥ x) k * (R *ᵥ x) k) = _
      ring
    rw [hquad]
    convert hopt using 1
    field_simp [hd]
    ring

variable {v : ℕ} (G : Matrix (Fin v) (Fin v) ℚ)

/-- The zero-pivot branch agrees with the same algebraic subtraction formula. -/
theorem residual_succ (k : ℕ) (hk : k < v) :
    ldlResidual G (k + 1) = ldlResidual G k -
      (ldlResidual G k ⟨k, hk⟩ ⟨k, hk⟩)⁻¹ •
        Matrix.of (fun i j => ldlResidual G k i ⟨k, hk⟩ *
          ldlResidual G k ⟨k, hk⟩ j) := by
  rw [ldlResidual, dite_eq_left hk]
  split_ifs with hd
  · simp only [hd, _root_.inv_zero, zero_smul, sub_zero]
  · rfl

/-- Every residual of a PSD matrix is PSD. -/
theorem residual_posSemidef (hG : G.PosSemidef) (k : ℕ) :
    (ldlResidual G k).PosSemidef := by
  induction k with
  | zero => exact hG
  | succ k ih =>
    by_cases hk : k < v
    · rw [residual_succ G k hk]
      by_cases hd : ldlResidual G k ⟨k, hk⟩ ⟨k, hk⟩ = 0
      · simpa only [hd, _root_.inv_zero, zero_smul, sub_zero] using ih
      · exact schur_posSemidef ih ⟨k, hk⟩ hd
    · simpa only [ldlResidual, dite_eq_right hk] using ih

/-- All previously processed rows of the residual vanish. -/
theorem residual_row_eq_zero (hG : G.PosSemidef) (k : ℕ) (hk : k ≤ v)
    (i j : Fin v) (hi : i.val < k) : ldlResidual G k i j = 0 := by
  induction k generalizing i j with
  | zero => omega
  | succ k ih =>
    have hkv : k < v := by omega
    rw [residual_succ G k hkv]
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, of_apply]
    by_cases hik : i.val < k
    · rw [ih (i := i) (j := j) (by omega) hik,
        ih (i := i) (j := ⟨k, hkv⟩) (by omega) hik, zero_mul, mul_zero, sub_zero]
    · have hie : i = ⟨k, hkv⟩ := Fin.ext (by change i.val = k; omega)
      subst i
      by_cases hd : ldlResidual G k ⟨k, hkv⟩ ⟨k, hkv⟩ = 0
      · have hcol := column_eq_zero_of_diag_eq_zero (residual_posSemidef G hG k)
          ⟨k, hkv⟩ hd j
        have hsym := (residual_posSemidef G hG k).isHermitian.isSymm.apply j ⟨k, hkv⟩
        rw [hsym, hcol, mul_zero, mul_zero, sub_self]
      · field_simp
        ring

/-- All previously processed columns of the residual vanish. -/
theorem residual_column_eq_zero (hG : G.PosSemidef) (k : ℕ) (hk : k ≤ v)
    (i j : Fin v) (hj : j.val < k) : ldlResidual G k i j = 0 := by
  rw [(residual_posSemidef G hG k).isHermitian.isSymm.apply j i]
  exact residual_row_eq_zero G hG k hk j i hj

/-- After all indices have been processed, the residual is zero. -/
theorem residual_final (hG : G.PosSemidef) : ldlResidual G v = 0 := by
  ext i j
  exact residual_row_eq_zero G hG v le_rfl i j i.isLt

/-- Telescoping the residual updates recovers the original matrix entrywise. -/
theorem decomposition (hG : G.PosSemidef) (i j : Fin v) :
    (∑ k : Fin v, (ldlResidual G k k k)⁻¹ *
      ldlResidual G k k i * ldlResidual G k k j) = G i j := by
  calc
    _ = ∑ k : Fin v, (ldlResidual G k i j - ldlResidual G (k + 1) i j) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [residual_succ G k k.isLt]
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, of_apply]
      rw [(residual_posSemidef G hG k).isHermitian.isSymm.apply i k]
      ring
    _ = ∑ k ∈ Finset.range v, (ldlResidual G k i j - ldlResidual G (k + 1) i j) :=
      Fin.sum_univ_eq_sum_range (fun k => ldlResidual G k i j - ldlResidual G (k + 1) i j) v
    _ = ldlResidual G 0 i j - ldlResidual G v i j :=
      Finset.sum_range_sub' _ _
    _ = G i j := by rw [ldlResidual, residual_final G hG]; exact sub_zero _

end ExplicitRIP.LDL
