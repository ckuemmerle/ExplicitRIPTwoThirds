/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Frozen.Defs.RIPConstant
public import ExplicitRIP.Analysis.RIPOneTwo.Basic
public import ExplicitRIP.Analysis.Gershgorin.HermitianBound
public import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Gershgorin

/-!
# Proof of [KM, (2)]: the coherence bound

Source: [KM, Section 1, (2)].

For unit-norm columns, every support Gram error has zero diagonal and off-diagonal entries
bounded by the coherence. Gershgorin bounds its Euclidean operator norm by the row sums; taking
the supremum over supports proves `δ_k ≤ (k - 1) μ` for `k ≥ 1`.
-/

public section

open scoped Matrix Matrix.Norms.L2Operator

namespace ExplicitRIP.CoherenceBound

section Hermitian

variable {𝕜 : Type*} [RCLike 𝕜] {q : Type*} [Fintype q] [DecidableEq q]
  {M : Matrix q q 𝕜}

/-- Gershgorin bounds the Euclidean operator norm of a Hermitian matrix by a row bound. -/
theorem opNorm_le_of_isHermitian_of_row_sum_le (hM : M.IsHermitian) {B : ℝ} (hB : 0 ≤ B)
    (hrow : ∀ a, ∑ b, ‖M a b‖ ≤ B) : ExplicitRIP.opNorm M ≤ B := by
  rw [Gersh.opNorm_eq_norm_eigenvalues hM]
  refine (pi_norm_le_iff_of_nonneg hB).2 fun i ↦ ?_
  have heig : Module.End.HasEigenvalue (Matrix.toLin' M)
      (RCLike.ofReal (hM.eigenvalues i) : 𝕜) := by
    apply Module.End.HasEigenvalue.of_mem_spectrum
    rw [Matrix.spectrum_toLin', hM.spectrum_eq_image_range]
    exact Set.mem_image_of_mem _ (Set.mem_range_self i)
  obtain ⟨a, ha⟩ := eigenvalue_mem_ball heig
  rw [Metric.mem_closedBall, dist_eq_norm] at ha
  calc
    ‖(RCLike.ofReal (hM.eigenvalues i) : 𝕜)‖
        = ‖((RCLike.ofReal (hM.eigenvalues i) : 𝕜) - M a a) + M a a‖ := by
          rw [sub_add_cancel]
    _ ≤ ‖(RCLike.ofReal (hM.eigenvalues i) : 𝕜) - M a a‖ + ‖M a a‖ := norm_add_le _ _
    _ ≤ (∑ b ∈ Finset.univ.erase a, ‖M a b‖) + ‖M a a‖ := add_le_add ha le_rfl
    _ = ∑ b, ‖M a b‖ := Finset.sum_erase_add _ _ (Finset.mem_univ a)
    _ ≤ B := hrow a

end Hermitian

section Columns

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

omit [Fintype n] in
/-- Unit columns give unit diagonal entries in the Gram matrix. -/
theorem gram_diag_eq_one (Φ : Matrix m n 𝕜)
    (hcol : ∀ j, ∑ i, ‖Φ i j‖ ^ 2 = 1) (b : n) : (Φᴴ * Φ) b b = 1 := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def, RCLike.conj_mul]
  have h := congrArg (RCLike.ofReal : ℝ → 𝕜) (hcol b)
  push_cast at h
  exact h

omit [Fintype n] in
/-- A support Gram error has the corresponding full Gram entries, minus the identity. -/
theorem support_gram_apply [DecidableEq n] (Φ : Matrix m n 𝕜)
    (S : Finset n) (a b : S) :
    ((Φ.submatrix id (Subtype.val : S → n))ᴴ * Φ.submatrix id (Subtype.val : S → n) - 1 :
      Matrix S S 𝕜) a b =
      (Φᴴ * Φ) a.1 b.1 - (1 : Matrix S S 𝕜) a b := by
  rfl

/-- Each support of size at most `k` has Gram error norm at most `(k - 1) μ`. -/
theorem opNorm_support_gram_le [DecidableEq n] (Φ : Matrix m n 𝕜)
    (hcol : ∀ j, ∑ i, ‖Φ i j‖ ^ 2 = 1) (k : ℕ) (hk : 1 ≤ k)
    (S : Finset n) (hS : S.card ≤ k) :
    ExplicitRIP.opNorm ((Φ.submatrix id (Subtype.val : S → n))ᴴ *
      Φ.submatrix id (Subtype.val : S → n) - 1) ≤ ((k : ℝ) - 1) * ExplicitRIP.coherence Φ := by
  have hμ := RIPOneTwo.coherence_nonneg Φ
  have hB : 0 ≤ ((k : ℝ) - 1) * ExplicitRIP.coherence Φ :=
    mul_nonneg (sub_nonneg.2 (by exact_mod_cast hk)) hμ
  refine opNorm_le_of_isHermitian_of_row_sum_le
    ((Matrix.isHermitian_conjTranspose_mul_self _).sub Matrix.isHermitian_one) hB fun a ↦ ?_
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
  have hdiag : ‖((Φ.submatrix id (Subtype.val : S → n))ᴴ *
      Φ.submatrix id (Subtype.val : S → n) - 1 : Matrix S S 𝕜) a a‖ = 0 := by
    rw [support_gram_apply, gram_diag_eq_one Φ hcol, Matrix.one_apply_eq, sub_self, norm_zero]
  have hoff : ∀ b ∈ Finset.univ.erase a, ‖((Φ.submatrix id (Subtype.val : S → n))ᴴ *
      Φ.submatrix id (Subtype.val : S → n) - 1 : Matrix S S 𝕜) a b‖ ≤ ExplicitRIP.coherence Φ := by
    intro b hb
    have hab : a ≠ b := (Finset.ne_of_mem_erase hb).symm
    rw [support_gram_apply, Matrix.one_apply_ne hab, sub_zero]
    exact RIPOneTwo.gram_norm_le_coherence Φ _ _ fun h ↦ hab (Subtype.ext h)
  have hcard : ((Finset.univ.erase a).card : ℝ) ≤ (k : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_coe]
    have h1 : 1 ≤ S.card := Finset.card_pos.2 ⟨a.1, a.2⟩
    rw [Nat.cast_sub h1]
    push_cast
    exact sub_le_sub_right (by exact_mod_cast hS) 1
  calc
    _ ≤ 0 + (Finset.univ.erase a).card • ExplicitRIP.coherence Φ :=
      add_le_add hdiag.le (Finset.sum_le_card_nsmul _ _ _ hoff)
    _ ≤ ((k : ℝ) - 1) * ExplicitRIP.coherence Φ := by
      rw [zero_add, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hcard hμ

end Columns

end ExplicitRIP.CoherenceBound

/-- For unit columns, the restricted isometry constant is at most `(k - 1)` times coherence. -/
theorem ExplicitRIP.Provider.ripConstant_le_coherence :
    ∀ {𝕜 : Type} [RCLike 𝕜] {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
      (Φ : Matrix m n 𝕜), (∀ j, ∑ i, ‖Φ i j‖ ^ 2 = 1) → ∀ k : ℕ, 1 ≤ k →
        ExplicitRIP.ripConstant Φ k ≤ ((k : ℝ) - 1) * ExplicitRIP.coherence Φ := by
  intro 𝕜 _ m n _ _ _ Φ hcol k hk
  exact Real.iSup_le
    (fun S ↦ ExplicitRIP.CoherenceBound.opNorm_support_gram_le Φ hcol k hk S.1 S.2)
    (mul_nonneg (sub_nonneg.2 (by exact_mod_cast hk))
      (ExplicitRIP.RIPOneTwo.coherence_nonneg Φ))

end
