/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.UnsignedHybrid.NormComparison
public import ExplicitRIP.Analysis.FlatRIP.Basic
public import ExplicitRIP.Frozen.LevDRBound
public import ExplicitRIP.Analysis.Gershgorin.HermitianBound

/-!
# The unsigned threshold certificate

The threshold pieces have disjoint entry supports, so their moduli add exactly. Combining the
discrete Rayleigh estimate with Hermitian Gershgorin gives the unsigned bound.

Source: [KM, Sections 2.2 and 2.3, (6)–(8)].
-/

public section

open scoped Matrix

namespace ExplicitRIP.UnsignedHybrid

/-- The moduli of the disjoint threshold pieces add entrywise. -/
theorem map_norm_eq_add_threshold {𝕜 : Type*} [RCLike 𝕜] {n : Type*}
    (M : Matrix n n 𝕜) (τ : ℝ) :
    M.map (fun z => ‖z‖) =
      ((Matrix.of fun i j => if τ < ‖M i j‖ then M i j else 0).map fun z => ‖z‖) +
      ((M - Matrix.of fun i j => if τ < ‖M i j‖ then M i j else 0).map fun z => ‖z‖) := by
  classical
  ext i j
  simp only [Matrix.add_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.of_apply]
  split_ifs <;> simp only [sub_self, sub_zero, norm_zero, add_zero, zero_add]

/-- Symmetry of entry moduli survives the small-entry threshold. -/
theorem norm_threshold_small_symm {𝕜 : Type*} [RCLike 𝕜] {n : Type*}
    (M : Matrix n n 𝕜) (hsym : ∀ i j, ‖M i j‖ = ‖M j i‖) (τ : ℝ) (i j : n) :
    ‖(M - Matrix.of fun i j => if τ < ‖M i j‖ then M i j else 0) i j‖ =
      ‖(M - Matrix.of fun i j => if τ < ‖M i j‖ then M i j else 0) j i‖ := by
  classical
  simp only [Matrix.sub_apply, Matrix.of_apply]
  by_cases h : τ < ‖M i j‖
  · have h' : τ < ‖M j i‖ := by rwa [← hsym i j]
    rw [ite_eq_left h, ite_eq_left h', sub_self, sub_self]
  · have h' : ¬τ < ‖M j i‖ := by rwa [← hsym i j]
    rw [ite_eq_right h, ite_eq_right h', sub_zero, sub_zero]
    exact hsym i j

/-- The support-size logarithm can be enlarged to the prescribed sparsity. -/
theorem log_card_le_log_sparsity {t k : ℕ} (hk : 1 ≤ k) (ht : t ≤ k) :
    Real.log (2 * t) ≤ Real.log (2 * k) := by
  have hk' : (1 : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast (show 1 ≤ 2 * k by omega)
  by_cases ht0 : t = 0
  · simp only [ht0, Nat.cast_zero, mul_zero, Real.log_zero]
    exact Real.log_nonneg hk'
  · apply Real.log_le_log
    · positivity
    · exact_mod_cast Nat.mul_le_mul_left 2 ht

/-- A uniform hybrid bound for any matrix with symmetric entry moduli. -/
theorem abs_split_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {𝕜 : Type} [RCLike 𝕜] {n : Type} [DecidableEq n]
      (M : Matrix n n 𝕜), (∀ i j, ‖M i j‖ = ‖M j i‖) →
      ∀ (τ : ℝ) (k : ℕ), 1 ≤ k → ∀ S : Finset n, S.card ≤ k →
        let A : Matrix n n 𝕜 := Matrix.of fun i j => if τ < ‖M i j‖ then M i j else 0
        let B : Matrix n n 𝕜 := M - A
        opNorm ((M.map fun z => ‖z‖).submatrix (Subtype.val : S → n)
            (Subtype.val : S → n)) ≤
          C * (Real.log (2 * k) * drNorm
              ((A.map fun z => ‖z‖).submatrix (Subtype.val : S → n) (Subtype.val : S → n)) +
            oneToOneNorm (B.submatrix (Subtype.val : S → n) (Subtype.val : S → n))) := by
  classical
  obtain ⟨CL, hCL, hLev⟩ := ExplicitRIP.lev_dr_bound
  refine ⟨max CL 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro 𝕜 _ n _ M hsym τ k hk S hS
  let A : Matrix n n 𝕜 := Matrix.of fun i j => if τ < ‖M i j‖ then M i j else 0
  let B : Matrix n n 𝕜 := M - A
  let Ha := (A.map fun z => ‖z‖).submatrix (Subtype.val : S → n) (Subtype.val : S → n)
  let Hb := (B.map fun z => ‖z‖).submatrix (Subtype.val : S → n) (Subtype.val : S → n)
  change opNorm ((M.map fun z => ‖z‖).submatrix (Subtype.val : S → n)
      (Subtype.val : S → n)) ≤
    max CL 1 * (Real.log (2 * k) * drNorm Ha + oneToOneNorm
      (B.submatrix (Subtype.val : S → n) (Subtype.val : S → n)))
  have hsplit : (M.map fun z => ‖z‖).submatrix (Subtype.val : S → n)
      (Subtype.val : S → n) = Ha + Hb := by
    rw [map_norm_eq_add_threshold M τ]
    rfl
  have hA : opNorm Ha ≤ CL * Real.log (2 * S.card) * drNorm Ha := by
    calc
      opNorm Ha ≤ opNorm (Ha.map Complex.ofReal) :=
        opNorm_real_le_opNorm_complex Ha
      _ ≤ CL * Real.log (2 * Fintype.card S) * drNorm (Ha.map Complex.ofReal) := hLev S _
      _ = CL * Real.log (2 * S.card) * drNorm Ha := by
        rw [Fintype.card_coe, drNorm_map_ofReal]
  have hB : opNorm Hb ≤ oneToOneNorm
      (B.submatrix (Subtype.val : S → n) (Subtype.val : S → n)) := by
    calc
      opNorm Hb ≤ opNorm (Hb.map Complex.ofReal) :=
        opNorm_real_le_opNorm_complex Hb
      _ ≤ oneToOneNorm (Hb.map Complex.ofReal) :=
        Gersh.opNorm_le_oneToOneNorm_of_isHermitian
          (isHermitian_map_ofReal_of_symm Hb (fun i j =>
            norm_threshold_small_symm M hsym τ i j))
      _ = oneToOneNorm (B.submatrix (Subtype.val : S → n) (Subtype.val : S → n)) :=
        oneToOneNorm_map_norm_ofReal
          (B.submatrix (Subtype.val : S → n) (Subtype.val : S → n))
  have hd : 0 ≤ drNorm Ha := Flat.drNorm_nonneg Ha
  have ho : 0 ≤ oneToOneNorm
      (B.submatrix (Subtype.val : S → n) (Subtype.val : S → n)) :=
    Real.iSup_nonneg fun _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hlog : Real.log (2 * S.card) ≤ Real.log (2 * k) := log_card_le_log_sparsity hk hS
  have hL : 0 ≤ Real.log (2 * k) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * k by omega))
  calc
    opNorm ((M.map fun z => ‖z‖).submatrix (Subtype.val : S → n)
        (Subtype.val : S → n)) ≤ opNorm Ha + opNorm Hb := by
      rw [hsplit]
      exact Hybrid.opNorm_add_le Ha Hb
    _ ≤ CL * Real.log (2 * S.card) * drNorm Ha + oneToOneNorm
        (B.submatrix (Subtype.val : S → n) (Subtype.val : S → n)) := add_le_add hA hB
    _ ≤ CL * Real.log (2 * k) * drNorm Ha + oneToOneNorm
        (B.submatrix (Subtype.val : S → n) (Subtype.val : S → n)) :=
      add_le_add (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlog hCL.le) hd) le_rfl
    _ ≤ max CL 1 * (Real.log (2 * k) * drNorm Ha) + max CL 1 * oneToOneNorm
        (B.submatrix (Subtype.val : S → n) (Subtype.val : S → n)) := by
      rw [mul_assoc CL]
      exact add_le_add
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg hL hd))
        (le_mul_of_one_le_left ho (le_max_right _ _))
    _ = _ := (mul_add _ _ _).symm

end ExplicitRIP.UnsignedHybrid
