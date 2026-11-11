/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Frozen.Defs.DRNorm
public import ExplicitRIP.Frozen.Defs.Coherence
import ExplicitRIP.Analysis.FlatRIP.Basic

/-!
# Support domination and the coherence envelope

Rectangle estimates bound the large-entry part of a threshold decomposition by its support and
the coherence.

Source: [KM, Section 2.2, (6), (8)].
-/

public section

open scoped BigOperators Matrix

namespace ExplicitRIP.Large

/-- Entrywise magnitudes are dominated in discrete Rayleigh norm by their binary support. -/
theorem drNorm_abs_le_max_mul_support {𝕜 q : Type*} [RCLike 𝕜] [Fintype q]
    (X : Matrix q q 𝕜) :
    drNorm (X.map fun z => ‖z‖) ≤
      (⨆ ij : q × q, ‖X ij.1 ij.2‖) *
        drNorm (Matrix.of fun i j => if X i j = 0 then (0 : ℝ) else 1) := by
  classical
  let A : Matrix q q ℝ := Matrix.of fun i j => if X i j = 0 then 0 else 1
  let C : ℝ := ⨆ ij : q × q, ‖X ij.1 ij.2‖
  have hC : 0 ≤ C := Real.iSup_nonneg fun _ => norm_nonneg _
  have hA (i j : q) : 0 ≤ A i j := by
    dsimp only [A, Matrix.of_apply]
    split_ifs <;> norm_num
  have hentry (i j : q) : ‖X i j‖ ≤ C * A i j := by
    by_cases hx : X i j = 0
    · simp only [hx, norm_zero, A, Matrix.of_apply, ite_true, mul_zero, le_refl]
    · simpa only [A, Matrix.of_apply, ite_eq_right hx, mul_one] using
        (le_ciSup (Finite.bddAbove_range (fun ij : q × q => ‖X ij.1 ij.2‖)) (i, j))
  change drNorm (X.map fun z => ‖z‖) ≤ C * drNorm A
  apply Real.iSup_le ?_ (mul_nonneg hC (ExplicitRIP.Flat.drNorm_nonneg A))
  intro IJ
  have hsumX : 0 ≤ ∑ i ∈ IJ.1.1, ∑ j ∈ IJ.1.2, ‖X i j‖ :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  have hsumA : 0 ≤ ∑ i ∈ IJ.1.1, ∑ j ∈ IJ.1.2, A i j :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hA i j
  have hsum : (∑ i ∈ IJ.1.1, ∑ j ∈ IJ.1.2, ‖X i j‖) ≤
      C * ∑ i ∈ IJ.1.1, ∑ j ∈ IJ.1.2, A i j := by
    calc
      _ ≤ ∑ i ∈ IJ.1.1, ∑ j ∈ IJ.1.2, C * A i j :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hentry i j
      _ = _ := by simp only [Finset.mul_sum]
  change ‖∑ i ∈ IJ.1.1, ∑ j ∈ IJ.1.2, ‖X i j‖‖ /
    Real.sqrt ((IJ.1.1.card : ℝ) * IJ.1.2.card) ≤ C * drNorm A
  rw [Real.norm_of_nonneg hsumX]
  calc
    _ ≤ (C * ∑ i ∈ IJ.1.1, ∑ j ∈ IJ.1.2, A i j) /
        Real.sqrt ((IJ.1.1.card : ℝ) * IJ.1.2.card) :=
      div_le_div_of_nonneg_right hsum (Real.sqrt_nonneg _)
    _ = C * (‖∑ i ∈ IJ.1.1, ∑ j ∈ IJ.1.2, A i j‖ /
        Real.sqrt ((IJ.1.1.card : ℝ) * IJ.1.2.card)) := by
      rw [Real.norm_of_nonneg hsumA, mul_div_assoc]
    _ ≤ C * drNorm A := mul_le_mul_of_nonneg_left
      (ExplicitRIP.Flat.normalized_le_drNorm A _ _ IJ.2.1 IJ.2.2) hC

/-- Every entry of a normalized Gram error is bounded by column coherence. -/
theorem gram_error_entry_norm_le_coherence {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (Φ : Matrix m n ℂ)
    (hΦ : ∀ j, ∑ i, ‖Φ i j‖ ^ 2 = 1) (i j : n) :
    ‖(Φᴴ * Φ - (1 : Matrix n n ℂ)) i j‖ ≤ coherence Φ := by
  by_cases hij : i = j
  · subst j
    rw [ExplicitRIP.Flat.gram_error_diag Φ hΦ i, norm_zero]
    exact Real.iSup_nonneg fun _ => norm_nonneg _
  · simp only [Matrix.sub_apply, Matrix.one_apply_ne hij, sub_zero]
    exact le_ciSup (Finite.bddAbove_range
      (fun ij : {ij : n × n // ij.1 ≠ ij.2} => ‖(Φᴴ * Φ) ij.1.1 ij.1.2‖))
      ⟨(i, j), hij⟩

/-- Thresholding a principal Gram error preserves the coherence bound, including empty supports. -/
theorem threshold_max_le_coherence {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (Φ : Matrix m n ℂ)
    (hΦ : ∀ j, ∑ i, ‖Φ i j‖ ^ 2 = 1) (τ : ℝ) (S : Finset n) :
    let M : Matrix S S ℂ :=
      (Φᴴ * Φ - 1).submatrix (Subtype.val : S → n) (Subtype.val : S → n)
    let X : Matrix S S ℂ := Matrix.of fun i j => if τ < ‖M i j‖ then M i j else 0
    (⨆ ij : S × S, ‖X ij.1 ij.2‖) ≤ coherence Φ := by
  dsimp only
  apply Real.iSup_le ?_ (Real.iSup_nonneg fun _ => norm_nonneg _)
  rintro ⟨i, j⟩
  change ‖if τ < ‖(Φᴴ * Φ - (1 : Matrix n n ℂ)) i.1 j.1‖ then
    (Φᴴ * Φ - (1 : Matrix n n ℂ)) i.1 j.1 else 0‖ ≤ _
  calc
    _ ≤ ‖(Φᴴ * Φ - (1 : Matrix n n ℂ)) i.1 j.1‖ := by
      split_ifs
      · exact le_rfl
      · simpa only [norm_zero] using
          norm_nonneg ((Φᴴ * Φ - (1 : Matrix n n ℂ)) i.1 j.1)
    _ ≤ coherence Φ := gram_error_entry_norm_le_coherence Φ hΦ i.1 j.1

end ExplicitRIP.Large
