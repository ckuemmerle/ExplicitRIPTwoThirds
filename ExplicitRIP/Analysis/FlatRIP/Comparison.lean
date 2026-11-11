/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.FlatRIP.Basic
public import ExplicitRIP.Analysis.FlatRIP.CutEstimate

/-!
# Comparison of the flat and discrete Rayleigh parameters

The upper estimate covers every support cardinality, including zero and one.
-/

public section

namespace ExplicitRIP.Flat

open Finset
open scoped Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

omit [Fintype n] in
theorem principal_gram_error_entry (Φ : Matrix m n ℂ) (S : Finset n) (i j : S) :
    ((Φ.submatrix id (Subtype.val : S → n))ᴴ *
      Φ.submatrix id (Subtype.val : S → n) - (1 : Matrix S S ℂ)) i j =
      (Φᴴ * Φ - (1 : Matrix n n ℂ)) i.val j.val := by
  rw [Matrix.sub_apply, principal_gram_entry, Matrix.sub_apply]
  congr 1
  exact (congrArg (fun A : Matrix S S ℂ => A i j)
    (Matrix.submatrix_one (Subtype.val : S → n) Subtype.val_injective)).symm

theorem principal_drNorm_le_two_mul_flatConstant (Φ : Matrix m n ℂ)
    (hΦ : ∀ j, ∑ i, ‖Φ i j‖ ^ 2 = 1) (k : ℕ) (S : Finset n) (hSk : S.card ≤ 2 * k) :
    drNorm ((Φ.submatrix id (Subtype.val : S → n))ᴴ *
      Φ.submatrix id (Subtype.val : S → n) - (1 : Matrix S S ℂ)) ≤ 2 * flatConstant Φ k := by
  classical
  obtain ⟨⟨hθ, hflat⟩, _⟩ := flatConstant_isLeast Φ k
  apply drNorm_le _ (mul_nonneg (by norm_num) hθ)
  intro I J
  let e : S ↪ n := Function.Embedding.subtype _
  have hIS : I.map e ⊆ S := fun _ hi => property_of_mem_map_subtype I hi
  have hJS : J.map e ⊆ S := fun _ hj => property_of_mem_map_subtype J hj
  have h := rectangle_bound_of_disjoint_bound (Φᴴ * Φ - (1 : Matrix n n ℂ)) (gram_error_diag Φ hΦ)
    S k hSk (flatConstant Φ k) hθ (fun A B _ _ hAB hAk hBk => by
      rw [sum_gram_error_of_disjoint Φ A B hAB]
      exact hflat A B hAB hAk hBk) (I.map e) (J.map e) hIS hJS
  simpa only [sum_map, e, Function.Embedding.coe_subtype, card_map,
    ← principal_gram_error_entry] using h

theorem rhoConstant_le_two_mul_flatConstant (Φ : Matrix m n ℂ)
    (hΦ : ∀ j, ∑ i, ‖Φ i j‖ ^ 2 = 1) (k : ℕ) :
    rhoConstant Φ (2 * k) ≤ 2 * flatConstant Φ k := by
  apply Real.iSup_le ?_ (mul_nonneg (by norm_num) (flatConstant_isLeast Φ k).1.1)
  intro S
  exact principal_drNorm_le_two_mul_flatConstant Φ hΦ k S.1 S.2.2

end ExplicitRIP.Flat
