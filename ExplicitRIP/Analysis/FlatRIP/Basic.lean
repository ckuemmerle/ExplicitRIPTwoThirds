/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Frozen.Defs.DRNorm
public import ExplicitRIP.Frozen.Defs.RhoConstant
public import ExplicitRIP.Frozen.FlatConstantCharacterization

/-!
# Finite maxima and principal Gram rectangles

Basic bridges for the lower inequality of [KM, Lemma 2], including empty maxima.
-/

public section

namespace ExplicitRIP.Flat

open Finset
open scoped Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {m n q : Type*}

theorem drNorm_nonneg [Fintype q] (M : Matrix q q 𝕜) : 0 ≤ drNorm M := by
  exact Real.iSup_nonneg fun _ => div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)

theorem normalized_le_drNorm [Fintype q] (M : Matrix q q 𝕜)
    (I J : Finset q) (hI : I.Nonempty) (hJ : J.Nonempty) :
    ‖∑ i ∈ I, ∑ j ∈ J, M i j‖ / Real.sqrt ((I.card : ℝ) * J.card) ≤ drNorm M := by
  classical
  let value : {IJ : Finset q × Finset q // IJ.1.Nonempty ∧ IJ.2.Nonempty} → ℝ :=
    fun IJ => ‖∑ i ∈ IJ.1.1, ∑ j ∈ IJ.1.2, M i j‖ /
      Real.sqrt ((IJ.1.1.card : ℝ) * IJ.1.2.card)
  exact le_ciSup (f := value) (Finite.bddAbove_range value) ⟨(I, J), hI, hJ⟩

theorem drNorm_le [Fintype q] (M : Matrix q q 𝕜) {θ : ℝ} (hθ : 0 ≤ θ)
    (h : ∀ I J : Finset q, ‖∑ i ∈ I, ∑ j ∈ J, M i j‖ ≤
      θ * Real.sqrt ((I.card : ℝ) * J.card)) : drNorm M ≤ θ := by
  apply Real.iSup_le ?_ hθ
  intro IJ
  have hs : 0 < Real.sqrt ((IJ.1.1.card : ℝ) * IJ.1.2.card) :=
    Real.sqrt_pos.mpr (mul_pos (Nat.cast_pos.mpr IJ.2.1.card_pos)
      (Nat.cast_pos.mpr IJ.2.2.card_pos))
  exact (div_le_iff₀ hs).mpr (h _ _)

theorem rhoConstant_nonneg [Fintype m] [Fintype n] [DecidableEq n]
    (Φ : Matrix m n 𝕜) (k : ℕ) : 0 ≤ rhoConstant Φ k :=
  Real.iSup_nonneg fun _ => drNorm_nonneg _

theorem principal_drNorm_le_rhoConstant [Fintype m] [Fintype n] [DecidableEq n]
    (Φ : Matrix m n 𝕜) (k : ℕ) (S : Finset n) (hS : S.Nonempty) (hSk : S.card ≤ k) :
    drNorm ((Φ.submatrix id (Subtype.val : S → n))ᴴ *
      Φ.submatrix id (Subtype.val : S → n) - (1 : Matrix S S 𝕜)) ≤ rhoConstant Φ k := by
  classical
  let value : {T : Finset n // T.Nonempty ∧ T.card ≤ k} → ℝ := fun T =>
    drNorm ((Φ.submatrix id (Subtype.val : T.1 → n))ᴴ *
      Φ.submatrix id (Subtype.val : T.1 → n) - 1)
  exact le_ciSup (f := value) (Finite.bddAbove_range value) ⟨S, hS, hSk⟩

theorem principal_gram_entry [Fintype m] (Φ : Matrix m n 𝕜) (S : Finset n) (i j : S) :
    ((Φ.submatrix id (Subtype.val : S → n))ᴴ *
      Φ.submatrix id (Subtype.val : S → n)) i j = (Φᴴ * Φ) i j := by
  rfl

theorem sum_gram_error_of_disjoint [Fintype m] [DecidableEq n]
    (Φ : Matrix m n 𝕜) (I J : Finset n) (hIJ : Disjoint I J) :
    (∑ i ∈ I, ∑ j ∈ J, (Φᴴ * Φ - (1 : Matrix n n 𝕜)) i j) =
      ∑ i ∈ I, ∑ j ∈ J, (Φᴴ * Φ) i j := by
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  have hij : i ≠ j := fun hij => (disjoint_left.mp hIJ hi) (hij.symm ▸ hj)
  simp only [Matrix.sub_apply, Matrix.one_apply_ne hij, sub_zero]

theorem flatConstant_le_rhoConstant [Fintype m] [Fintype n] [DecidableEq n]
    (Φ : Matrix m n 𝕜) (k : ℕ) : flatConstant Φ k ≤ rhoConstant Φ (2 * k) := by
  classical
  apply Real.iSup_le ?_ (rhoConstant_nonneg Φ _)
  intro IJ
  let I := IJ.1.1
  let J := IJ.1.2
  let S := I ∪ J
  let I' : Finset S := I.subtype (· ∈ S)
  let J' : Finset S := J.subtype (· ∈ S)
  have hIS : I ⊆ S := subset_union_left
  have hJS : J ⊆ S := subset_union_right
  have hImap : I'.map (Function.Embedding.subtype _) = I := subtype_map_of_mem hIS
  have hJmap : J'.map (Function.Embedding.subtype _) = J := subtype_map_of_mem hJS
  have hIc : I'.card = I.card := by rw [← hImap, card_map]
  have hJc : J'.card = J.card := by rw [← hJmap, card_map]
  have hIn : I'.Nonempty := by
    apply card_pos.mp
    rw [hIc]
    exact IJ.2.1.card_pos
  have hJn : J'.Nonempty := by
    apply card_pos.mp
    rw [hJc]
    exact IJ.2.2.1.card_pos
  have hdis : Disjoint I' J' := (disjoint_map (Function.Embedding.subtype _)).mp
    (by rw [hImap, hJmap]; exact IJ.2.2.2.1)
  have hsum : (∑ i ∈ I', ∑ j ∈ J',
      ((Φ.submatrix id (Subtype.val : S → n))ᴴ *
        Φ.submatrix id (Subtype.val : S → n) - (1 : Matrix S S 𝕜)) i j) =
      ∑ i ∈ I, ∑ j ∈ J, (Φᴴ * Φ) i j := by
    rw [sum_gram_error_of_disjoint _ _ _ hdis]
    simp_rw [principal_gram_entry]
    conv_rhs => rw [← hImap, ← hJmap]
    simp only [sum_map, Function.Embedding.coe_subtype]
  have hSk : S.card ≤ 2 * k :=
    (card_union_le I J).trans (by have := IJ.2.2.2.2.1; have := IJ.2.2.2.2.2; dsimp [I, J]; omega)
  have hSn : S.Nonempty := IJ.2.1.mono hIS
  have h := (normalized_le_drNorm
    ((Φ.submatrix id (Subtype.val : S → n))ᴴ *
      Φ.submatrix id (Subtype.val : S → n) - (1 : Matrix S S 𝕜)) I' J' hIn hJn).trans
    (principal_drNorm_le_rhoConstant Φ (2 * k) S hSn hSk)
  simpa only [hsum, hIc, hJc] using h

theorem gram_error_diag {m n : Type*} [Fintype m] [DecidableEq n]
    (Φ : Matrix m n ℂ) (hΦ : ∀ j, ∑ i, ‖Φ i j‖ ^ 2 = 1) (j : n) :
    (Φᴴ * Φ - (1 : Matrix n n ℂ)) j j = 0 := by
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply_eq, RCLike.star_def, Complex.conj_mul',
    ← Complex.ofReal_pow, ← Complex.ofReal_sum, hΦ j, Complex.ofReal_one, sub_self]

end ExplicitRIP.Flat
