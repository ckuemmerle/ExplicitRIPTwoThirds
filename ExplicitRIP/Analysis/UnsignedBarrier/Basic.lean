/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Frozen.Defs.UnsignedRIPConstant
public import ExplicitRIP.Analysis.FlatRIP.Basic

/-!
# Matrix tests for the unsigned barrier

Coordinate-vector and all-ones tests bound the column energy and total mass of the absolute Gram
error.

Source: [KM, proof of Theorem 4, (12)].
-/

public section

open scoped BigOperators Matrix
open Finset

namespace ExplicitRIP.Absbar

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem opNorm_nonneg (M : Matrix ι ι ℝ) : 0 ≤ opNorm M := norm_nonneg _

theorem column_sq_le_opNorm_sq (M : Matrix ι ι ℝ) (i : ι) :
    ∑ j, M j i ^ 2 ≤ opNorm M ^ 2 := by
  let T := Matrix.toEuclideanCLM (𝕜 := ℝ) M
  have h := T.le_opNorm (EuclideanSpace.single i 1)
  have hnorm : ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by
    simp only [EuclideanSpace.single, PiLp.norm_single, norm_one]
  rw [hnorm, mul_one] at h
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
  have hcol : T (EuclideanSpace.single i 1) = WithLp.toLp 2 (fun j => M j i) := by
    change Matrix.toEuclideanCLM (𝕜 := ℝ) M (WithLp.toLp 2 (Pi.single i 1)) = _
    exact congrArg (WithLp.toLp 2) (Matrix.mulVec_single_one M i)
  change ‖T (EuclideanSpace.single i 1)‖ ^ 2 ≤ opNorm M ^ 2 at hsq
  rw [hcol, EuclideanSpace.norm_sq_eq] at hsq
  simpa only [WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs] using hsq

theorem sum_entries_le_card_mul_opNorm (M : Matrix ι ι ℝ) :
    (∑ i, ∑ j, M i j) ≤ (Fintype.card ι : ℝ) * opNorm M := by
  let x : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun _ => 1)
  let T := Matrix.toEuclideanCLM (𝕜 := ℝ) M
  have hx : ‖x‖ ^ 2 = (Fintype.card ι : ℝ) := by
    simp [x, EuclideanSpace.norm_sq_eq]
  have hi : inner ℝ x (T x) = ∑ i, ∑ j, M i j := by
    simp [x, T, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Matrix.mulVec]
  calc
    (∑ i, ∑ j, M i j) = inner ℝ x (T x) := hi.symm
    _ ≤ ‖x‖ * ‖T x‖ := real_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖T‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (T.le_opNorm x) (norm_nonneg x)
    _ = (Fintype.card ι : ℝ) * opNorm M := by
      change ‖x‖ * (opNorm M * ‖x‖) = _
      calc
        _ = ‖x‖ ^ 2 * opNorm M := by ring
        _ = _ := by rw [hx]

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

theorem principal_opNorm_le (Φ : Matrix m n ℂ) (k : ℕ) (S : Finset n)
    (hS : S.card ≤ k) :
    opNorm (((Φᴴ * Φ - (1 : Matrix n n ℂ)).map fun z => ‖z‖).submatrix
      (Subtype.val : S → n) (Subtype.val : S → n)) ≤ unsignedRIPConstant Φ k := by
  let value : {T : Finset n // T.card ≤ k} → ℝ := fun T =>
    opNorm (((Φᴴ * Φ - (1 : Matrix n n ℂ)).map fun z => ‖z‖).submatrix
      (Subtype.val : T.1 → n) (Subtype.val : T.1 → n))
  exact le_ciSup (f := value) (Finite.bddAbove_range value) ⟨S, hS⟩

theorem unsignedRIPConstant_nonneg (Φ : Matrix m n ℂ) (k : ℕ) :
    0 ≤ unsignedRIPConstant Φ k :=
  (opNorm_nonneg _).trans (principal_opNorm_le Φ k ∅ (by simp))

theorem support_column_sq_le (Φ : Matrix m n ℂ) (k : ℕ) (i : n)
    (S : Finset n) (hS : S.card + 1 ≤ k) :
    (∑ j ∈ S, ‖(Φᴴ * Φ - (1 : Matrix n n ℂ)) j i‖ ^ 2) ≤ unsignedRIPConstant Φ k ^ 2 := by
  classical
  let U := insert i S
  let ii : U := ⟨i, mem_insert_self i S⟩
  have hU : U.card ≤ k := (card_insert_le i S).trans hS
  have hnorm := principal_opNorm_le Φ k U hU
  have hsq := (column_sq_le_opNorm_sq
    (((Φᴴ * Φ - (1 : Matrix n n ℂ)).map fun z => ‖z‖).submatrix
      (Subtype.val : U → n) (Subtype.val : U → n)) ii).trans
    (pow_le_pow_left₀ (opNorm_nonneg _) hnorm 2)
  have hsum : (∑ j : U, ‖(Φᴴ * Φ - (1 : Matrix n n ℂ)) j i‖ ^ 2) =
      ∑ j ∈ U, ‖(Φᴴ * Φ - (1 : Matrix n n ℂ)) j i‖ ^ 2 := by
    exact sum_coe_sort U (fun j : n => ‖(Φᴴ * Φ - (1 : Matrix n n ℂ)) j i‖ ^ 2)
  change (∑ j : U, ‖(Φᴴ * Φ - (1 : Matrix n n ℂ)) j i‖ ^ 2) ≤ _ at hsq
  rw [hsum] at hsq
  exact (sum_le_sum_of_subset_of_nonneg (subset_insert i S)
    (fun j _ _ => sq_nonneg _)).trans hsq

theorem support_mass_le (Φ : Matrix m n ℂ) (k : ℕ) (S : Finset n)
    (hS : S.card ≤ k) :
    (∑ i ∈ S, ∑ j ∈ S, ‖(Φᴴ * Φ - (1 : Matrix n n ℂ)) i j‖) ≤
      (S.card : ℝ) * unsignedRIPConstant Φ k := by
  have h := (sum_entries_le_card_mul_opNorm
    (((Φᴴ * Φ - (1 : Matrix n n ℂ)).map fun z => ‖z‖).submatrix
      (Subtype.val : S → n) (Subtype.val : S → n))).trans
    (mul_le_mul_of_nonneg_left (principal_opNorm_le Φ k S hS)
      (Nat.cast_nonneg _))
  have hsum : (∑ i : S, ∑ j : S, ‖(Φᴴ * Φ - (1 : Matrix n n ℂ)) i j‖) =
      ∑ i ∈ S, ∑ j ∈ S, ‖(Φᴴ * Φ - (1 : Matrix n n ℂ)) i j‖ := by
    rw [sum_coe_sort S (fun i : n => ∑ j : S, ‖(Φᴴ * Φ - (1 : Matrix n n ℂ)) i j‖)]
    apply sum_congr rfl
    intro i _
    exact sum_coe_sort S (fun j : n => ‖(Φᴴ * Φ - (1 : Matrix n n ℂ)) i j‖)
  change (∑ i : S, ∑ j : S, ‖(Φᴴ * Φ - (1 : Matrix n n ℂ)) i j‖) ≤
    (Fintype.card S : ℝ) * unsignedRIPConstant Φ k at h
  rwa [hsum, Fintype.card_coe] at h

theorem rows_pos_of_unit_columns (m n : ℕ) (Φ : Matrix (Fin m) (Fin n) ℂ)
    (hunit : ∀ j, ∑ i, ‖Φ i j‖ ^ 2 = 1) (hn : 0 < n) : 0 < m := by
  by_contra! hm
  have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
  subst m
  have h := hunit ⟨0, hn⟩
  simp at h

end ExplicitRIP.Absbar
