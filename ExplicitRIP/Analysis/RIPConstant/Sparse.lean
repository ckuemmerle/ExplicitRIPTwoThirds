/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.RIPConstant.Quadratic

/-!
# Sparse vectors and principal Gram errors

Zero extension identifies sparse-vector distortion with principal Gram errors. The finite-sum
argument works over `RCLike` scalars.

Source: [KM, Section 1].
-/

@[expose] public section

namespace ExplicitRIP.Ripc

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*}
variable [Fintype m] [Fintype n] [DecidableEq n]

/-- Extend coefficients on a selected column set by zero. -/
noncomputable def zeroExtend (S : Finset n) (x : S → 𝕜) : n → 𝕜 :=
  fun j ↦ if h : j ∈ S then x ⟨j, h⟩ else 0

theorem sum_zeroExtend {V : Type*} [AddCommMonoid V]
    (S : Finset n) (x : S → 𝕜) (f : n → 𝕜 → V) (hf : ∀ j, f j 0 = 0) :
    (∑ j, f j (zeroExtend S x j)) = ∑ j : S, f j.val (x j) := by
  classical
  calc
    _ = ∑ j ∈ S, f j (zeroExtend S x j) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      simp only [zeroExtend, dite_eq_right hj, hf]
    _ = _ := by
      rw [Finset.sum_subtype S (fun _ ↦ Iff.rfl) (fun j ↦ f j (zeroExtend S x j))]
      apply Finset.sum_congr rfl
      intro j _
      simp only [zeroExtend, dite_eq_left j.property]

theorem sum_norm_sq_zeroExtend (S : Finset n) (x : S → 𝕜) :
    (∑ j, ‖zeroExtend S x j‖ ^ 2) = ∑ j : S, ‖x j‖ ^ 2 :=
  sum_zeroExtend S x (fun _ z ↦ ‖z‖ ^ 2) (by simp)

omit [Fintype m] in
theorem mulVec_zeroExtend (Φ : Matrix m n 𝕜) (S : Finset n) (x : S → 𝕜) :
    Φ *ᵥ zeroExtend S x = (Φ.submatrix id Subtype.val) *ᵥ x := by
  funext i
  exact sum_zeroExtend S x (fun j z ↦ Φ i j * z) (by simp)

omit [Fintype n] in
theorem support_zeroExtend_subset (S : Finset n) (x : S → 𝕜) :
    Function.support (zeroExtend S x) ⊆ (S : Set n) := by
  intro j hj
  by_contra hjS
  change j ∉ S at hjS
  exact hj (by simp only [zeroExtend, dite_eq_right hjS])

omit [Fintype n] in
theorem support_zeroExtend_ncard_le (S : Finset n) (x : S → 𝕜) :
    (Function.support (zeroExtend S x)).ncard ≤ S.card := by
  simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard (support_zeroExtend_subset S x)

theorem sparse_abs_iff_principal_opNorm (Φ : Matrix m n 𝕜) (k : ℕ)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (∀ z : n → 𝕜, (Function.support z).ncard ≤ k →
      |(∑ i, ‖(Φ *ᵥ z) i‖ ^ 2) - ∑ j, ‖z j‖ ^ 2| ≤ δ * ∑ j, ‖z j‖ ^ 2) ↔
    ∀ S : Finset n, S.card ≤ k →
      ExplicitRIP.opNorm ((Φ.submatrix id (Subtype.val : S → n))ᴴ *
        Φ.submatrix id (Subtype.val : S → n) - 1) ≤ δ := by
  classical
  constructor
  · intro h S hS
    apply (gram_error_opNorm_le_iff _ hδ).mpr
    intro x
    have hx := h (zeroExtend S x) ((support_zeroExtend_ncard_le S x).trans hS)
    simpa only [mulVec_zeroExtend, sum_norm_sq_zeroExtend] using hx
  · intro h z hz
    let S := (Function.support z).toFinset
    let x : S → 𝕜 := fun j ↦ z j.val
    have hS : S.card ≤ k := by
      simpa only [S, ← Set.ncard_eq_toFinset_card'] using hz
    have he : zeroExtend S x = z := by
      funext j
      by_cases hj : z j = 0
      · simp [zeroExtend, S, hj, Function.mem_support]
      · simp [zeroExtend, S, x, hj, Function.mem_support]
    have hn : (∑ j, ‖z j‖ ^ 2) = ∑ j : S, ‖x j‖ ^ 2 := by
      rw [← he]
      exact sum_norm_sq_zeroExtend S x
    have hm : Φ *ᵥ z = (Φ.submatrix id Subtype.val) *ᵥ x := by
      rw [← he]
      exact mulVec_zeroExtend Φ S x
    have hx := (gram_error_opNorm_le_iff _ hδ).mp (h S hS) x
    rwa [← hm, ← hn] at hx

theorem sparse_bounds_iff_principal_opNorm (Φ : Matrix m n 𝕜) (k : ℕ)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (∀ z : n → 𝕜, (Function.support z).ncard ≤ k →
      (1 - δ) * ∑ j, ‖z j‖ ^ 2 ≤ ∑ i, ‖(Φ *ᵥ z) i‖ ^ 2 ∧
        ∑ i, ‖(Φ *ᵥ z) i‖ ^ 2 ≤ (1 + δ) * ∑ j, ‖z j‖ ^ 2) ↔
    ∀ S : Finset n, S.card ≤ k →
      ExplicitRIP.opNorm ((Φ.submatrix id (Subtype.val : S → n))ᴴ *
        Φ.submatrix id (Subtype.val : S → n) - 1) ≤ δ := by
  rw [← sparse_abs_iff_principal_opNorm Φ k hδ]
  apply forall_congr'
  intro z
  apply forall_congr'
  intro _
  rw [abs_le]
  constructor
  · rintro ⟨hl, hu⟩
    constructor <;> linarith only [hl, hu]
  · rintro ⟨hl, hu⟩
    constructor <;> linarith only [hl, hu]

end ExplicitRIP.Ripc
