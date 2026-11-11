/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Frozen.Defs.Coherence

/-!
# One- and two-column energy formulas

The elementary Gram calculations and coherence bounds give the first two restricted isometry
constants.

Source: [KM, Section 2.2].
-/

public section

open scoped Matrix

namespace ExplicitRIP.RIPOneTwo

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

theorem sum_eq_single_of_eq_zero {V : Type*} [AddCommMonoid V] (f : n → V)
    (a : n) (hf : ∀ j, j ≠ a → f j = 0) : ∑ j, f j = f a := by
  exact Finset.sum_eq_single a (fun j _ hj ↦ hf j hj) (by simp)

theorem sum_eq_pair_of_eq_zero {V : Type*} [AddCommMonoid V] (f : n → V)
    (a b : n) (hab : a ≠ b) (hf : ∀ j, j ≠ a → j ≠ b → f j = 0) :
    ∑ j, f j = f a + f b := by
  classical
  calc
    ∑ j, f j = ∑ j ∈ ({a, b} : Finset n), f j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
      exact hf j hj.1 hj.2
    _ = f a + f b := Finset.sum_pair hab

omit [Fintype n] in
theorem support_cases_one [Finite n] (z : n → 𝕜) (hz : (Function.support z).ncard ≤ 1) :
    z = 0 ∨ ∃ a, ∀ j, j ≠ a → z j = 0 := by
  by_cases hzero : (Function.support z).ncard = 0
  · left
    have hs := (Set.ncard_eq_zero (Set.toFinite _)).mp hzero
    ext j
    apply Function.notMem_support.mp
    rw [hs]
    exact Set.notMem_empty j
  · right
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp (show (Function.support z).ncard = 1 by omega)
    refine ⟨a, fun j hj ↦ Function.notMem_support.mp ?_⟩
    simpa only [ha, Set.mem_singleton_iff] using hj

omit [Fintype n] in
theorem support_cases_two [Finite n] (z : n → 𝕜) (hz : (Function.support z).ncard ≤ 2) :
    z = 0 ∨ (∃ a, ∀ j, j ≠ a → z j = 0) ∨
      ∃ a b, a ≠ b ∧ ∀ j, j ≠ a → j ≠ b → z j = 0 := by
  by_cases hsmall : (Function.support z).ncard ≤ 1
  · rcases support_cases_one z hsmall with hzero | hone
    · exact Or.inl hzero
    · exact Or.inr (Or.inl hone)
  · obtain ⟨a, b, hab, hs⟩ := Set.ncard_eq_two.mp
      (show (Function.support z).ncard = 2 by omega)
    refine Or.inr (Or.inr ⟨a, b, hab, fun j hja hjb ↦ Function.notMem_support.mp ?_⟩)
    simp only [hs, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hja, hjb⟩

theorem energy_single (Φ : Matrix m n 𝕜)
    (hΦ : ∀ j, ∑ i, ‖Φ i j‖ ^ 2 = 1) (z : n → 𝕜)
    (a : n) (hz : ∀ j, j ≠ a → z j = 0) :
    (∑ i, ‖(Φ *ᵥ z) i‖ ^ 2) = ∑ j, ‖z j‖ ^ 2 := by
  have hrow (i : m) : (Φ *ᵥ z) i = Φ i a * z a := by
    exact sum_eq_single_of_eq_zero (fun j ↦ Φ i j * z j) a
      (fun j hj ↦ by rw [hz j hj, mul_zero])
  rw [sum_eq_single_of_eq_zero (fun j ↦ ‖z j‖ ^ 2) a
    (fun j hj ↦ by rw [hz j hj, norm_zero, zero_pow (by decide : 2 ≠ 0)])]
  simp_rw [hrow, norm_mul, mul_pow]
  rw [← Finset.sum_mul, hΦ a, one_mul]

theorem norm_add_sq (u v : 𝕜) :
    ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 + 2 * RCLike.re (star u * v) := by
  have h := RCLike.normSq_add v u
  simp only [RCLike.normSq_eq_def', RCLike.star_def] at h ⊢
  rw [add_comm u v, mul_comm ((starRingEnd 𝕜) u) v, add_comm (‖u‖ ^ 2) (‖v‖ ^ 2)]
  exact h

theorem energy_pair (Φ : Matrix m n 𝕜)
    (hΦ : ∀ j, ∑ i, ‖Φ i j‖ ^ 2 = 1) (z : n → 𝕜)
    (a b : n) (hab : a ≠ b) (hz : ∀ j, j ≠ a → j ≠ b → z j = 0) :
    (∑ i, ‖(Φ *ᵥ z) i‖ ^ 2) = ‖z a‖ ^ 2 + ‖z b‖ ^ 2 +
      2 * RCLike.re (star (z a) * z b * (Φᴴ * Φ) a b) := by
  have hrow (i : m) : (Φ *ᵥ z) i = Φ i a * z a + Φ i b * z b := by
    exact sum_eq_pair_of_eq_zero (fun j ↦ Φ i j * z j) a b hab
      (fun j hja hjb ↦ by rw [hz j hja hjb, mul_zero])
  have hcross (i : m) :
      star (Φ i a * z a) * (Φ i b * z b) =
        (star (z a) * z b) * (star (Φ i a) * Φ i b) := by
    rw [star_mul]
    ring
  simp_rw [hrow, norm_add_sq, norm_mul, mul_pow, hcross]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Finset.sum_mul, hΦ a, hΦ b, one_mul, one_mul, ← Finset.mul_sum,
    ← map_sum, ← Finset.mul_sum]
  rfl

theorem norm_sq_pair (z : n → 𝕜) (a b : n) (hab : a ≠ b)
    (hz : ∀ j, j ≠ a → j ≠ b → z j = 0) :
    (∑ j, ‖z j‖ ^ 2) = ‖z a‖ ^ 2 + ‖z b‖ ^ 2 := by
  exact sum_eq_pair_of_eq_zero (fun j ↦ ‖z j‖ ^ 2) a b hab
    (fun j hja hjb ↦ by rw [hz j hja hjb, norm_zero, zero_pow (by decide : 2 ≠ 0)])

theorem coherence_nonneg (Φ : Matrix m n 𝕜) : 0 ≤ ExplicitRIP.coherence Φ := by
  exact Real.iSup_nonneg fun _ ↦ norm_nonneg _

theorem gram_norm_le_coherence (Φ : Matrix m n 𝕜) (a b : n) (hab : a ≠ b) :
    ‖(Φᴴ * Φ) a b‖ ≤ ExplicitRIP.coherence Φ := by
  let f : {ij : n × n // ij.1 ≠ ij.2} → ℝ := fun p ↦ ‖(Φᴴ * Φ) p.val.1 p.val.2‖
  exact le_ciSup (Finite.bddAbove_range f) ⟨(a, b), hab⟩

theorem cross_term_bound (u v g : 𝕜) :
    |2 * RCLike.re (star u * v * g)| ≤ ‖g‖ * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  calc
    |2 * RCLike.re (star u * v * g)| = 2 * |RCLike.re (star u * v * g)| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ 2 * ‖star u * v * g‖ :=
      mul_le_mul_of_nonneg_left (RCLike.abs_re_le_norm _) (by norm_num)
    _ = ‖g‖ * (2 * ‖u‖ * ‖v‖) := by rw [norm_mul, norm_mul, norm_star]; ring
    _ ≤ ‖g‖ * (‖u‖ ^ 2 + ‖v‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (by nlinarith only [sq_nonneg (‖u‖ - ‖v‖)]) (norm_nonneg _)

end ExplicitRIP.RIPOneTwo
