/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.RIPOneTwo.Basic
public import ExplicitRIP.Frozen.Defs.RIPConstant
import ExplicitRIP.Frozen.RIPConstantCharacterization

/-!
# The first two restricted isometry constants

The least-distortion characterization and one- and two-column energy formulas prove the result,
including empty column index types. A unit phase attains the two-column distortion.

Source: [KM, Section 2.2].
-/

public section

open scoped Matrix

namespace ExplicitRIP.RIPOneTwo

variable {𝕜 : Type} [RCLike 𝕜] {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq n]

omit [DecidableEq n] in
theorem energy_one_sparse (Φ : Matrix m n 𝕜)
    (hΦ : ∀ j, ∑ i, ‖Φ i j‖ ^ 2 = 1) (z : n → 𝕜)
    (hz : (Function.support z).ncard ≤ 1) :
    (∑ i, ‖(Φ *ᵥ z) i‖ ^ 2) = ∑ j, ‖z j‖ ^ 2 := by
  rcases support_cases_one z hz with rfl | ⟨a, ha⟩
  · simp only [Matrix.mulVec_zero, Pi.zero_apply, norm_zero,
      zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero]
  · exact energy_single Φ hΦ z a ha

theorem ripConstant_one_eq_zero (Φ : Matrix m n 𝕜)
    (hΦ : ∀ j, ∑ i, ‖Φ i j‖ ^ 2 = 1) : ExplicitRIP.ripConstant Φ 1 = 0 := by
  have hleast := ExplicitRIP.ripConstant_isLeast Φ 1
  refine le_antisymm (hleast.2 ?_) hleast.1.1
  refine ⟨le_rfl, fun z hz ↦ ?_⟩
  rw [energy_one_sparse Φ hΦ z hz]
  simp only [sub_zero, add_zero, one_mul, le_refl, and_self]

theorem ripConstant_two_le_coherence (Φ : Matrix m n 𝕜)
    (hΦ : ∀ j, ∑ i, ‖Φ i j‖ ^ 2 = 1) :
    ExplicitRIP.ripConstant Φ 2 ≤ ExplicitRIP.coherence Φ := by
  apply (ExplicitRIP.ripConstant_isLeast Φ 2).2
  refine ⟨coherence_nonneg Φ, fun z hz ↦ ?_⟩
  rcases support_cases_two z hz with rfl | ⟨a, ha⟩ | ⟨a, b, hab, hzab⟩
  · simp only [Matrix.mulVec_zero, Pi.zero_apply, norm_zero,
      zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, mul_zero, le_refl, and_self]
  · rw [energy_single Φ hΦ z a ha]
    have hm := mul_nonneg (coherence_nonneg Φ)
      (Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) ↦ sq_nonneg ‖z j‖)
    constructor <;> nlinarith only [hm]
  · rw [energy_pair Φ hΦ z a b hab hzab, norm_sq_pair z a b hab hzab]
    have hc := (cross_term_bound (z a) (z b) ((Φᴴ * Φ) a b)).trans
      (mul_le_mul_of_nonneg_right (gram_norm_le_coherence Φ a b hab)
        (add_nonneg (sq_nonneg ‖z a‖) (sq_nonneg ‖z b‖)))
    rcases abs_le.mp hc with ⟨hlo, hhi⟩
    constructor <;> nlinarith only [hlo, hhi]

theorem phase_norm (g : 𝕜) (hg : g ≠ 0) : ‖-star g / (‖g‖ : 𝕜)‖ = 1 := by
  rw [norm_div, norm_neg, norm_star, RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.mpr hg)]

theorem phase_mul (g : 𝕜) (hg : g ≠ 0) :
    (-star g / (‖g‖ : 𝕜)) * g = -(‖g‖ : 𝕜) := by
  have hn : (‖g‖ : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hg)
  rw [div_mul_eq_mul_div, neg_mul, RCLike.star_def, RCLike.conj_mul]
  field_simp [hn]

/-- Every off-diagonal Gram modulus is attained as a two-sparse distortion. -/
theorem gram_norm_le_ripConstant_two (Φ : Matrix m n 𝕜)
    (hΦ : ∀ j, ∑ i, ‖Φ i j‖ ^ 2 = 1) (a b : n) (hab : a ≠ b) :
    ‖(Φᴴ * Φ) a b‖ ≤ ExplicitRIP.ripConstant Φ 2 := by
  have hleast := ExplicitRIP.ripConstant_isLeast Φ 2
  by_cases hg : (Φᴴ * Φ) a b = 0
  · simpa only [hg, norm_zero] using hleast.1.1
  · let g := (Φᴴ * Φ) a b
    let t : 𝕜 := -star g / (‖g‖ : 𝕜)
    let z : n → 𝕜 := fun j ↦ if j = a then 1 else if j = b then t else 0
    have hza : z a = 1 := by simp only [z, ite_true]
    have hzb : z b = t := by simp only [z, hab.symm, ite_false, ite_true]
    have hzab : ∀ j, j ≠ a → j ≠ b → z j = 0 := by
      intro j hja hjb
      simp only [z, hja, hjb, ite_false]
    have hs : Function.support z ⊆ ({a, b} : Set n) := by
      intro j hj
      by_contra hjab
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hjab
      exact hj (hzab j hjab.1 hjab.2)
    have hcard : (Function.support z).ncard ≤ 2 := by
      exact (Set.ncard_le_ncard hs).trans (by rw [Set.ncard_pair hab])
    have ht : ‖t‖ = 1 := phase_norm g hg
    have htg : t * g = -(‖g‖ : 𝕜) := phase_mul g hg
    have hinput : (∑ j, ‖z j‖ ^ 2) = 2 := by
      rw [norm_sq_pair z a b hab hzab, hza, hzb, ht, norm_one]
      norm_num
    have houtput : (∑ i, ‖(Φ *ᵥ z) i‖ ^ 2) = 2 - 2 * ‖g‖ := by
      rw [energy_pair Φ hΦ z a b hab hzab, hza, hzb, ht, norm_one]
      change 1 ^ 2 + 1 ^ 2 + 2 * RCLike.re (star (1 : 𝕜) * t * g) = _
      rw [star_one, one_mul, htg, map_neg, RCLike.ofReal_re]
      ring
    have hlo := (hleast.1.2 z hcard).1
    rw [hinput, houtput] at hlo
    change ‖g‖ ≤ ExplicitRIP.ripConstant Φ 2
    linarith only [hlo]

theorem coherence_le_ripConstant_two (Φ : Matrix m n 𝕜)
    (hΦ : ∀ j, ∑ i, ‖Φ i j‖ ^ 2 = 1) :
    ExplicitRIP.coherence Φ ≤ ExplicitRIP.ripConstant Φ 2 := by
  apply Real.iSup_le
  · intro p
    exact gram_norm_le_ripConstant_two Φ hΦ p.val.1 p.val.2 p.property
  · exact (ExplicitRIP.ripConstant_isLeast Φ 2).1.1

theorem ripConstant_one_two (Φ : Matrix m n 𝕜)
    (hΦ : ∀ j, ∑ i, ‖Φ i j‖ ^ 2 = 1) :
    ExplicitRIP.ripConstant Φ 1 = 0 ∧
      ExplicitRIP.ripConstant Φ 2 = ExplicitRIP.coherence Φ := by
  exact ⟨ripConstant_one_eq_zero Φ hΦ,
    le_antisymm (ripConstant_two_le_coherence Φ hΦ) (coherence_le_ripConstant_two Φ hΦ)⟩

end ExplicitRIP.RIPOneTwo
