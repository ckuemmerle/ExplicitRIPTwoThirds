/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.ConstructionBarrier.Finite

/-!
# Asymptotic construction barrier

Vanishing dimension ratio forces divergence of the prime parameter. Uniform algebraic bounds
then give both little-o assertions and the bounded-RIP assertion for subframes of the host frame
with parameters [KM, (13)]. The vanishing-distortion conclusion is the host-frame case of
[KM, Proposition 10].
-/

public section

open Filter Asymptotics
open scoped Topology Matrix

namespace ExplicitRIP.Actbar

variable (p : ℕ → ℕ) [∀ j, Fact (p j).Prime] [∀ j, Fact (p j % 4 = 3)]
  (Γ : ∀ j, Finset (ZMod (p j) × ZMod (p j) × ZMod (p j) × ZMod (p j)))

omit [∀ j, Fact (p j % 4 = 3)] in
theorem reciprocal_ratio_tendsto_atTop
    (hΓ : ∀ᶠ j in atTop, (Γ j).Nonempty)
    (hratio : Tendsto (fun j => (rowCount (p j) : ℝ) / (Γ j).card) atTop (𝓝 0)) :
    Tendsto (fun j => ((Γ j).card : ℝ) / rowCount (p j)) atTop atTop := by
  have hpos : ∀ᶠ j in atTop, 0 < (rowCount (p j) : ℝ) / (Γ j).card := by
    filter_upwards [hΓ] with j hj
    exact div_pos (Nat.cast_pos.mpr (rowCount_pos (Fact.out : (p j).Prime).two_le))
      (Nat.cast_pos.mpr hj.card_pos)
  have h := (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).comp (tendsto_nhdsWithin_iff.mpr ⟨hratio, hpos⟩)
  simpa only [Function.comp_def, inv_div] using h

omit [∀ j, Fact (p j % 4 = 3)] in
/-- Parameter divergence follows from `n/m ≤ 2p` and `m/n → 0`. -/
theorem parameter_tendsto_atTop
    (hΓ : ∀ᶠ j in atTop, (Γ j).Nonempty)
    (hratio : Tendsto (fun j => (rowCount (p j) : ℝ) / (Γ j).card) atTop (𝓝 0)) :
    Tendsto (fun j => (p j : ℝ)) atTop atTop := by
  have h := tendsto_atTop_mono (fun j => selected_ratio_le_two_mul (p j) (Γ j))
    (reciprocal_ratio_tendsto_atTop p Γ hΓ hratio)
  exact (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).mp h

omit [∀ j, Fact (p j % 4 = 3)] in
theorem parameter_sq_isBigO_rows :
    (fun j => (p j : ℝ) ^ 2) =O[atTop]
      (fun j => (rowCount (p j) : ℝ) ^ (2 / 3 : ℝ)) := by
  apply IsBigO.of_bound 4
  apply Eventually.of_forall
  intro j
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  exact sq_le_four_rowCount_rpow (Fact.out : (p j).Prime).two_le

variable (Φ : ∀ j, Matrix (Fin (rowCount (p j))) (Γ j) ℝ)

theorem sparsity_bound_eventually
    (hΓ : ∀ᶠ j in atTop, (Γ j).Nonempty)
    (hGram : ∀ j, (Φ j)ᵀ * Φ j = (hermitianHostGram ℝ (p j)).submatrix Subtype.val Subtype.val)
    (k : ℕ → ℕ)
    (hratio : Tendsto (fun j => (rowCount (p j) : ℝ) / (Γ j).card) atTop (𝓝 0))
    (hδ : (fun j => ripConstant (Φ j) (k j)) =O[atTop] (fun _ => (1 : ℝ))) :
    ∀ᶠ j in atTop, (k j : ℝ) ≤ 1 + 4 * ripConstant (Φ j) (k j) ^ 2 * (p j : ℝ) ^ 2 := by
  obtain ⟨C, hC, hCb⟩ := isBigO_iff'.mp hδ
  have ht := (reciprocal_ratio_tendsto_atTop p Γ hΓ hratio).eventually_gt_atTop (C ^ 2 + 2)
  filter_upwards [hΓ, hCb, ht] with j hj hCj htj
  have hbound : ripConstant (Φ j) (k j) ^ 2 ≤ C ^ 2 := by
    have hd : ripConstant (Φ j) (k j) ≤ C := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (rip_nonneg _ _), norm_one, mul_one] using hCj
    exact (sq_le_sq₀ (rip_nonneg _ _) hC.le).mpr hd
  exact finite_barrier (p j) (Γ j) (Φ j) hj (hGram j) (k j) (by linarith only [hbound, htj])

theorem sparsity_isBigO_sq
    (hΓ : ∀ᶠ j in atTop, (Γ j).Nonempty)
    (hGram : ∀ j, (Φ j)ᵀ * Φ j = (hermitianHostGram ℝ (p j)).submatrix Subtype.val Subtype.val)
    (k : ℕ → ℕ)
    (hratio : Tendsto (fun j => (rowCount (p j) : ℝ) / (Γ j).card) atTop (𝓝 0))
    (hδ : (fun j => ripConstant (Φ j) (k j)) =O[atTop] (fun _ => (1 : ℝ))) :
    (fun j => (k j : ℝ)) =O[atTop] (fun j => (p j : ℝ) ^ 2) := by
  obtain ⟨C, hC, hCb⟩ := isBigO_iff'.mp hδ
  apply IsBigO.of_bound (1 + 4 * C ^ 2)
  filter_upwards [sparsity_bound_eventually p Γ Φ hΓ hGram k hratio hδ, hCb] with j hj hCj
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]
  have hd : ripConstant (Φ j) (k j) ≤ C := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (rip_nonneg _ _), norm_one, mul_one] using hCj
  have hds := (sq_le_sq₀ (rip_nonneg _ _) hC.le).mpr hd
  have hp : (2 : ℝ) ≤ p j := by exact_mod_cast (Fact.out : (p j).Prime).two_le
  have hm := mul_le_mul_of_nonneg_right hds (sq_nonneg (p j : ℝ))
  nlinarith only [hj, hm, hp, sq_nonneg ((p j : ℝ) - 1)]

theorem sparsity_isLittleO_sq
    (hΓ : ∀ᶠ j in atTop, (Γ j).Nonempty)
    (hGram : ∀ j, (Φ j)ᵀ * Φ j = (hermitianHostGram ℝ (p j)).submatrix Subtype.val Subtype.val)
    (k : ℕ → ℕ)
    (hratio : Tendsto (fun j => (rowCount (p j) : ℝ) / (Γ j).card) atTop (𝓝 0))
    (hδ : Tendsto (fun j => ripConstant (Φ j) (k j)) atTop (𝓝 0)) :
    (fun j => (k j : ℝ)) =o[atTop] (fun j => (p j : ℝ) ^ 2) := by
  have hp := parameter_tendsto_atTop p Γ hΓ hratio
  have hi : Tendsto (fun j => ((p j : ℝ) ^ 2)⁻¹) atTop (𝓝 0) :=
    (tendsto_pow_atTop (α := ℝ) (by decide : 2 ≠ 0) |>.comp hp).inv_tendsto_atTop
  have hmajor : Tendsto (fun j => ((p j : ℝ) ^ 2)⁻¹ + 4 * ripConstant (Φ j) (k j) ^ 2)
      atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] using
      hi.add ((hδ.pow 2).const_mul 4)
  have hquot : Tendsto (fun j => (k j : ℝ) / (p j : ℝ) ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun j => by positivity)) ?_ hmajor
    filter_upwards [sparsity_bound_eventually p Γ Φ hΓ hGram k hratio (hδ.isBigO_one ℝ)] with j hj
    have hpp : (0 : ℝ) < p j := Nat.cast_pos.mpr (Fact.out : (p j).Prime).pos
    apply (div_le_iff₀ (sq_pos_of_pos hpp)).2
    have heq : (((p j : ℝ) ^ 2)⁻¹ + 4 * ripConstant (Φ j) (k j) ^ 2) * (p j : ℝ) ^ 2 =
        1 + 4 * ripConstant (Φ j) (k j) ^ 2 * (p j : ℝ) ^ 2 := by
      rw [add_mul, inv_mul_cancel₀ (pow_ne_zero _ hpp.ne')]
    rwa [heq]
  apply isLittleO_of_tendsto (fun j hj => ?_) hquot
  have hp0 : (p j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : (p j).Prime).ne_zero
  exact False.elim ((pow_ne_zero 2 hp0) hj)

end ExplicitRIP.Actbar
