/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.SrgScaling.Common

/-!
# Vanishing edge common-neighbor parameter

The edge/nonedge ratio vanishes precisely for the negative sign and the sharp cube-root scale.
Source: [KM, Appendix A].
-/

public section

open Filter Asymptotics
open scoped Topology

namespace ExplicitRIP.SrgScaling

/-- Normalizing coherence by its reciprocal cube-root scale identifies the cubic parameter. -/
theorem normalized_coherence_cube (m μ : ℝ) (hm : 0 < m) :
    (μ / m ^ (-(1 / 3 : ℝ))) ^ 3 = m * μ ^ 3 := by
  rw [div_pow]
  apply (div_eq_iff (pow_ne_zero _ (Real.rpow_pos_of_pos hm _).ne')).2
  have hh := congrArg (fun t : ℝ => μ ^ 3 * t) (scale_cube hm)
  nlinarith only [hh]

/-- The cubic parameter tends to one precisely when coherence is equivalent to its scale. -/
theorem cubic_limit_iff (m μ : ℕ → ℝ) (hm : ∀ j, 0 < m j) (hμ : ∀ j, 0 < μ j) :
    Tendsto (fun j => m j * μ j ^ 3) atTop (𝓝 1) ↔
      μ ~[atTop] (fun j => m j ^ (-(1 / 3 : ℝ))) := by
  have ht : ∀ᶠ j in atTop, m j ^ (-(1 / 3 : ℝ)) ≠ 0 :=
    Eventually.of_forall fun j => (Real.rpow_pos_of_pos (hm j) _).ne'
  rw [isEquivalent_iff_tendsto_one ht]
  constructor
  · intro hb
    have hroot := hb.rpow_const (p := (1 / 3 : ℝ)) (Or.inl one_ne_zero)
    simp only [Real.one_rpow] at hroot
    apply hroot.congr
    intro j
    dsimp
    rw [← normalized_coherence_cube (m j) (μ j) (hm j),
      ← Real.rpow_natCast_mul (div_nonneg (hμ j).le (Real.rpow_nonneg (hm j).le _))]
    norm_num
  · intro hratio
    have hcube := hratio.pow 3
    simp only [one_pow] at hcube
    exact hcube.congr fun j => normalized_coherence_cube (m j) (μ j) (hm j)

/-- With a vanishing error, cancellation of the leading positive term fixes the sign. -/
theorem vanishing_ratio_iff (l c m μ ε : ℕ → ℝ)
    (hm : ∀ j, 0 < m j) (hμ : ∀ j, 0 < μ j)
    (hε : ∀ j, ε j = 1 ∨ ε j = -1)
    (hc : ∀ᶠ j in atTop, c j ≠ 0)
    (herr : Tendsto (fun j => l j / c j - (1 + ε j * m j * μ j ^ 3)) atTop (𝓝 0)) :
    l =o[atTop] c ↔ (∀ᶠ j in atTop, ε j = -1) ∧
      μ ~[atTop] (fun j => m j ^ (-(1 / 3 : ℝ))) := by
  have hzero : ∀ᶠ j in atTop, c j = 0 → l j = 0 := hc.mono fun _ hj hz => (hj hz).elim
  rw [isLittleO_iff_tendsto' hzero]
  constructor
  · intro hratio
    have hmain : Tendsto (fun j => 1 + ε j * m j * μ j ^ 3) atTop (𝓝 0) := by
      simpa only [sub_zero, sub_sub_cancel] using hratio.sub herr
    have hneg : ∀ᶠ j in atTop, ε j = -1 := by
      filter_upwards [hmain.eventually_lt_const zero_lt_one] with j hj
      rcases hε j with he | he
      · have hb : 0 < m j * μ j ^ 3 := mul_pos (hm j) (pow_pos (hμ j) 3)
        rw [he, one_mul] at hj
        linarith only [hj, hb]
      · exact he
    refine ⟨hneg, (cubic_limit_iff m μ hm hμ).mp ?_⟩
    have hsub : Tendsto (fun j => 1 - m j * μ j ^ 3) atTop (𝓝 0) := by
      apply hmain.congr'
      filter_upwards [hneg] with j hj
      simp only [hj, neg_mul, one_mul, sub_eq_add_neg]
    simpa only [sub_zero, sub_sub_cancel] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub hsub
  · rintro ⟨hneg, hscale⟩
    have hb := (cubic_limit_iff m μ hm hμ).mpr hscale
    have hmain : Tendsto (fun j => 1 + ε j * m j * μ j ^ 3) atTop (𝓝 0) := by
      have hh := (tendsto_const_nhds (x := (1 : ℝ))).sub hb
      simp only [sub_self] at hh
      apply hh.congr'
      filter_upwards [hneg] with j hj
      simp only [hj, neg_mul, one_mul, sub_eq_add_neg]
    simpa only [add_zero, sub_add_cancel] using herr.add hmain

/-- In the sharp coherence regime the complementary angle has the sharp `-2/3` equivalent. -/
theorem sharp_complementary_angle (m μ ν : ℕ → ℝ) (hm : ∀ j, 0 < m j)
    (hν : ν ~[atTop] (fun j => 1 / (m j * μ j)))
    (hμ : μ ~[atTop] (fun j => m j ^ (-(1 / 3 : ℝ)))) :
    ν ~[atTop] (fun j => m j ^ (-(2 / 3 : ℝ))) := by
  have h := (IsEquivalent.refl (u := (fun _ : ℕ => (1 : ℝ))) (l := atTop)).div
    ((IsEquivalent.refl (u := m) (l := atTop)).mul hμ)
  have hr : (fun j => 1 / (m j * μ j)) ~[atTop]
      (fun j => m j ^ (-(2 / 3 : ℝ))) := by
    exact h.congr_right (Eventually.of_forall fun j => scale_reciprocal (hm j))
  exact hν.trans hr

end ExplicitRIP.SrgScaling
