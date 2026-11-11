/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.SrgScaling.Ratios

/-!
# Common-neighbor parameter asymptotics

The adjacency identities give the nonedge parameter and the error in the edge/nonedge ratio.
Source: [KM, Appendix A].
-/

public section

open Filter Asymptotics
open scoped Topology

namespace ExplicitRIP.SrgScaling

/-- The nonedge parameter normalized by its principal term. -/
theorem normalized_common (k c μ ν ε : ℝ) (hk : k ≠ 0) (hμ : 0 < μ) (hν : 0 < ν)
    (hc : (μ + ν) * c = k * ν * (1 - ε * μ)) :
    c / (k * ν / μ) = (1 - ε * μ) / (1 + ν / μ) := by
  have hsum : μ + ν ≠ 0 := (add_pos hμ hν).ne'
  have hc' : c = k * ν * (1 - ε * μ) / (μ + ν) := (eq_div_iff hsum).mpr (by
    simpa only [mul_comm c] using hc)
  rw [hc']
  field_simp [hk, hμ.ne', hν.ne', hsum]

/-- The nonedge common-neighbor parameter is equivalent to degree squared over order. -/
theorem common_equivalent (v k c μ ν ε : ℕ → ℝ)
    (hμ : ∀ j, 0 < μ j) (hν : ∀ j, 0 < ν j)
    (hε : ∀ j, ε j = 1 ∨ ε j = -1)
    (hμ0 : Tendsto μ atTop (𝓝 0))
    (hR0 : Tendsto (fun j => ν j / μ j) atTop (𝓝 0))
    (hK : (fun j => k j / v j) ~[atTop] (fun j => ν j / μ j))
    (hc : ∀ j, (μ j + ν j) * c j = k j * ν j * (1 - ε j * μ j)) :
    c ~[atTop] (fun j => k j ^ 2 / v j) := by
  have hk : ∀ᶠ j in atTop, k j ≠ 0 := by
    filter_upwards [hK.eventually_pos (Eventually.of_forall fun j => div_pos (hν j) (hμ j))]
      with j hj
    intro hzero
    simp only [hzero, zero_div] at hj
    exact hj.false
  have hεμ := bounded_mul_zero (signs_bounded ε hε) hμ0
  have hlim : Tendsto (fun j => (1 - ε j * μ j) / (1 + ν j / μ j)) atTop (𝓝 1) := by
    convert (tendsto_const_nhds.sub hεμ).div (tendsto_const_nhds.add hR0)
      (by norm_num : (1 : ℝ) + 0 ≠ 0) using 1
    norm_num
  have hC : c ~[atTop] (fun j => k j * ν j / μ j) := by
    apply isEquivalent_of_tendsto_one
    apply hlim.congr'
    filter_upwards [hk] with j hj
    exact (normalized_common (k j) (c j) (μ j) (ν j) (ε j) hj (hμ j) (hν j) (hc j)).symm
  have hscaled := (IsEquivalent.refl (u := k) (l := atTop)).mul hK
  have hs : (fun j => k j ^ 2 / v j) ~[atTop] (fun j => k j * ν j / μ j) := by
    have heq₁ : (k * (fun j => k j / v j)) =ᶠ[atTop] (fun j => k j ^ 2 / v j) :=
      Eventually.of_forall fun j => by dsimp; ring
    have heq₂ : (k * (fun j => ν j / μ j)) =ᶠ[atTop] (fun j => k j * ν j / μ j) :=
      Eventually.of_forall fun j => by dsimp; ring
    exact (hscaled.congr_left heq₁).congr_right heq₂
  exact hC.trans hs.symm

/-- The reciprocal of `k ν`, expressed in bounded normalized quantities. -/
theorem reciprocal_degree_angle (v k m μ ν : ℝ)
    (hv : v ≠ 0) (hm : m ≠ 0) (hμ : μ ≠ 0) (hν : ν ≠ 0) :
    1 / (k * ν) = ((m * μ ^ 3) * (m / v)) /
      (((k / v) / (ν / μ)) * (m * μ * ν) ^ 2) := by
  by_cases hk : k = 0
  · simp only [hk, zero_mul, zero_div, div_zero]
  · field_simp [hv, hm, hμ, hν, hk]


/-- The error in replacing `μ²/ν` by `m μ³`. -/
theorem squared_angle_error (m μ ν : ℝ) (hm : m ≠ 0) (hμ : μ ≠ 0) (hν : ν ≠ 0) :
    μ ^ 2 / ν - m * μ ^ 3 = (m * μ ^ 3) * (1 / (m * μ * ν) - 1) := by
  field_simp [hm, hμ, hν]

/-- Exact error formula for the ratio of common-neighbor parameters. -/
theorem common_ratio_error (k l c m μ ν ε : ℝ)
    (hk : k ≠ 0) (hμ : 0 < μ) (hν : 0 < ν) (hd : 1 - ε * μ ≠ 0)
    (hc : (μ + ν) * c = k * ν * (1 - ε * μ))
    (hl : (μ + ν) * l = (k - 1) * ν + ε * (k * μ ^ 2 - 1)) :
    l / c - (1 + ε * m * μ ^ 3) =
      (-1 / k + ε * (μ ^ 2 / ν - m * μ ^ 3 - 1 / (k * ν)) +
        (1 + ε * m * μ ^ 3) * (ε * μ)) / (1 - ε * μ) := by
  have hsum : μ + ν ≠ 0 := (add_pos hμ hν).ne'
  have hratio : l / c = ((k - 1) * ν + ε * (k * μ ^ 2 - 1)) /
      (k * ν * (1 - ε * μ)) := by
    rw [← hl, ← hc, mul_div_mul_left _ _ hsum]
  rw [hratio]
  field_simp [hk, hν.ne', hd]
  ring

/-- Vanishing errors in the ratio of the two common-neighbor parameters. -/
theorem common_ratio_limit (v k l c m μ ν ε : ℕ → ℝ)
    (hv : ∀ j, 0 < v j) (hm : ∀ j, 0 < m j)
    (hμ : ∀ j, 0 < μ j) (hν : ∀ j, 0 < ν j)
    (hε : ∀ j, ε j = 1 ∨ ε j = -1)
    (hmv : m =o[atTop] v)
    (hμ0 : Tendsto μ atTop (𝓝 0)) (hν0 : Tendsto ν atTop (𝓝 0))
    (hB : (fun j => m j * μ j ^ 3) =O[atTop] (fun _ => (1 : ℝ)))
    (hq : Tendsto (fun j => m j * μ j * ν j) atTop (𝓝 1))
    (hK : (fun j => k j / v j) ~[atTop] (fun j => ν j / μ j))
    (hc : ∀ᶠ j in atTop, (μ j + ν j) * c j = k j * ν j * (1 - ε j * μ j))
    (hl : ∀ᶠ j in atTop,
      (μ j + ν j) * l j = (k j - 1) * ν j + ε j * (k j * μ j ^ 2 - 1)) :
    Tendsto (fun j => l j / c j - (1 + ε j * m j * μ j ^ 3)) atTop (𝓝 0) := by
  have hs : Tendsto (fun j => (k j / v j) / (ν j / μ j)) atTop (𝓝 1) :=
    (isEquivalent_iff_tendsto_one (Eventually.of_forall fun j =>
      (div_pos (hν j) (hμ j)).ne')).mp hK
  have hinv : Tendsto (fun j => 1 / (k j * ν j)) atTop (𝓝 0) := by
    have hnum := bounded_mul_zero hB hmv.tendsto_div_nhds_zero
    have hh := hnum.div (hs.mul (hq.pow 2)) (by norm_num : (1 : ℝ) * 1 ^ 2 ≠ 0)
    simp only [one_pow, mul_one, zero_div] at hh
    apply hh.congr
    intro j
    exact (reciprocal_degree_angle (v j) (k j) (m j) (μ j) (ν j)
      (hv j).ne' (hm j).ne' (hμ j).ne' (hν j).ne').symm
  have hik : Tendsto (fun j => 1 / k j) atTop (𝓝 0) := by
    have hh := hν0.mul hinv
    simp only [zero_mul] at hh
    apply hh.congr
    intro j
    by_cases hk : k j = 0
    · simp only [hk, zero_mul, div_zero, mul_zero]
    · field_simp [hk, (hν j).ne']
  have herr : Tendsto (fun j => μ j ^ 2 / ν j - m j * μ j ^ 3) atTop (𝓝 0) := by
    have hh : Tendsto (fun j => 1 / (m j * μ j * ν j) - 1) atTop (𝓝 0) := by
      simpa only [one_div, inv_one, sub_self] using
        (hq.inv₀ one_ne_zero).sub (tendsto_const_nhds (x := (1 : ℝ)))
    exact (bounded_mul_zero hB hh).congr (fun j =>
      (squared_angle_error (m j) (μ j) (ν j) (hm j).ne' (hμ j).ne' (hν j).ne').symm)
  have hεO := signs_bounded ε hε
  have hεμ := bounded_mul_zero hεO hμ0
  have hεB : (fun j => ε j * (m j * μ j ^ 3)) =O[atTop] (fun _ => (1 : ℝ)) := by
    simpa only [Pi.mul_apply, mul_one] using hεO.mul hB
  have hOB : (fun j => 1 + ε j * m j * μ j ^ 3) =O[atTop] (fun _ => (1 : ℝ)) := by
    simpa only [Pi.add_apply, mul_assoc] using
      (isBigO_refl (fun _ : ℕ => (1 : ℝ)) atTop).add hεB
  have hlast := bounded_mul_zero hOB hεμ
  have hmid := bounded_mul_zero hεO (show
      Tendsto (fun j => μ j ^ 2 / ν j - m j * μ j ^ 3 - 1 / (k j * ν j))
        atTop (𝓝 0) from by simpa only [sub_zero] using herr.sub hinv)
  have hlim : Tendsto
      (fun j => (-1 / k j + ε j * (μ j ^ 2 / ν j - m j * μ j ^ 3 -
        1 / (k j * ν j)) + (1 + ε j * m j * μ j ^ 3) * (ε j * μ j)) /
        (1 - ε j * μ j)) atTop (𝓝 0) := by
    have hd : Tendsto (fun j => 1 - ε j * μ j) atTop (𝓝 1) := by
      simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hεμ
    simpa only [neg_zero, zero_add, inv_one, zero_mul, div_eq_mul_inv, neg_mul] using
      ((hik.neg.add hmid).add hlast).mul (hd.inv₀ one_ne_zero)
  apply hlim.congr'
  filter_upwards [hc, hl, hεμ.eventually_lt_const zero_lt_one,
    hK.eventually_pos (Eventually.of_forall fun j => div_pos (hν j) (hμ j))]
    with j hcj hlj hdj hkj
  have hk : k j ≠ 0 := by intro hz; simp only [hz, zero_div] at hkj; exact hkj.false
  exact (common_ratio_error (k j) (l j) (c j) (m j) (μ j) (ν j) (ε j) hk
    (hμ j) (hν j) (sub_pos.mpr hdj).ne' hcj hlj).symm

end ExplicitRIP.SrgScaling
