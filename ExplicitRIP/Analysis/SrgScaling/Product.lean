/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.SrgScaling.Powers

/-!
# The product of the two Gram angles

The moment identity implies `m μ ν → 1`, and hence the complementary angle has scale `m^(-2/3)`.
Source: [KM, Appendix A].
-/

public section

open Filter Asymptotics
open scoped Topology

namespace ExplicitRIP.SrgScaling

/-- Vanishing dimension ratio and divergent dimension imply vanishing reciprocal order. -/
theorem inverse_vertices_zero (m v : ℕ → ℝ) (hmpos : ∀ j, 0 < m j)
    (hm : Tendsto m atTop atTop) (hmv : m =o[atTop] v) :
    Tendsto (fun j => 1 / v j) atTop (𝓝 0) := by
  have h := hmv.tendsto_div_nhds_zero.mul hm.inv_tendsto_atTop
  simp only [zero_mul] at h
  apply h.congr
  intro j
  calc
    (m j / v j) * (m j)⁻¹ = (m j * (m j)⁻¹) / v j := by ring
    _ = 1 / v j := by rw [mul_inv_cancel₀ (hmpos j).ne']

/-- Normalizing the moment identity isolates the product `m μ ν`. -/
theorem normalized_product (v m μ ν ε : ℝ) (hv : v ≠ 0) (hm : m ≠ 0)
    (hd : 1 - 1 / v ≠ 0)
    (h : v / m - 1 = (v - 1) * μ * ν - ε * (μ - ν)) :
    m * μ * ν = (1 - m / v + (m / v) * (ε * (μ - ν))) / (1 - 1 / v) := by
  apply (eq_div_iff hd).2
  field_simp [hv, hm] at h ⊢
  nlinarith only [h]

/-- The angle product is asymptotic to reciprocal dimension. -/
theorem angle_product_limit (v m μ ν ε : ℕ → ℝ)
    (hvpos : ∀ j, 0 < v j) (hmpos : ∀ j, 0 < m j)
    (hνpos : ∀ j, 0 < ν j) (hνμ : ∀ j, ν j < μ j)
    (hε : ∀ j, ε j = 1 ∨ ε j = -1)
    (hm : Tendsto m atTop atTop) (hmv : m =o[atTop] v)
    (hμ : μ =Θ[atTop] (fun j => m j ^ (-(1 / 3 : ℝ))))
    (hid : ∀ j, v j / m j - 1 = (v j - 1) * μ j * ν j - ε j * (μ j - ν j)) :
    Tendsto (fun j => m j * μ j * ν j) atTop (𝓝 1) := by
  have hμ0 := coherence_zero m μ hm hμ
  have hν0 : Tendsto ν atTop (𝓝 0) :=
    squeeze_zero (fun j => (hνpos j).le) (fun j => (hνμ j).le) hμ0
  have hdiff : Tendsto (fun j => ε j * (μ j - ν j)) atTop (𝓝 0) :=
    bounded_mul_zero (signs_bounded ε hε) (by simpa only [sub_zero] using hμ0.sub hν0)
  have hiV := inverse_vertices_zero m v hmpos hm hmv
  have hlim : Tendsto
      (fun j => (1 - m j / v j + (m j / v j) * (ε j * (μ j - ν j))) /
        (1 - 1 / v j)) atTop (𝓝 1) := by
    convert ((tendsto_const_nhds.sub hmv.tendsto_div_nhds_zero).add
      (hmv.tendsto_div_nhds_zero.mul hdiff)).div
      (tendsto_const_nhds.sub hiV) (by norm_num : (1 : ℝ) - 0 ≠ 0) using 1
    norm_num
  apply hlim.congr'
  filter_upwards [hiV.eventually_lt_const zero_lt_one] with j hj
  exact (normalized_product (v j) (m j) (μ j) (ν j) (ε j) (hvpos j).ne'
    (hmpos j).ne' (sub_pos.mpr hj).ne' (hid j)).symm

/-- The complementary angle is equivalent to reciprocal dimension divided by coherence. -/
theorem angle_equivalent (v m μ ν ε : ℕ → ℝ)
    (hvpos : ∀ j, 0 < v j) (hmpos : ∀ j, 0 < m j)
    (hνpos : ∀ j, 0 < ν j) (hνμ : ∀ j, ν j < μ j)
    (hε : ∀ j, ε j = 1 ∨ ε j = -1)
    (hm : Tendsto m atTop atTop) (hmv : m =o[atTop] v)
    (hμ : μ =Θ[atTop] (fun j => m j ^ (-(1 / 3 : ℝ))))
    (hid : ∀ j, v j / m j - 1 = (v j - 1) * μ j * ν j - ε j * (μ j - ν j)) :
    ν ~[atTop] (fun j => 1 / (m j * μ j)) := by
  apply isEquivalent_of_tendsto_one
  have hlim := angle_product_limit v m μ ν ε hvpos hmpos hνpos hνμ hε hm hmv hμ hid
  apply hlim.congr
  intro j
  change m j * μ j * ν j = ν j / (1 / (m j * μ j))
  rw [div_div_eq_mul_div, div_one]
  ring

end ExplicitRIP.SrgScaling
