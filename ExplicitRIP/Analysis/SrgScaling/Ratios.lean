/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.SrgScaling.Product

/-!
# Degree and complementary-angle ratios

Normalization of the row-sum identity gives the degree scaling in [KM, Appendix A].
-/

public section

open Filter Asymptotics
open scoped Topology

namespace ExplicitRIP.SrgScaling

/-- Dividing the angle equivalent by coherence gives the reciprocal quadratic scale. -/
theorem angle_ratio_equivalent (m μ ν : ℕ → ℝ) (hm : ∀ j, 0 < m j)
    (hμ : ∀ j, 0 < μ j) (hν : ν ~[atTop] (fun j => 1 / (m j * μ j))) :
    (fun j => ν j / μ j) ~[atTop] (fun j => 1 / (m j * μ j ^ 2)) := by
  have h := hν.div (IsEquivalent.refl (u := μ) (l := atTop))
  apply h.congr_right
  exact Eventually.of_forall fun j => by
    dsimp
    field_simp [(hm j).ne', (hμ j).ne']

/-- The normalized degree ratio is an exact quotient with numerator and denominator near one. -/
theorem normalized_degree (v k μ ν ε : ℝ) (hv : 0 < v) (hμ : 0 < μ) (hν : 0 < ν)
    (hrow : k * (μ + ν) = (v - 1) * ν - ε) :
    (k / v) / (ν / μ) =
      (1 - 1 / v - ε * (1 / (v * ν))) / (1 + ν / μ) := by
  have hd : 1 + ν / μ ≠ 0 := (by positivity : 0 < 1 + ν / μ).ne'
  apply (eq_div_iff hd).2
  field_simp [hv.ne', hμ.ne', hν.ne']
  nlinarith only [hrow]

/-- A divergent normalized product forces reciprocal `v ν` to vanish. -/
theorem inverse_vertex_angle_zero (v m μ ν : ℕ → ℝ)
    (hvpos : ∀ j, 0 < v j) (hmpos : ∀ j, 0 < m j)
    (hμpos : ∀ j, 0 < μ j) (hνpos : ∀ j, 0 < ν j)
    (hmv : m =o[atTop] v) (hμ0 : Tendsto μ atTop (𝓝 0))
    (hq : Tendsto (fun j => m j * μ j * ν j) atTop (𝓝 1)) :
    Tendsto (fun j => 1 / (v j * ν j)) atTop (𝓝 0) := by
  have h := (hmv.tendsto_div_nhds_zero.mul hμ0).div hq one_ne_zero
  simp only [zero_mul, zero_div] at h
  apply h.congr
  intro j
  change (m j / v j * μ j) / (m j * μ j * ν j) = 1 / (v j * ν j)
  field_simp [(hvpos j).ne', (hmpos j).ne', (hμpos j).ne', (hνpos j).ne']

/-- The normalized degree and angle ratios both tend to one. -/
theorem degree_equivalent (v k m μ ν ε : ℕ → ℝ)
    (hvpos : ∀ j, 0 < v j) (hmpos : ∀ j, 0 < m j)
    (hνpos : ∀ j, 0 < ν j) (hνμ : ∀ j, ν j < μ j)
    (hε : ∀ j, ε j = 1 ∨ ε j = -1)
    (hm : Tendsto m atTop atTop) (hmv : m =o[atTop] v)
    (hμ : μ =Θ[atTop] (fun j => m j ^ (-(1 / 3 : ℝ))))
    (hq : Tendsto (fun j => m j * μ j * ν j) atTop (𝓝 1))
    (hν : ν ~[atTop] (fun j => 1 / (m j * μ j)))
    (hrow : ∀ j, k j * (μ j + ν j) = (v j - 1) * ν j - ε j) :
    (fun j => k j / v j) ~[atTop] (fun j => ν j / μ j) := by
  have hμpos : ∀ j, 0 < μ j := fun j => (hνpos j).trans (hνμ j)
  have hμ0 := coherence_zero m μ hm hμ
  have hR := angle_ratio_equivalent m μ ν hmpos hμpos hν
  have hR0 : Tendsto (fun j => ν j / μ j) atTop (𝓝 0) :=
    (hR.isTheta.trans (quadratic_reciprocal_isTheta m μ hmpos hμ)).tendsto_zero_iff.mpr
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp hm)
  have hiV := inverse_vertices_zero m v hmpos hm hmv
  have hiVν := inverse_vertex_angle_zero v m μ ν hvpos hmpos hμpos hνpos hmv hμ0 hq
  have hεi := bounded_mul_zero (signs_bounded ε hε) hiVν
  have hlim : Tendsto
      (fun j => (1 - 1 / v j - ε j * (1 / (v j * ν j))) / (1 + ν j / μ j))
      atTop (𝓝 1) := by
    convert ((tendsto_const_nhds.sub hiV).sub hεi).div
      (tendsto_const_nhds.add hR0) (by norm_num : (1 : ℝ) + 0 ≠ 0) using 1
    norm_num
  apply isEquivalent_of_tendsto_one
  apply hlim.congr
  intro j
  exact (normalized_degree (v j) (k j) (μ j) (ν j) (ε j) (hvpos j) (hμpos j)
    (hνpos j) (hrow j)).symm

end ExplicitRIP.SrgScaling
