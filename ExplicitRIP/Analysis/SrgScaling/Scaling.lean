/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.SrgScaling.Vanishing

/-!
# Scaling laws from the scalar graph identities

This real-analysis theorem assembles the asymptotic consequences of the moment and adjacency
identities. Source: [KM, Appendix A].
-/

public section

open Filter Asymptotics
open scoped Topology

namespace ExplicitRIP.SrgScaling

/-- The scalar moment and common-neighbor identities imply all the scaling laws. -/
theorem scaling_laws (v k l c m μ ν ε : ℕ → ℝ)
    (hvpos : ∀ j, 0 < v j) (hmpos : ∀ j, 0 < m j)
    (hνpos : ∀ j, 0 < ν j) (hνμ : ∀ j, ν j < μ j)
    (hε : ∀ j, ε j = 1 ∨ ε j = -1)
    (hm : Tendsto m atTop atTop) (hmv : m =o[atTop] v)
    (hμ : μ =Θ[atTop] (fun j => m j ^ (-(1 / 3 : ℝ))))
    (hid : ∀ j, v j / m j - 1 = (v j - 1) * μ j * ν j - ε j * (μ j - ν j))
    (hrow : ∀ j, k j * (μ j + ν j) = (v j - 1) * ν j - ε j)
    (hc : ∀ j, (μ j + ν j) * c j = k j * ν j * (1 - ε j * μ j))
    (hl : ∀ j, (μ j + ν j) * l j =
      (k j - 1) * ν j + ε j * (k j * μ j ^ 2 - 1)) :
    ν =Θ[atTop] (fun j => m j ^ (-(2 / 3 : ℝ))) ∧
      (fun j => k j / v j) ~[atTop] (fun j => ν j / μ j) ∧
      (fun j => ν j / μ j) ~[atTop] (fun j => 1 / (m j * μ j ^ 2)) ∧
      (fun j => 1 / (m j * μ j ^ 2)) =Θ[atTop] (fun j => m j ^ (-(1 / 3 : ℝ))) ∧
      c ~[atTop] (fun j => k j ^ 2 / v j) ∧
      Tendsto (fun j => l j / c j - (1 + ε j * m j * μ j ^ 3)) atTop (𝓝 0) ∧
      (l =o[atTop] c ↔ (∀ᶠ j in atTop, ε j = -1) ∧
        μ ~[atTop] (fun j => m j ^ (-(1 / 3 : ℝ)))) ∧
      (l =o[atTop] c → ν ~[atTop] (fun j => m j ^ (-(2 / 3 : ℝ)))) := by
  have hμpos : ∀ j, 0 < μ j := fun j => (hνpos j).trans (hνμ j)
  have hq := angle_product_limit v m μ ν ε hvpos hmpos hνpos hνμ hε hm hmv hμ hid
  have hν := angle_equivalent v m μ ν ε hvpos hmpos hνpos hνμ hε hm hmv hμ hid
  have hνT := hν.isTheta.trans (linear_reciprocal_isTheta m μ hmpos hμ)
  have hR := angle_ratio_equivalent m μ ν hmpos hμpos hν
  have hQT := quadratic_reciprocal_isTheta m μ hmpos hμ
  have hK := degree_equivalent v k m μ ν ε hvpos hmpos hνpos hνμ hε hm hmv hμ hq hν hrow
  have hμ0 := coherence_zero m μ hm hμ
  have hν0 : Tendsto ν atTop (𝓝 0) :=
    squeeze_zero (fun j => (hνpos j).le) (fun j => (hνμ j).le) hμ0
  have hR0 : Tendsto (fun j => ν j / μ j) atTop (𝓝 0) :=
    (hR.isTheta.trans hQT).tendsto_zero_iff.mpr
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp hm)
  have hC := common_equivalent v k c μ ν ε hμpos hνpos hε hμ0 hR0 hK hc
  have hD := common_ratio_limit v k l c m μ ν ε hvpos hmpos hμpos hνpos hε hmv hμ0 hν0
    (cubic_isTheta m μ hmpos hμ).1 hq hK (Eventually.of_forall hc) (Eventually.of_forall hl)
  have hcne : ∀ᶠ j in atTop, c j ≠ 0 := by
    have hkpos := hK.eventually_pos
      (Eventually.of_forall fun j => div_pos (hνpos j) (hμpos j))
    have hk2pos : ∀ᶠ j in atTop, 0 < k j ^ 2 / v j := by
      filter_upwards [hkpos] with j hj
      have hk : k j ≠ 0 := by intro hz; simp only [hz, zero_div] at hj; exact hj.false
      exact div_pos (sq_pos_of_ne_zero hk) (hvpos j)
    exact (hC.eventually_pos hk2pos).mono fun _ hj => hj.ne'
  have hcriterion := vanishing_ratio_iff l c m μ ε hmpos hμpos hε hcne hD
  refine ⟨hνT, hK, hR, hQT, hC, hD, hcriterion, ?_⟩
  intro hsmall
  exact sharp_complementary_angle m μ ν hmpos hν (hcriterion.mp hsmall).2

end ExplicitRIP.SrgScaling
