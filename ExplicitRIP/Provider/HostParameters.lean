/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Contact.HostFrame
public import ExplicitRIP.Contact.HostFrame.ScaleAsymptotics

/-!
# The strongly regular parameters of the host graph

Source: [KM, Section 3, the parameters of VO₄⁻(p) before (13)].

The affine polar graph has strongly regular parameters `(p⁴, (p - 1)(p² + 1), p - 2, p(p - 1))`.
As `p → ∞` through primes `p ≡ 3 (mod 4)`, these are `∼ (p⁴, p³, p, p²)` with `λ = o(μ′)`.
-/

public section

open scoped Matrix

theorem ExplicitRIP.Provider.host_parameters :
    (∀ (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)],
      open Classical in
        (ExplicitRIP.contactGraph p).IsSRGWith (p ^ 4) ((p - 1) * (p ^ 2 + 1)) (p - 2)
          (p * (p - 1))) ∧
    ∀ ε : ℝ, 0 < ε → ∃ P : ℕ,
      ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)], P ≤ p →
        |(p : ℝ) ^ 4 / (p : ℝ) ^ 4 - 1| ≤ ε ∧
        |(((p : ℝ) - 1) * ((p : ℝ) ^ 2 + 1)) / (p : ℝ) ^ 3 - 1| ≤ ε ∧
        |((p : ℝ) - 2) / (p : ℝ) - 1| ≤ ε ∧
        |((p : ℝ) * ((p : ℝ) - 1)) / (p : ℝ) ^ 2 - 1| ≤ ε ∧
        |((p : ℝ) - 2) / ((p : ℝ) * ((p : ℝ) - 1))| ≤ ε := by
  refine ⟨fun p _ _ => ExplicitRIP.Contact.HostFrame.isSRGWith p, ?_⟩
  intro ε hε
  obtain ⟨P, hP⟩ := exists_nat_gt (max (2 : ℝ) (2 / ε))
  refine ⟨P, fun p _ _ hp => ?_⟩
  have hcast : (P : ℝ) ≤ p := by exact_mod_cast hp
  have hp2 : (2 : ℝ) ≤ p := (le_max_left _ _).trans (hP.le.trans hcast)
  have hεp : 2 / ε ≤ (p : ℝ) := (le_max_right _ _).trans (hP.le.trans hcast)
  have hp0 : (0 : ℝ) < p := by linarith only [hp2]
  have hsmall : 2 / (p : ℝ) ≤ ε := by
    apply (div_le_iff₀ hp0).mpr
    simpa only [mul_comm] using (div_le_iff₀ hε).mp hεp
  have hsmall' : 1 / (p : ℝ) ≤ ε :=
    (div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) hp0.le).trans hsmall
  refine ⟨?_, (ExplicitRIP.Contact.HostFrame.dimension_ratio_error (p : ℝ) hp2).trans hsmall',
    ?_, ?_, ?_⟩
  · rw [div_self (pow_ne_zero 4 hp0.ne'), sub_self, abs_zero]
    exact hε.le
  · have he : ((p : ℝ) - 2) / (p : ℝ) - 1 = -(2 / (p : ℝ)) := by
      field_simp
      ring
    rw [he, abs_neg, abs_of_nonneg (div_nonneg (by norm_num) hp0.le)]
    exact hsmall
  · have he : ((p : ℝ) * ((p : ℝ) - 1)) / (p : ℝ) ^ 2 - 1 = -(1 / (p : ℝ)) := by
      field_simp
      ring
    rw [he, abs_neg, abs_of_nonneg (div_nonneg (by norm_num) hp0.le)]
    exact hsmall'
  · have hq : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 1) := by nlinarith only [hp2]
    rw [abs_of_nonneg (div_nonneg (by linarith only [hp2]) hq.le)]
    refine le_trans ?_ hsmall'
    apply (div_le_div_iff₀ hq hp0).mpr
    nlinarith only [hp2]
