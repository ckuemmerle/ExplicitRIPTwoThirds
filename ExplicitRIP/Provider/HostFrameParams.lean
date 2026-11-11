/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Contact.HostFrame.ScaleAsymptotics

/-!
# The host frame and the parameters of [KM, (13)]

Source: [KM, Section 3, (13), and proof of Theorem 1, (16) and footnote 4].

The contact graph carries a real unit-norm tight frame whose Gram matrix is `p⁴/m` times the
projection onto the least adjacency eigenspace. This eigenspace has dimension
`m = (p - 1)(p² + 1)` and eigenvalue `-(p² - p + 1)`. The parameter asymptotics in [KM, (13)]
and (16) hold as `p → ∞` through primes `p ≡ 3 (mod 4)`.
-/

public section

open scoped Matrix

theorem ExplicitRIP.Provider.host_frame_params :
    (∀ (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)],
      (open Classical in
        (ExplicitRIP.contactGraph p).adjMatrix ℝ * ExplicitRIP.hostGram ℝ p =
          (-((p : ℝ) ^ 2 - p + 1)) • ExplicitRIP.hostGram ℝ p) ∧
      ExplicitRIP.hostGram ℝ p * ExplicitRIP.hostGram ℝ p =
        ((p : ℝ) ^ 4 / (((p - 1) * (p ^ 2 + 1) : ℕ) : ℝ)) • ExplicitRIP.hostGram ℝ p ∧
      (ExplicitRIP.hostGram ℝ p).rank = (p - 1) * (p ^ 2 + 1) ∧
      (open Classical in
        Module.finrank ℝ (Module.End.eigenspace
            (Matrix.toLin' ((ExplicitRIP.contactGraph p).adjMatrix ℝ)) (-((p : ℝ) ^ 2 - p + 1))) =
          (p - 1) * (p ^ 2 + 1)) ∧
      ∃ B : Matrix (Fin ((p - 1) * (p ^ 2 + 1))) (ZMod p × ZMod p × ZMod p × ZMod p) ℝ,
        Bᵀ * B = ExplicitRIP.hostGram ℝ p ∧ (∀ x, ∑ r, B r x ^ 2 = 1) ∧
        B * Bᵀ = ((p : ℝ) ^ 4 / (((p - 1) * (p ^ 2 + 1) : ℕ) : ℝ)) •
          (1 : Matrix (Fin ((p - 1) * (p ^ 2 + 1))) (Fin ((p - 1) * (p ^ 2 + 1))) ℝ)) ∧
    ∀ ε : ℝ, 0 < ε → ∃ P : ℕ, ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)], P ≤ p →
      let m : ℝ := ((p : ℝ) - 1) * ((p : ℝ) ^ 2 + 1)
      let μ : ℝ := ((p : ℝ) ^ 2 - p + 1) / m
      let ν : ℝ := 1 / ((p : ℝ) ^ 2 + 1)
      |m / (p : ℝ) ^ 3 - 1| ≤ ε ∧
        |μ * m ^ (1 / 3 : ℝ) - 1| ≤ ε ∧ |ν * m ^ (2 / 3 : ℝ) - 1| ≤ ε ∧
        |(p : ℝ) * μ - 1| ≤ ε ∧ |(p : ℝ) ^ 2 * ν - 1| ≤ ε := by
  refine ⟨fun p _ _ => ?_, ?_⟩
  · exact ⟨ExplicitRIP.Contact.HostFrame.adj_mul_hostGram p,
      ExplicitRIP.Contact.HostFrame.hostGram_mul_self p,
      ExplicitRIP.Contact.HostFrame.hostGram_rank p,
      ExplicitRIP.Contact.HostFrame.eigenspace_finrank p,
      ExplicitRIP.Contact.HostFrame.exists_tight_frame p⟩
  · intro ε hε
    obtain ⟨P, hP⟩ := exists_nat_gt (max (2 : ℝ) (2 / ε))
    refine ⟨P, fun p _ _ hp => ?_⟩
    have hcast : (P : ℝ) ≤ p := by exact_mod_cast hp
    have hp2 : (2 : ℝ) ≤ p := (le_max_left _ _).trans (hP.le.trans hcast)
    have hεp : 2 / ε ≤ (p : ℝ) := (le_max_right _ _).trans (hP.le.trans hcast)
    have hp0 : (0 : ℝ) < p := by linarith only [hp2]
    have hsmall : 2 / (p : ℝ) ≤ ε := by
      apply (div_le_iff₀ hp0).mpr
      simpa only [mul_comm] using (div_le_iff₀ hε).mp hεp
    obtain ⟨ha, hb⟩ := ExplicitRIP.Contact.HostFrame.scale_error_bounds (p : ℝ) hp2
    obtain ⟨hc, hd, _⟩ := ExplicitRIP.HostFrame.parameter_error_bounds (p : ℝ) hp2
    have hsmall' : 1 / (p : ℝ) ≤ ε :=
      (div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) hp0.le).trans hsmall
    exact ⟨(ExplicitRIP.Contact.HostFrame.dimension_ratio_error (p : ℝ) hp2).trans hsmall',
      ha.trans hsmall, hb.trans hsmall, hc.trans hsmall', hd.trans hsmall'⟩
