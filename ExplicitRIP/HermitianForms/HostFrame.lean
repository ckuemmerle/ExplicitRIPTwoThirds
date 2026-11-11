/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.HermitianForms.HostFrame.Gram
public import ExplicitRIP.HermitianForms.HostFrame.Spectral
public import ExplicitRIP.HermitianForms.HostFrame.Asymptotics

/-!
# The Hermitian host frame from its strongly regular parameters

This supplies the frame and asymptotic properties of the Hermitian-forms model of `VO₄⁻(p)`,
assuming the strong regularity proved separately. The frame has the parameters of
[KM, Section 3, (13)] and is transported to contact coordinates by the sphere map.
-/

public section

open scoped Matrix

theorem ExplicitRIP.HostFrame.frame_of_isSRGWith (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]
    (hSRG : (open Classical in
      (ExplicitRIP.hermitianGraph p).IsSRGWith (p ^ 4) ((p - 1) * (p ^ 2 + 1)) (p - 2)
        (p * (p - 1)))) :
    ∃ B : Matrix (Fin ((p - 1) * (p ^ 2 + 1))) (ZMod p × ZMod p × ZMod p × ZMod p) ℝ,
      Bᵀ * B = ExplicitRIP.hermitianHostGram ℝ p ∧
      B * Bᵀ = ((p : ℝ) ^ 4 / (((p - 1) * (p ^ 2 + 1) : ℕ) : ℝ)) •
        (1 : Matrix (Fin ((p - 1) * (p ^ 2 + 1))) (Fin ((p - 1) * (p ^ 2 + 1))) ℝ) := by
  classical
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hmNat : 0 < (p - 1) * (p ^ 2 + 1) :=
    Nat.mul_pos (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt) (by omega)
  have hm : 0 < (((p - 1) * (p ^ 2 + 1) : ℕ) : ℝ) := by exact_mod_cast hmNat
  refine ExplicitRIP.HostFrame.exists_tight_frame_of_scaled_projection
    (ExplicitRIP.hermitianHostGram ℝ p) (ExplicitRIP.HostFrame.hostGram_isHermitian p)
    ((p : ℝ) ^ 4 / (((p - 1) * (p ^ 2 + 1) : ℕ) : ℝ)) (by positivity)
    (ExplicitRIP.HostFrame.hostGram_mul_self_of_isSRGWith p hSRG)
    ((p - 1) * (p ^ 2 + 1)) ?_
  rw [ExplicitRIP.HostFrame.hostGram_trace, div_mul_cancel₀ _ hm.ne']

theorem ExplicitRIP.HostFrame.asymptotics_of_isSRGWith
    (hSRG : ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)],
      (open Classical in
      (ExplicitRIP.hermitianGraph p).IsSRGWith (p ^ 4) ((p - 1) * (p ^ 2 + 1)) (p - 2)
        (p * (p - 1)))) :
    ∀ ε : ℝ, 0 < ε → ∃ P : ℕ, ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)], P ≤ p →
      |(p : ℝ) * (((p : ℝ) ^ 2 - p + 1) / (((p : ℝ) - 1) * ((p : ℝ) ^ 2 + 1))) - 1| ≤ ε ∧
      |(p : ℝ) ^ 2 * (1 / ((p : ℝ) ^ 2 + 1)) - 1| ≤ ε ∧
      |(p : ℝ) * (((ExplicitRIP.hermitianGraph p).edgeSet.ncard : ℝ) / ((p ^ 4).choose 2 : ℕ)) -
        1| ≤ ε := by
  intro ε hε
  obtain ⟨P, hP⟩ := exists_nat_gt (max (2 : ℝ) (1 / ε))
  refine ⟨P, ?_⟩
  intro p _ _ hPp
  have hcast : (P : ℝ) ≤ p := by exact_mod_cast hPp
  have hp2 : (2 : ℝ) ≤ p := (le_max_left _ _).trans ((le_of_lt hP).trans hcast)
  have hεp : 1 / ε ≤ (p : ℝ) := (le_max_right _ _).trans ((le_of_lt hP).trans hcast)
  have hp0 : (0 : ℝ) < p := by linarith
  have hsmall : 1 / (p : ℝ) ≤ ε := by
    apply (div_le_iff₀ hp0).mpr
    simpa only [mul_comm] using (div_le_iff₀ hε).mp hεp
  obtain ⟨ha, hb, hd⟩ := ExplicitRIP.HostFrame.parameter_error_bounds (p : ℝ) hp2
  rw [ExplicitRIP.HostFrame.edge_density_of_isSRGWith p (hSRG p)]
  exact ⟨ha.trans hsmall, hb.trans hsmall, hd.trans hsmall⟩
