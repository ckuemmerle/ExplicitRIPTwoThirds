/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.HermitianForms.Defs.HermitianGraph
public import ExplicitRIP.HermitianForms.Defs.HostGram
public import ExplicitRIP.HermitianForms.HostSRG
public import ExplicitRIP.HermitianForms.HostFrame

/-!
# The tight frame of the Hermitian forms graph

The Hermitian-forms model of `VO₄⁻(p)` is strongly regular with parameters
`(p⁴, m, p - 2, p(p - 1))`. It carries a real unit-norm tight frame with Gram matrix
`hermitianHostGram`, adjacent magnitude asymptotic to `1/p`, and nonadjacent magnitude asymptotic
to `1/p²`. The sphere map transports these properties to the contact graph of [KM, Section 4.1].

The graph parameters and frame are those of [KM, Section 3, (13)].
-/

public section

open scoped Matrix

theorem ExplicitRIP.Hermitian.hermitian_graph_frame :
    (∀ (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)],
      (open Classical in
        (ExplicitRIP.hermitianGraph p).IsSRGWith (p ^ 4) ((p - 1) * (p ^ 2 + 1)) (p - 2)
          (p * (p - 1))) ∧
      ∃ B : Matrix (Fin ((p - 1) * (p ^ 2 + 1))) (ZMod p × ZMod p × ZMod p × ZMod p) ℝ,
        Bᵀ * B = ExplicitRIP.hermitianHostGram ℝ p ∧
        B * Bᵀ = ((p : ℝ) ^ 4 / (((p - 1) * (p ^ 2 + 1) : ℕ) : ℝ)) •
          (1 : Matrix (Fin ((p - 1) * (p ^ 2 + 1))) (Fin ((p - 1) * (p ^ 2 + 1))) ℝ)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ P : ℕ, ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)], P ≤ p →
        |(p : ℝ) * (((p : ℝ) ^ 2 - p + 1) / (((p : ℝ) - 1) * ((p : ℝ) ^ 2 + 1))) - 1| ≤ ε ∧
        |(p : ℝ) ^ 2 * (1 / ((p : ℝ) ^ 2 + 1)) - 1| ≤ ε ∧
        |(p : ℝ) * (((ExplicitRIP.hermitianGraph p).edgeSet.ncard : ℝ) / ((p ^ 4).choose 2 : ℕ)) -
          1| ≤ ε :=
  ⟨fun p _ _ => ⟨ExplicitRIP.HostFrame.isSRGWith p,
      ExplicitRIP.HostFrame.frame_of_isSRGWith p (ExplicitRIP.HostFrame.isSRGWith p)⟩,
    ExplicitRIP.HostFrame.asymptotics_of_isSRGWith fun p _ _ => ExplicitRIP.HostFrame.isSRGWith p⟩
