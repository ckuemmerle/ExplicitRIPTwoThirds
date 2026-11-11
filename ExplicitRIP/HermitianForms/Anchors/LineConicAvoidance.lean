/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.HermitianForms.Defs.SelectedVertices
public import ExplicitRIP.Algebra.AvoidanceLine
public import ExplicitRIP.Algebra.AvoidanceConic

/-!
# Line and conic avoidance in Hermitian coordinates

Each line contains at most `3L` selected Hermitian vertices and each plane conic contains at
most `6L`. The linear sphere map transports both bounds to the light-cone selection in contact
coordinates. These are the norm-graph intersection bounds of [KM, Lemma 7], applied to
`c = N(a, b₁, b₂) + t` in Hermitian coordinates. Its sphere-map image satisfies
`r - z = N(r + z, x, y) + t`, whereas [KM, (15)] uses `r = N(x, y, z) + t`.
-/

public section

open scoped Matrix

theorem ExplicitRIP.Hermitian.line_conic_avoidance :
    ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)], ∀ T : Finset (ZMod p),
      (∀ x₀ v : ZMod p × ZMod p × ZMod p × ZMod p, v ≠ 0 →
        ((ExplicitRIP.hermitianSelectedVertices p T).filter
          (fun x => ∃ t : ZMod p, x = x₀ + t • v)).card ≤ 3 * T.card) ∧
      ∀ x₀ u w : ZMod p × ZMod p × ZMod p × ZMod p, LinearIndependent (ZMod p) ![u, w] →
        ∀ g : MvPolynomial (Fin 2) (ZMod p), g ≠ 0 → g.totalDegree ≤ 2 →
          ((ExplicitRIP.hermitianSelectedVertices p T).filter (fun x => ∃ s t : ZMod p,
            x = x₀ + s • u + t • w ∧ MvPolynomial.eval ![s, t] g = 0)).card ≤ 6 * T.card :=
  fun p _ _ T =>
    ⟨fun x₀ v hv => ExplicitRIP.Avoidance.line_bound p T x₀ v hv,
      fun x₀ u w huw g hg hdeg =>
        ExplicitRIP.Avoidance.conic_bound p T
          (fun x₀ v hv => ExplicitRIP.Avoidance.line_bound p T x₀ v hv)
          x₀ u w huw g hg hdeg⟩
