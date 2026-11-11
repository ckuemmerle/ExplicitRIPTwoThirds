/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Frozen.Defs.SelectedVertices
import ExplicitRIP.HermitianForms.Anchors.LineConicAvoidance

/-!
# Proof of Lemma 7 of [KM]: line and conic avoidance

Source: [KM, Lemma 7 and its proof].

In the coordinates `(x, y, z, r)` of [KM, Section 4.1], the norm graph `V′_T` meets each affine
line in at most `3L` points and each affine plane conic in at most `6L` points, where `L = |T|`.
-/

public section

open scoped Matrix

theorem ExplicitRIP.Provider.line_conic_avoidance :
    ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)], ∀ T : Finset (ZMod p),
      (∀ x₀ v : ZMod p × ZMod p × ZMod p × ZMod p, v ≠ 0 →
        ((ExplicitRIP.selectedVertices p T).filter
          (fun x => ∃ t : ZMod p, x = x₀ + t • v)).card ≤ 3 * T.card) ∧
      ∀ x₀ u w : ZMod p × ZMod p × ZMod p × ZMod p, LinearIndependent (ZMod p) ![u, w] →
        ∀ g : MvPolynomial (Fin 2) (ZMod p), g ≠ 0 → g.totalDegree ≤ 2 →
          ((ExplicitRIP.selectedVertices p T).filter (fun x => ∃ s t : ZMod p,
            x = x₀ + s • u + t • w ∧ MvPolynomial.eval ![s, t] g = 0)).card ≤ 6 * T.card := by
  intro p _ _ T
  exact ExplicitRIP.Hermitian.line_conic_avoidance p T
