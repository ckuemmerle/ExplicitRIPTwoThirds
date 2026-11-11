/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.SelectedVertices
import ExplicitRIP.Provider.LineConicAvoidance

/-!
# Lemma 7 of [KM]: line and conic avoidance

Source: [KM, Lemma 7(a) and (b)].

In part (b), an affine plane conic is represented by the zero set of a nonzero polynomial of
total degree at most two in affine plane coordinates.
-/

public section

open scoped Matrix

/-- [KM, Lemma 7]. For a prime `p ≡ 3 (mod 4)` and `T ⊆ 𝔽_p` of size `L`, every affine line
`{x₀ + t v : t ∈ 𝔽_p}` with `v ≠ 0` in `𝔽_p⁴` contains at most `3L` points of `V'_T`. Every
affine plane conic defined over `𝔽_p`, represented by the points `x₀ + s u + t w` with
`u, w` linearly independent and `g(s, t) = 0` for a nonzero polynomial `g` of total degree
at most two, contains at most `6L` points of `V'_T`. -/
theorem ExplicitRIP.line_conic_avoidance :
    ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)], ∀ T : Finset (ZMod p),
      (∀ x₀ v : ZMod p × ZMod p × ZMod p × ZMod p, v ≠ 0 →
        ((ExplicitRIP.selectedVertices p T).filter
          (fun x => ∃ t : ZMod p, x = x₀ + t • v)).card ≤ 3 * T.card) ∧
      ∀ x₀ u w : ZMod p × ZMod p × ZMod p × ZMod p, LinearIndependent (ZMod p) ![u, w] →
        ∀ g : MvPolynomial (Fin 2) (ZMod p), g ≠ 0 → g.totalDegree ≤ 2 →
          ((ExplicitRIP.selectedVertices p T).filter (fun x => ∃ s t : ZMod p,
            x = x₀ + s • u + t • w ∧ MvPolynomial.eval ![s, t] g = 0)).card ≤ 6 * T.card :=
by exact ExplicitRIP.Provider.line_conic_avoidance
