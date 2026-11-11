/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.SelectedVertices
public import ExplicitRIP.Frozen.Defs.ContactGraph
public import ExplicitRIP.Frozen.Defs.InducedEdgeCount
import ExplicitRIP.Provider.HereditaryDensity

/-!
# Proposition 8 of [KM]: hereditary density of the selected vertices

Source: [KM, Proposition 8].
-/

public section

open scoped Matrix

/-- [KM, Proposition 8]. There is an absolute constant `C` such that for every prime
`p ≡ 3 (mod 4)`, every `T ⊆ 𝔽_p` of size `L` and every `U ⊆ V'_T` of size `s ≤ p²`,
`e(U) ≤ C L s^{3/2}`, where edges are those of `VO₄⁻(p)`. -/
theorem ExplicitRIP.hereditary_density :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)], ∀ T : Finset (ZMod p),
      ∀ U ⊆ ExplicitRIP.selectedVertices p T, U.card ≤ p ^ 2 →
        (open Classical in
          (ExplicitRIP.inducedEdgeCount (ExplicitRIP.contactGraph p) U : ℝ)) ≤
          C * T.card * (U.card : ℝ) ^ (3 / 2 : ℝ) :=
by exact ExplicitRIP.Provider.hereditary_density
