/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Contact.HereditaryDensity

/-!
# Proof of Proposition 8 of [KM]: hereditary density

Source: [KM, Proposition 8 and its proof].

The translate-pair argument applies the contact-pencil dichotomy of [KM, Theorem 6] directly to
the norm graph. For `T ⊆ 𝔽_p` of size `L` and `U ⊆ V′_T` of size `s ≤ p²`, it gives
`e(U) ≲ L s^{3/2}`.
-/

public section

theorem ExplicitRIP.Provider.hereditary_density :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)], ∀ T : Finset (ZMod p),
      ∀ U ⊆ ExplicitRIP.selectedVertices p T, U.card ≤ p ^ 2 →
        (open Classical in
          (ExplicitRIP.inducedEdgeCount (ExplicitRIP.contactGraph p) U : ℝ)) ≤
          C * T.card * (U.card : ℝ) ^ (3 / 2 : ℝ) := by
  exact ExplicitRIP.Contact.Density.hereditary_density
