/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.SphereContacts

/-!
# Proof of Theorem 6 of [KM]: the sphere-contact dichotomy

Source: [KM, Theorem 6]; [Z, Theorem 1.8].

[Z, Theorem 1.8] is used for oriented spheres over `𝔽_p`, with `p ≡ 3 (mod 4)` and at most `p²`
spheres. Either the number of two-rich pencils is bounded by an absolute multiple of `s^(3/2)`,
or each conic of a complementary pair contains at least `√s` spheres.
-/

public section

open scoped Matrix

theorem ExplicitRIP.Provider.zahl_sphere_contacts :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)],
      ∀ U : Finset (ZMod p × ZMod p × ZMod p × ZMod p), U.card ≤ p ^ 2 →
        (ExplicitRIP.richPencilCount U 2 : ℝ) ≤ C * (U.card : ℝ) ^ (3 / 2 : ℝ) ∨
          ∃ 𝒞 𝒞' : Set (ZMod p × ZMod p × ZMod p × ZMod p),
            ExplicitRIP.IsComplementaryConicPair 𝒞 𝒞' ∧
              (open Classical in
                Real.sqrt U.card ≤ ((U.filter (· ∈ 𝒞)).card : ℝ) ∧
                  Real.sqrt U.card ≤ ((U.filter (· ∈ 𝒞')).card : ℝ)) :=
by
  obtain ⟨C, hC, h⟩ := ExplicitRIP.Zahl.sphere_contacts
  refine ⟨C, hC, ?_⟩
  intro p _ _ U hU
  exact (h p U hU).2
