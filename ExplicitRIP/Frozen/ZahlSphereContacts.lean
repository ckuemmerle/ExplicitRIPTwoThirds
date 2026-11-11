/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.RichPencilCount
public import ExplicitRIP.Frozen.Defs.IsComplementaryConicPair
import ExplicitRIP.Provider.ZahlSphereContacts

/-!
# Theorem 6 of [KM]: the sphere-contact dichotomy

Source: [KM, Theorem 6]; [Z, Theorem 1.8].
-/

public section

open scoped Matrix

/-- [KM, Theorem 6], a special case of [Z, Theorem 1.8]. There is an absolute constant `C` such
that for every prime `p ≡ 3 (mod 4)` and every `U ⊆ 𝔽_p⁴` of size `s ≤ p²`, either the
number of pencils containing at least two points of `U` is at most `C s^{3/2}`, or there is
a pair of complementary conics `𝒞, 𝒞'` each containing at least `√s` points of `U`. -/
theorem ExplicitRIP.zahl_sphere_contacts :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)],
      ∀ U : Finset (ZMod p × ZMod p × ZMod p × ZMod p), U.card ≤ p ^ 2 →
        (ExplicitRIP.richPencilCount U 2 : ℝ) ≤ C * (U.card : ℝ) ^ (3 / 2 : ℝ) ∨
          ∃ 𝒞 𝒞' : Set (ZMod p × ZMod p × ZMod p × ZMod p),
            ExplicitRIP.IsComplementaryConicPair 𝒞 𝒞' ∧
              (open Classical in
                Real.sqrt U.card ≤ ((U.filter (· ∈ 𝒞)).card : ℝ) ∧
                  Real.sqrt U.card ≤ ((U.filter (· ∈ 𝒞')).card : ℝ)) :=
by exact ExplicitRIP.Provider.zahl_sphere_contacts
