/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Relative.Zahl.SphereContacts
public import ExplicitRIP.GuthZahl.Boundary.HeisenbergStructure

/-!
# Zahl's sphere-contact theorem

[Z, Theorem 1.8] in the case used in [KM, Theorem 6]: sphere families in `𝔽_p⁴`,
`p ≡ 3 (mod 4)`, with at most `p²` spheres. It is the conditional version
`ExplicitRIP.Relative.Zahl.sphere_contacts`, whose premise is the Guth–Zahl structure
theorem for Heisenberg lines, applied to
`ExplicitRIP.GuthZahl.guthZahl_heisenberg_structure`. The result is restricted to these fields.
-/

public section

namespace ExplicitRIP.Zahl

/-- [Z, Theorem 1.8] for `𝔽_p`, `p ≡ 3 (mod 4)`, and at most `p²` spheres: the bound on `h`-rich
pencils for every `h ≥ 3`, and either the bound on two-rich pencils or a complementary conic pair
each of whose sides carries at least `√|S|` of the spheres. -/
theorem sphere_contacts :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)],
      ∀ S : Finset (ZMod p × ZMod p × ZMod p × ZMod p), S.card ≤ p ^ 2 →
        (∀ h : ℕ, 3 ≤ h →
          (ExplicitRIP.richPencilCount S h : ℝ) ≤
            C * (S.card : ℝ) ^ (3 / 2 : ℝ) * (h : ℝ) ^ (-(3 / 2 : ℝ))) ∧
        ((ExplicitRIP.richPencilCount S 2 : ℝ) ≤ C * (S.card : ℝ) ^ (3 / 2 : ℝ) ∨
          ∃ C₀ C₁ : Set (ZMod p × ZMod p × ZMod p × ZMod p),
            ExplicitRIP.IsComplementaryConicPair C₀ C₁ ∧
              (open Classical in
                Real.sqrt S.card ≤ ((S.filter (· ∈ C₀)).card : ℝ) ∧
                  Real.sqrt S.card ≤ ((S.filter (· ∈ C₁)).card : ℝ))) :=
  ExplicitRIP.Relative.Zahl.sphere_contacts
    ExplicitRIP.GuthZahl.guthZahl_heisenberg_structure

end ExplicitRIP.Zahl

end
