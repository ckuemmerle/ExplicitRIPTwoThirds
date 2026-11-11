/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Structure
public import ExplicitRIP.GuthZahl.Boundary.Translations

/-!
# The raw positive-characteristic Guth–Zahl boundary with `c = 1`

The line-only structure theorem `guthZahl_lines_charSquare` gives a bound on rich
points or a surface containing many lines. This module transports that alternative
to Zahl's normalized chart lines.
-/

public section

namespace ExplicitRIP.GuthZahl
open ExplicitRIP.Zahl (ChartLine)

open Classical in
/-- The line-only structure theorem `guthZahl_lines_charSquare` supplies `c = 1` directly;
no fixed-size thinning is needed for this boundary. -/
theorem guthZahl_algebraicallyClosed_charSquare_structure :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [IsAlgClosed K] [CharP K p],
        (2 : K) ≠ 0 → ∀ L : Finset (ChartLine K), L.card ≤ p ^ 2 → ∀ A : ℝ,
          C * Real.sqrt (L.card : ℝ) ≤ A →
            (Zahl.richCount L 2 : ℝ) ≤ C * A * (L.card : ℝ) ∨
              (∃ normal : Point K, normal ≠ 0 ∧ ∃ offset : K,
                A ≤ ((L.filter (Zahl.planeContains normal offset)).card : ℝ)) ∨
              ∃ f : Poly K, Irreducible f ∧ Zahl.doublyRuledHypersurface f ∧
                A ≤ ((L.filter (Zahl.hypersurfaceContains f)).card : ℝ) := by
  obtain ⟨C, hC, h⟩ := guthZahl_lines_charSquare
  refine ⟨max C 1, le_max_right _ _, ?_⟩
  intro p hp K hK hclosed hchar h2 L hsize A hA
  have hsize' : (chartFamily L).card ≤ p ^ 2 := by rwa [chartFamily_card]
  have hA' : C * Real.sqrt (chartFamily L).card ≤ A := by
    rw [chartFamily_card]
    exact (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)).trans hA
  rcases h p K (chartFamily L) hsize' A hA' with hcoun | ⟨f, hf, hr, _, hmany⟩
  · left
    rw [chartFamily_richCount, chartFamily_card] at hcoun
    have hAnonneg : 0 ≤ A :=
      (mul_nonneg (le_trans zero_le_one (le_max_right C 1)) (Real.sqrt_nonneg _)).trans hA
    exact hcoun.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hAnonneg) (Nat.cast_nonneg _))
  · right; right
    refine ⟨f, hf, (doublyRuled_iff_zahl f).mp hr, ?_⟩
    rwa [chartFamily_filter_card] at hmany

end ExplicitRIP.GuthZahl

end
