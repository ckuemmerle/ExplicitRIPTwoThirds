/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Boundary.Defs
import ExplicitRIP.Relative.GuthZahl.Boundary.Descent
import ExplicitRIP.GuthZahl.Boundary.Descent
import ExplicitRIP.GuthZahl.Boundary.Translations
import ExplicitRIP.GuthZahl.RuledSurfaces

/-!
# The Guth–Zahl structure theorem for Heisenberg lines, from the algebraically closed case

A conditional helper. Its only premise is the line case of [GZ, Theorem 3.8] over
an algebraically closed field of positive characteristic, in the exact form proved by
`ExplicitRIP.GuthZahl.guthZahl_algebraicallyClosed_charSquare_structure`.
The theorem `ExplicitRIP.GuthZahl.guthZahl_heisenberg_structure` applies the result below
to that proof. Extension to an algebraic closure preserves two-rich counts, and the plane
and split-quadric alternatives descend with their cardinality bounds.
-/

public section

namespace ExplicitRIP.GuthZahl
open ExplicitRIP.Zahl (ChartLine)

open Classical in
/-- The Guth–Zahl structure theorem for chart lines over fields of positive characteristic,
assuming the algebraically closed case `hRaw`. Scalar extension and descent of planes and
split quadrics give the proof, after enlarging `C` to at least 5. -/
theorem _root_.ExplicitRIP.Relative.GuthZahl.guthZahl_positive_chart_structure
    (hRaw : (∃ C : ℝ, 1 ≤ C ∧
            ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [IsAlgClosed K] [CharP K p],
              (2 : K) ≠ 0 → ∀ L : Finset (ChartLine K), L.card ≤ p ^ 2 → ∀ A : ℝ,
                C * Real.sqrt (L.card : ℝ) ≤ A →
                  (Zahl.richCount L 2 : ℝ) ≤ C * A * (L.card : ℝ) ∨
                    (∃ normal : Point K, normal ≠ 0 ∧ ∃ offset : K,
                      A ≤ ((L.filter (Zahl.planeContains normal offset)).card : ℝ)) ∨
                    ∃ f : Poly K, Irreducible f ∧ Zahl.doublyRuledHypersurface f ∧
                      A ≤ ((L.filter (Zahl.hypersurfaceContains f)).card : ℝ))) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ 1 ∧ 5 ≤ C ∧
      ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [CharP F p],
        (2 : F) ≠ 0 → ∀ L : Finset (ChartLine F),
          (L.card : ℝ) ≤ c * (p : ℝ) ^ 2 → ∀ A : ℝ,
          C * Real.sqrt (L.card : ℝ) ≤ A →
            (Zahl.richCount L 2 : ℝ) ≤ C * A * (L.card : ℝ) ∨
              (∃ normal : Point F, normal ≠ 0 ∧ ∃ offset : F,
                A ≤ ((L.filter (Zahl.planeContains normal offset)).card : ℝ)) ∨
              ∃ Q : Zahl.SplitQuadric F,
                A ≤ ((L.filter (Zahl.quadricContains Q)).card : ℝ) := by
  obtain ⟨C, hC, hraw⟩ := hRaw
  refine ⟨1, max C 5, by norm_num, le_rfl, le_max_right _ _, ?_⟩
  intro p hp F hF hchar h2 L hsize A hA
  by_cases hL : L.Nonempty
  · have hC0 : 0 ≤ max C 5 := (by norm_num : (0 : ℝ) ≤ 5).trans (le_max_right _ _)
    have hcard_one : (1 : ℝ) ≤ (L.card : ℝ) := by
      exact_mod_cast Finset.one_le_card.mpr hL
    have hA5 : 5 ≤ A := calc
      (5 : ℝ) ≤ max C 5 := le_max_right _ _
      _ = max C 5 * 1 := (mul_one _).symm
      _ ≤ max C 5 * Real.sqrt (L.card : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.one_le_sqrt.mpr hcard_one) hC0
      _ ≤ A := hA
    have hA0 : 0 ≤ A := (by norm_num : (0 : ℝ) ≤ 5).trans hA5
    have hA2 : 2 ≤ A := (by norm_num : (2 : ℝ) ≤ 5).trans hA5
    let φ : F →+* AlgebraicClosure F := algebraMap F (AlgebraicClosure F)
    have h2K : (2 : AlgebraicClosure F) ≠ 0 := by
      simpa only [map_ofNat, map_zero] using φ.injective.ne h2
    have hsizeK : (mapChartFamily φ L).card ≤ p ^ 2 := by
      rw [mapChartFamily_card]
      exact_mod_cast (show (L.card : ℝ) ≤ (p : ℝ) ^ 2 by
        simpa only [one_mul] using hsize)
    have hAK : C * Real.sqrt ((mapChartFamily φ L).card : ℝ) ≤ A := by
      rw [mapChartFamily_card]
      exact (mul_le_mul_of_nonneg_right (le_max_left C 5) (Real.sqrt_nonneg _)).trans hA
    rcases hraw p (AlgebraicClosure F) h2K (mapChartFamily φ L) hsizeK A hAK with
      hcount | ⟨normal, hn, offset, hplane⟩ | ⟨f, hf, hruled, hsurface⟩
    · left
      rw [mapChartFamily_richCount φ L 2 le_rfl, mapChartFamily_card] at hcount
      exact hcount.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left C 5) hA0) (Nat.cast_nonneg _))
    · exact Or.inr (Or.inl
        (Relative.GuthZahl.Boundary.plane_filter_descends φ L A hA2 normal hn offset hplane))
    · have hr : DoublyRuled f := (doublyRuled_iff_zahl f).mpr hruled
      by_cases hlinear : f.totalDegree = 1
      · obtain ⟨normal, hn, offset, rfl⟩ := degree_one_plane_form f hlinear
        apply Or.inr ∘ Or.inl
        apply Relative.GuthZahl.Boundary.plane_filter_descends φ L A hA2 normal hn offset
        refine hsurface.trans ?_
        exact_mod_cast Finset.card_le_card (show
          (mapChartFamily φ L).filter (Zahl.hypersurfaceContains (planePolynomial normal offset)) ⊆
            (mapChartFamily φ L).filter (Zahl.planeContains normal offset) from by
          intro l hl
          obtain ⟨hlL, hl⟩ := Finset.mem_filter.mp hl
          exact Finset.mem_filter.mpr ⟨hlL, (planeContains_iff_LineOn normal offset l).mpr
            ((chartLift_LineOn_iff_hypersurfaceContains _ l).mpr hl)⟩)
      · obtain ⟨Q, hQ⟩ := doublyRuled_degree_two_normal_form h2K f hf hr
          (doublyRuled_degree_le_two h2K f hf hr) hlinear
        apply Or.inr ∘ Or.inr
        apply Relative.GuthZahl.Boundary.quadric_filter_descends φ h2 L A hA5 Q
        refine hsurface.trans ?_
        exact_mod_cast Finset.card_le_card (show
          (mapChartFamily φ L).filter (Zahl.hypersurfaceContains f) ⊆
            (mapChartFamily φ L).filter (Zahl.quadricContains Q) from by
          intro l hl
          obtain ⟨hlL, hl⟩ := Finset.mem_filter.mp hl
          exact Finset.mem_filter.mpr ⟨hlL, fun x hx => (hQ x).mp (hl x hx)⟩)
  · have hempty : L = ∅ := Finset.not_nonempty_iff_eq_empty.mp hL
    subst L
    left
    simp only [Zahl.richCount, Zahl.richPoints, Finset.filter_empty, Finset.card_empty,
      show ¬ 2 ≤ (0 : ℕ) by decide, Set.ofPred_false, Set.ncard_empty, Nat.cast_zero,
      mul_zero, le_refl]

open Classical in
/-- The Guth–Zahl structure theorem for Heisenberg lines, assuming the
algebraically closed case `hRaw`: the positive-characteristic chart theorem specialized to the
quadratic extension `𝔽_p[i]`, which has characteristic `p`. -/
theorem _root_.ExplicitRIP.Relative.GuthZahl.guthZahl_heisenberg_structure
    (hRaw : (∃ C : ℝ, 1 ≤ C ∧
            ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [IsAlgClosed K] [CharP K p],
              (2 : K) ≠ 0 → ∀ L : Finset (ChartLine K), L.card ≤ p ^ 2 → ∀ A : ℝ,
                C * Real.sqrt (L.card : ℝ) ≤ A →
                  (Zahl.richCount L 2 : ℝ) ≤ C * A * (L.card : ℝ) ∨
                    (∃ normal : Point K, normal ≠ 0 ∧ ∃ offset : K,
                      A ≤ ((L.filter (Zahl.planeContains normal offset)).card : ℝ)) ∨
                    ∃ f : Poly K, Irreducible f ∧ Zahl.doublyRuledHypersurface f ∧
                      A ≤ ((L.filter (Zahl.hypersurfaceContains f)).card : ℝ))) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ 1 ∧ 1 ≤ C ∧
      ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)],
        ∀ L : Finset (Zahl.HLine (ZMod p)),
          (L.card : ℝ) ≤ c * (p : ℝ) ^ 2 →
          ∀ A : ℝ, C * Real.sqrt (L.card : ℝ) ≤ A →
            (Zahl.richCount (Zahl.chartImage L) 2 : ℝ) ≤ C * A * (L.card : ℝ) ∨
              (∃ normal : Point (Zahl.QuadraticExtension (ZMod p)), normal ≠ 0 ∧
                ∃ offset : Zahl.QuadraticExtension (ZMod p),
                  A ≤ (((Zahl.chartImage L).filter (Zahl.planeContains normal offset)).card : ℝ)) ∨
              ∃ Q : Zahl.SplitQuadric (Zahl.QuadraticExtension (ZMod p)),
                A ≤ (((Zahl.chartImage L).filter (Zahl.quadricContains Q)).card : ℝ) := by
  obtain ⟨c, C, hc, hc1, hC, h⟩ :=
    Relative.GuthZahl.guthZahl_positive_chart_structure hRaw
  refine ⟨c, C, hc, hc1, (by norm_num : (1 : ℝ) ≤ 5).trans hC, ?_⟩
  intro p hp hmod L hsize A hA
  -- Match the equality instance used in the definition of `chartImage`.
  let : DecidableEq (ZMod p) := Classical.decEq _
  have h2 : (2 : Zahl.QuadraticExtension (ZMod p)) ≠ 0 := by
    intro hz
    have hdiv : p ∣ 2 :=
      (CharP.cast_eq_zero_iff (Zahl.QuadraticExtension (ZMod p)) p 2).mp hz
    have hle := Nat.le_of_dvd (by decide : 0 < 2) hdiv
    have hmod3 : p % 4 = 3 := Fact.out
    omega
  have hcardNat : (Zahl.chartImage L).card ≤ L.card := by
    unfold Zahl.chartImage
    exact Finset.card_image_le
  have hcard : ((Zahl.chartImage L).card : ℝ) ≤ (L.card : ℝ) :=
    Nat.cast_le.mpr hcardNat
  have hC0 : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 5).trans hC
  have hA0 : 0 ≤ A := (mul_nonneg hC0 (Real.sqrt_nonneg _)).trans hA
  have hs : ((Zahl.chartImage L).card : ℝ) ≤ c * (p : ℝ) ^ 2 := hcard.trans hsize
  have ha : C * Real.sqrt ((Zahl.chartImage L).card : ℝ) ≤ A :=
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcard) hC0).trans hA
  rcases h p (Zahl.QuadraticExtension (ZMod p)) h2 (Zahl.chartImage L) hs A ha with
    hcount | hstructure
  · exact Or.inl (hcount.trans (mul_le_mul_of_nonneg_left hcard (mul_nonneg hC0 hA0)))
  · exact Or.inr hstructure

end ExplicitRIP.GuthZahl

end
