/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Boundary.Defs
import ExplicitRIP.GuthZahl.Boundary.Descent
import ExplicitRIP.GuthZahl.Boundary.Translations

/-!
# Cardinality bounds after plane and quadric descent

A selected family of extended chart lines comes from a subfamily over the original field. The
geometric descent lemmas preserve every selected line, so their lower cardinality bounds descend as
well. These lemmas are unconditional; they serve the conditional results of
`ExplicitRIP/Relative/GuthZahl/Boundary.lean`.
-/

public section

namespace ExplicitRIP.Relative.GuthZahl.Boundary

open ExplicitRIP.GuthZahl
open ExplicitRIP.Zahl (ChartLine)

open Classical in
theorem mapChartFamily_filter_card {F K : Type*} [Field F] [Field K]
    (φ : F →+* K) (L : Finset (ChartLine F)) (P : ChartLine K → Prop) :
    ((mapChartFamily φ L).filter P).card =
      (L.filter (fun l => P (mapChart φ l))).card := by
  rw [mapChartFamily, Finset.filter_image]
  exact mapChartFamily_card φ _

open Classical in
theorem plane_filter_descends {F K : Type*} [Field F] [Field K]
    (φ : F →+* K) (L : Finset (ChartLine F)) (A : ℝ) (hA : 2 ≤ A)
    (normal : Point K) (hn : normal ≠ 0) (offset : K)
    (hcard : A ≤ (((mapChartFamily φ L).filter
      (Zahl.planeContains normal offset)).card : ℝ)) :
    ∃ n : Point F, n ≠ 0 ∧ ∃ b : F,
      A ≤ ((L.filter (Zahl.planeContains n b)).card : ℝ) := by
  let S := L.filter (fun l => Zahl.planeContains normal offset (mapChart φ l))
  have hS : A ≤ (S.card : ℝ) := by
    simpa only [mapChartFamily_filter_card] using hcard
  have htwo : 2 ≤ S.card := by exact_mod_cast hA.trans hS
  obtain ⟨n, hn, b, hplane⟩ := plane_family_descends φ S htwo normal hn offset
    (fun l hl => (Finset.mem_filter.mp hl).2)
  refine ⟨n, hn, b, hS.trans ?_⟩
  exact_mod_cast Finset.card_le_card (show S ⊆ L.filter (Zahl.planeContains n b) from
    fun l hl => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hl).1, hplane l hl⟩)

open Classical in
theorem quadric_filter_descends {F K : Type*} [Field F] [Field K]
    (φ : F →+* K) (h2 : (2 : F) ≠ 0) (L : Finset (ChartLine F))
    (A : ℝ) (hA : 5 ≤ A) (Q : Zahl.SplitQuadric K)
    (hcard : A ≤ (((mapChartFamily φ L).filter (Zahl.quadricContains Q)).card : ℝ)) :
    ∃ Q₀ : Zahl.SplitQuadric F,
      A ≤ ((L.filter (Zahl.quadricContains Q₀)).card : ℝ) := by
  let S := L.filter (fun l => Zahl.quadricContains Q (mapChart φ l))
  have hS : A ≤ (S.card : ℝ) := by
    simpa only [mapChartFamily_filter_card] using hcard
  have hfive : 5 ≤ S.card := by exact_mod_cast hA.trans hS
  obtain ⟨Q₀, hquadric⟩ := quadric_family_descends φ h2 S hfive Q
    (fun l hl => (Finset.mem_filter.mp hl).2)
  refine ⟨Q₀, hS.trans ?_⟩
  exact_mod_cast Finset.card_le_card (show S ⊆ L.filter (Zahl.quadricContains Q₀) from
    fun l hl => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hl).1, hquadric l hl⟩)

end ExplicitRIP.Relative.GuthZahl.Boundary

end
