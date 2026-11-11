/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Components.Defs
public import ExplicitRIP.GuthZahl.Contagion.Defs
import ExplicitRIP.GuthZahl.CommonLines
import ExplicitRIP.GuthZahl.Basic.Restriction
import ExplicitRIP.GuthZahl.Components.CommonLineCounts.PairSum

/-!
# Common-line counts in the Guth–Zahl component argument

A discrepancy between the line and surface generic patterns supplies a polynomial
relatively prime to the surface equation. Summing the common-surface bound controls
all such lines. Summing the same bound over distinct factor pairs controls lines
contained in multiple factors.
-/

public section

namespace ExplicitRIP.GuthZahl

open Classical in
/-- A different line pattern must add a zero test not divisible by f. The common-surface line
bound controls the union of all such exceptional lines. -/
theorem surface_exceptional_lines_bound {K : Type*} [Field K] [IsAlgClosed K]
    {J : ℕ} (f : Poly K) (hf : Irreducible f) (qs : Fin J → Poly K)
    (Ls : Finset (Line K)) (hLs : ∀ L ∈ Ls, LineOn f L) :
    (Ls.filter (fun L => lineGenericPattern qs L ≠ surfaceGenericPattern f qs)).card ≤
      2 * f.totalDegree * ∑ j, (qs j).totalDegree := by
  classical
  let E : Fin J → Finset (Line K) :=
    fun j => Ls.filter (fun L => ¬ f ∣ qs j ∧ LineOn (qs j) L)
  have hcover :
      Ls.filter (fun L => lineGenericPattern qs L ≠ surfaceGenericPattern f qs) ⊆
        Finset.univ.biUnion E := by
    intro L hL
    obtain ⟨hL, hpattern⟩ := Finset.mem_filter.mp hL
    apply Finset.mem_biUnion.mpr
    by_contra hnone
    apply hpattern
    funext j
    change decide (LineOn (qs j) L) = decide (f ∣ qs j)
    apply Bool.decide_congr
    constructor
    · intro hq
      by_contra hndvd
      exact hnone ⟨j, Finset.mem_univ j, Finset.mem_filter.mpr ⟨hL, hndvd, hq⟩⟩
    · intro hdvd
      exact lineOn_of_dvd hdvd (hLs L hL)
  have hbound (j : Fin J) : (E j).card ≤ 2 * f.totalDegree * (qs j).totalDegree := by
    by_cases hdvd : f ∣ qs j
    · have hE : E j = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro L _ h
        exact h.1 hdvd
      simp only [hE, Finset.card_empty, Nat.zero_le]
    · have hq : qs j ≠ 0 := by
        intro hzero
        apply hdvd
        rw [hzero]
        exact dvd_zero f
      apply common_surface_lines_bound f (qs j) hf.ne_zero hq
        (hf.isRelPrime_iff_not_dvd.mpr hdvd) (E j)
      intro L hL
      obtain ⟨hL, _, hqL⟩ := Finset.mem_filter.mp hL
      exact ⟨hLs L hL, hqL⟩
  calc
    _ ≤ (Finset.univ.biUnion E).card := Finset.card_le_card hcover
    _ ≤ ∑ j, (E j).card := Finset.card_biUnion_le
    _ ≤ ∑ j, 2 * f.totalDegree * (qs j).totalDegree :=
      Finset.sum_le_sum fun j _ => hbound j
    _ = 2 * f.totalDegree * ∑ j, (qs j).totalDegree := (Finset.mul_sum _ _ _).symm

open Classical in
/-- Lines contained in more than one irreducible factor number at most the square of the total
degree. -/
theorem multiply_contained_lines_bound {K : Type*} [Field K] [IsAlgClosed K]
    {m : ℕ} (Ls : Finset (Line K)) (F : Fin m → Poly K)
    (hne : ∀ i, F i ≠ 0) (hcop : ∀ i j, i ≠ j → IsRelPrime (F i) (F j)) :
    (multipleFactorLines Ls F).card ≤ (∑ i, (F i).totalDegree) ^ 2 := by
  classical
  let E : Fin m → Fin m → Finset (Line K) :=
    fun i j => Ls.filter (fun L => LineOn (F i) L ∧ LineOn (F j) L)
  have hcover : multipleFactorLines Ls F ⊆
      Finset.univ.biUnion (fun i => (Finset.univ.filter (fun j => i < j)).biUnion (E i)) := by
    intro L hL
    obtain ⟨hL, i, j, hij, hi, hj⟩ := Finset.mem_filter.mp hL
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact ⟨i, j, hlt, Finset.mem_filter.mpr ⟨hL, hi, hj⟩⟩
    · exact ⟨j, i, hgt, Finset.mem_filter.mpr ⟨hL, hj, hi⟩⟩
  calc
    _ ≤ (Finset.univ.biUnion
        (fun i => (Finset.univ.filter (fun j => i < j)).biUnion (E i))).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ i, ((Finset.univ.filter (fun j => i < j)).biUnion (E i)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ i, ∑ j ∈ Finset.univ with i < j,
        2 * (F i).totalDegree * (F j).totalDegree := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.card_biUnion_le.trans
      apply Finset.sum_le_sum
      intro j hj
      apply common_surface_lines_bound (F i) (F j) (hne i) (hne j)
        (hcop i j (ne_of_lt (Finset.mem_filter.mp hj).2)) (E i j)
      intro L hL
      exact (Finset.mem_filter.mp hL).2
    _ ≤ (∑ i, (F i).totalDegree) ^ 2 :=
      Components.CommonLineCounts.sum_pair_bounds_le_sq_sum Finset.univ
        (fun i => (F i).totalDegree)

end ExplicitRIP.GuthZahl

end
