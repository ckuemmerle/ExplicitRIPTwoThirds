/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Incidence.Counting.Finite
public import ExplicitRIP.Zahl.Basic.Lie

/-! # Counting rich incidences on a surface -/

public section

namespace ExplicitRIP.Zahl


open Classical in
/-- Rich counts vanish when the requested multiplicity exceeds the family size. -/
lemma richCount_eq_zero_of_card_lt {K : Type*} [CommRing K]
    (L : Finset (ChartLine K)) {k : ℕ} (hk : L.card < k) : richCount L k = 0 := by
  have he : richPoints L k = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro w hw
    exact (not_le_of_gt hk) (hw.trans (Finset.card_filter_le _ _))
  rw [richCount, he, Set.ncard_empty]

open Classical in
/-- Lowering the multiplicity threshold increases the finite rich-point count. -/
lemma richCount_antitone {K : Type*} [Field K]
    (L : Finset (ChartLine K)) {j k : ℕ} (hj : 2 ≤ j) (hjk : j ≤ k) :
    richCount L k ≤ richCount L j :=
  Set.ncard_le_ncard (fun _ hw => hjk.trans hw) (richPoints_finite L j hj)

open Classical in
/-- A surface incidence budget, allowing finitely many exceptional points.
Outside lines meet the surface at most `t` times; away from `E`, at most `b ≤ 2`
contained lines pass through a point. -/
lemma surface_incidence_budget {K : Type*} [Field K]
    (T R : Finset (ChartLine K)) (surface : Set (Point K))
    (E : Finset (Point K)) (b t : ℕ) (hb : b ≤ 2)
    (hcontained : ∀ l ∈ R, linePoints l ⊆ surface)
    (hthrough : ∀ w, w ∉ E → (R.filter (fun l => w ∈ linePoints l)).card ≤ b)
    (houtside : ∀ m ∈ T \ R, (linePoints m ∩ surface).Finite ∧
      (linePoints m ∩ surface).ncard ≤ t) :
    (∑ l ∈ R, (richPoints T 3 ∩ linePoints l).ncard) ≤
      R.card * E.card + b * t * T.card := by
  let P := (richPoints_finite T 3 (by omega)).toFinset.filter
    (fun w => w ∈ surface ∧ w ∉ E)
  have hP (w : Point K) : w ∈ P ↔ w ∈ richPoints T 3 ∧ w ∈ surface ∧ w ∉ E := by
    simp only [P, Finset.mem_filter, Set.Finite.mem_toFinset]
  have hexternal (w : Point K) (hw : w ∈ P) :
      ((T \ R).filter (fun l => w ∈ linePoints l)).Nonempty := by
    obtain ⟨hwT, _, hwE⟩ := (hP w).mp hw
    by_contra hnone
    have hsub : T.filter (fun l => w ∈ linePoints l) ⊆
        R.filter (fun l => w ∈ linePoints l) := by
      intro l hl
      obtain ⟨hlT, hwl⟩ := Finset.mem_filter.mp hl
      have hlR : l ∈ R := by
        by_contra hlR
        exact hnone ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hlT, hlR⟩, hwl⟩⟩
      exact Finset.mem_filter.mpr ⟨hlR, hwl⟩
    have hcard := (Finset.card_le_card hsub).trans ((hthrough w hwE).trans hb)
    change 3 ≤ (T.filter (fun l => w ∈ linePoints l)).card at hwT
    omega
  have hcap (m : ChartLine K) (hm : m ∈ T \ R) :
      (P.filter (fun w => w ∈ linePoints m)).card ≤ t := by
    rw [← Set.ncard_coe_finset]
    apply (Set.ncard_le_ncard ?_ (houtside m hm).1).trans (houtside m hm).2
    intro w hw
    obtain ⟨hwP, hwm⟩ := Finset.mem_filter.mp hw
    exact ⟨hwm, ((hP w).mp hwP).2.1⟩
  have hPcard : P.card ≤ t * T.card := by
    calc
      P.card = ∑ _w ∈ P, 1 := by simp only [Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ ∑ w ∈ P, ((T \ R).filter (fun l => w ∈ linePoints l)).card :=
        Finset.sum_le_sum (fun w hw => Finset.one_le_card.mpr (hexternal w hw))
      _ = ∑ m ∈ T \ R, (P.filter (fun w => w ∈ linePoints m)).card :=
        Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
          (fun w m => w ∈ linePoints m)
      _ ≤ ∑ _m ∈ T \ R, t := Finset.sum_le_sum hcap
      _ = t * (T \ R).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ t * T.card := Nat.mul_le_mul_left t
        (Finset.card_le_card Finset.sdiff_subset)
  have hdegree (l : ChartLine K) (hl : l ∈ R) :
      (richPoints T 3 ∩ linePoints l).ncard ≤
        E.card + (P.filter (fun w => w ∈ linePoints l)).card := by
    have hsub : richPoints T 3 ∩ linePoints l ⊆
        (E : Set (Point K)) ∪ (↑(P.filter (fun w => w ∈ linePoints l)) : Set (Point K)) := by
      intro w hw
      by_cases hwE : w ∈ E
      · exact Or.inl hwE
      · exact Or.inr (Finset.mem_filter.mpr
          ⟨(hP w).mpr ⟨hw.1, hcontained l hl hw.2, hwE⟩, hw.2⟩)
    calc
      _ ≤ ((E : Set (Point K)) ∪
          (↑(P.filter (fun w => w ∈ linePoints l)) : Set (Point K))).ncard :=
        Set.ncard_le_ncard hsub (E.finite_toSet.union (Finset.finite_toSet _))
      _ ≤ _ := by
        simpa only [Set.ncard_coe_finset] using
          Set.ncard_union_le (E : Set (Point K))
            (↑(P.filter (fun w => w ∈ linePoints l)) : Set (Point K))
  calc
    _ ≤ ∑ l ∈ R, (E.card + (P.filter (fun w => w ∈ linePoints l)).card) :=
      Finset.sum_le_sum hdegree
    _ = R.card * E.card + ∑ w ∈ P, (R.filter (fun l => w ∈ linePoints l)).card := by
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
      congr 1
      exact Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (fun l w => w ∈ linePoints l)
    _ ≤ R.card * E.card + ∑ _w ∈ P, b :=
      Nat.add_le_add_left (Finset.sum_le_sum (fun w hw => hthrough w ((hP w).mp hw).2.2)) _
    _ = R.card * E.card + b * P.card := by
      rw [Finset.sum_const, smul_eq_mul, mul_comm P.card b]
    _ ≤ _ := Nat.add_le_add_left
      (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left b hPcard) _

end ExplicitRIP.Zahl
