/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Geometry.Lines

/-!
# Finiteness of rich affine points

Two distinct chart lines have at most one common point. A finite family therefore
has only finitely many points incident to at least two of its lines.
-/

public section

namespace ExplicitRIP.Zahl

/-- Two-rich points have a pair of distinct incident witnesses. -/
theorem mem_richPoints_two_iff {K : Type*} [CommRing K]
    (L : Finset (ChartLine K)) (w : Point K) :
    w ∈ richPoints L 2 ↔
      ∃ l ∈ L, ∃ m ∈ L, l ≠ m ∧ w ∈ linePoints l ∧ w ∈ linePoints m := by
  classical
  change 1 < (L.filter (fun l => w ∈ linePoints l)).card ↔ _
  simp only [Finset.one_lt_card, Finset.mem_filter]
  aesop

/-- Rich-point sets at threshold at least two are finite. -/
theorem richPoints_finite {K : Type*} [Field K]
    (L : Finset (ChartLine K)) (k : ℕ) (hk : 2 ≤ k) :
    (richPoints L k).Finite := by
  classical
  have hf : (⋃ l : ↥L, ⋃ m : {m : ↥L // m ≠ l},
      linePoints l.val ∩ linePoints m.val.val).Finite := by
    apply Set.finite_iUnion
    intro l
    apply Set.finite_iUnion
    intro m
    exact (linePoints_inter_subsingleton (fun h => m.property (Subtype.ext h.symm))).finite
  apply hf.subset
  intro w hw
  have hw₂ : w ∈ richPoints L 2 := le_trans hk hw
  obtain ⟨l, hl, m, hm, hne, hwl, hwm⟩ := (mem_richPoints_two_iff L w).mp hw₂
  exact Set.mem_iUnion.mpr ⟨⟨l, hl⟩, Set.mem_iUnion.mpr
    ⟨⟨⟨m, hm⟩, fun h => hne (congrArg Subtype.val h).symm⟩, hwl, hwm⟩⟩

end ExplicitRIP.Zahl
