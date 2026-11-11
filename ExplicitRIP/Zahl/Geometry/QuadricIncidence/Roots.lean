/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Geometry.Lines

/-!
# Intersection of a line with a split quadric

The restriction polynomial bounds the finite intersection of a noncontained
line with the quadric by two points.
-/

public section

namespace ExplicitRIP.Zahl

open Polynomial

/-- A line outside a split quadric meets it in at most two points. -/
theorem quadric_intersection_ncard_le_two {K : Type*} [Field K]
    (Q : SplitQuadric K) (l : ChartLine K) (hl : ¬ quadricContains Q l) :
    (linePoints l ∩ {w | quadricValue Q w = 0}).Finite ∧
      (linePoints l ∩ {w | quadricValue Q w = 0}).ncard ≤ 2 := by
  classical
  let p := quadricRestriction Q l
  obtain ⟨hdeg, heval⟩ := quadricRestriction_spec Q l
  have hp : p ≠ 0 := by
    intro hzero
    apply hl
    rintro w ⟨x, rfl⟩
    rw [← heval x]
    change p.eval x = 0
    rw [hzero, eval_zero]
  have hset : linePoints l ∩ {w | quadricValue Q w = 0} =
      linePoint l '' (p.roots.toFinset : Set K) := by
    ext w
    constructor
    · rintro ⟨⟨x, rfl⟩, hx⟩
      refine ⟨x, ?_, rfl⟩
      apply Multiset.mem_toFinset.mpr
      apply (mem_roots hp).mpr
      exact (heval x).trans hx
    · rintro ⟨x, hx, rfl⟩
      refine ⟨linePoint_mem_linePoints l x, ?_⟩
      exact (heval x).symm.trans ((mem_roots hp).mp (Multiset.mem_toFinset.mp hx))
  rw [hset]
  refine ⟨p.roots.toFinset.finite_toSet.image (linePoint l), ?_⟩
  calc
    (linePoint l '' (p.roots.toFinset : Set K)).ncard ≤
        (p.roots.toFinset : Set K).ncard := Set.ncard_image_le p.roots.toFinset.finite_toSet
    _ = p.roots.toFinset.card := Set.ncard_coe_finset _
    _ ≤ p.roots.card := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := card_roots' p
    _ ≤ 2 := hdeg

end ExplicitRIP.Zahl
