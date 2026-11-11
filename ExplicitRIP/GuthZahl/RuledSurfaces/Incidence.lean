/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Basic.Restriction

/-!
# Incidence consequences of complementary rulings

Intersecting distinct affine lines are coplanar. Consequently, a family of
pairwise noncoplanar lines has at most one member through any point, and two
such families have at most two members through any point.
-/

public section

namespace ExplicitRIP.GuthZahl.RuledSurfaces

variable {K : Type*} [Field K]

/-- Coplanarity is symmetric. -/
theorem coplanar_comm (L M : Line K) : Coplanar L M ↔ Coplanar M L := by
  constructor <;> rintro ⟨P, hP, hL, hM⟩ <;> exact ⟨P, hP, hM, hL⟩

/-- Two distinct lines through the same point span an affine plane. -/
theorem coplanar_of_mem_of_ne {L M : Line K} {x : Point K}
    (hxL : x ∈ L.1) (hxM : x ∈ M.1) (hLM : L ≠ M) : Coplanar L M := by
  refine ⟨L.1 ⊔ M.1, ?_, le_sup_left, le_sup_right⟩
  rw [AffineSubspace.direction_sup_eq_sup_direction hxL hxM]
  have hupper := Submodule.finrank_sup_add_finrank_inf_eq L.1.direction M.1.direction
  rw [L.2, M.2] at hupper
  have hlt : L.1.direction < L.1.direction ⊔ M.1.direction := by
    apply lt_of_le_of_ne le_sup_left
    intro heq
    have hML : M.1.direction ≤ L.1.direction := heq ▸ le_sup_right
    have heqLine : M = L := line_eq_of_le
      (AffineSubspace.le_of_direction_le hML ⟨x, hxM, hxL⟩)
    exact hLM heqLine.symm
  have hlower := Submodule.finrank_lt_finrank_of_lt hlt
  rw [L.2] at hlower
  omega

/-- A point belongs to at most one member of a pairwise noncoplanar family. -/
theorem card_le_one_of_pairwise_not_coplanar (R : Set (Line K))
    (hR : ∀ L ∈ R, ∀ M ∈ R, L ≠ M → ¬ Coplanar L M)
    (x : Point K) (Ls : Finset (Line K))
    (hLs : ∀ L ∈ Ls, x ∈ L.1 ∧ L ∈ R) : Ls.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro L hL M hM
  by_contra hne
  exact hR L (hLs L hL).2 M (hLs M hM).2 hne
    (coplanar_of_mem_of_ne (hLs L hL).1 (hLs M hM).1 hne)

/-- Two pairwise noncoplanar families contribute at most two lines through a point. -/
theorem card_le_two_of_two_skew_families (R S : Set (Line K))
    (hR : ∀ L ∈ R, ∀ M ∈ R, L ≠ M → ¬ Coplanar L M)
    (hS : ∀ L ∈ S, ∀ M ∈ S, L ≠ M → ¬ Coplanar L M)
    (x : Point K) (Ls : Finset (Line K))
    (hLs : ∀ L ∈ Ls, x ∈ L.1 ∧ (L ∈ R ∨ L ∈ S)) : Ls.card ≤ 2 := by
  classical
  have hfirst : (Ls.filter (fun L => L ∈ R)).card ≤ 1 := by
    apply card_le_one_of_pairwise_not_coplanar R hR x
    intro L hL
    obtain ⟨hL, hLR⟩ := Finset.mem_filter.mp hL
    exact ⟨(hLs L hL).1, hLR⟩
  have hsecond : (Ls.filter (fun L => L ∉ R)).card ≤ 1 := by
    apply card_le_one_of_pairwise_not_coplanar S hS x
    intro L hL
    obtain ⟨hL, hLR⟩ := Finset.mem_filter.mp hL
    exact ⟨(hLs L hL).1, (hLs L hL).2.resolve_left hLR⟩
  have hcard := Finset.card_filter_add_card_filter_not (s := Ls) (p := fun L => L ∈ R)
  omega

end ExplicitRIP.GuthZahl.RuledSurfaces
end
