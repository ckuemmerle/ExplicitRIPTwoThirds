/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.RuledSurfaces.Incidence

/-!
# Coplanarity and affine intersections

These lemmas keep parallel lines in the coplanarity relation and separate that
case from an actual affine intersection. They also provide the finite pairwise
intersection fact used when excluding concurrent triples.
-/

public section

namespace ExplicitRIP.GuthZahl.RuledSurfaces

variable {K : Type*} [Field K]

/-- A nonzero linear functional on three-dimensional affine space has a two-dimensional kernel. -/
theorem finrank_ker_eq_two {φ : Point K →ₗ[K] K} (hφ : φ ≠ 0) :
    Module.finrank K (LinearMap.ker φ) = 2 := by
  have hsurj := surjective_of_nonzero_of_finrank_eq_one (Module.finrank_self K) hφ
  have hdim := LinearMap.finrank_range_add_finrank_ker φ
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self] at hdim
  have hpoint : Module.finrank K (Point K) = 3 := by
    simp only [Point, Module.finrank_pi, Fintype.card_fin]
  rw [hpoint] at hdim
  exact Nat.add_left_cancel hdim

/-- A nonempty affine subspace of dimension at most two is contained in a plane. -/
theorem exists_plane_of_finrank_direction_le_two (S : AffineSubspace K (Point K))
    (hS : (S : Set (Point K)).Nonempty) (hdim : Module.finrank K S.direction ≤ 2) :
    ∃ P : AffineSubspace K (Point K), Module.finrank K P.direction = 2 ∧ S ≤ P := by
  have hproper : S.direction < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro htop
    rw [htop, finrank_top] at hdim
    have hpoint : Module.finrank K (Point K) = 3 := by
      simp only [Point, Module.finrank_pi, Fintype.card_fin]
    rw [hpoint] at hdim
    omega
  obtain ⟨φ, hφ, hker⟩ := S.direction.exists_le_ker_of_lt_top hproper
  obtain ⟨a, ha⟩ := hS
  refine ⟨AffineSubspace.mk' a (LinearMap.ker φ), ?_, ?_⟩
  · rw [AffineSubspace.direction_mk']
    exact finrank_ker_eq_two hφ
  · intro x hx
    apply AffineSubspace.mem_mk'.2
    exact hker (AffineSubspace.vsub_mem_direction hx ha)

/-- A bound on the dimension of the affine span implies coplanarity. -/
theorem coplanar_of_finrank_sup_le_two (L M : Line K)
    (h : Module.finrank K (L.1 ⊔ M.1).direction ≤ 2) : Coplanar L M := by
  obtain ⟨a, ha⟩ := line_nonempty L
  obtain ⟨P, hP, hle⟩ := exists_plane_of_finrank_direction_le_two (L.1 ⊔ M.1)
    ⟨a, (le_sup_left : L.1 ≤ L.1 ⊔ M.1) ha⟩ h
  exact ⟨P, hP, le_trans le_sup_left hle, le_trans le_sup_right hle⟩

/-- Parallel affine lines are coplanar. -/
theorem coplanar_of_direction_eq {L M : Line K} (hdir : L.1.direction = M.1.direction) :
    Coplanar L M := by
  apply coplanar_of_finrank_sup_le_two
  obtain ⟨a, ha⟩ := line_nonempty L
  obtain ⟨b, hb⟩ := line_nonempty M
  rw [AffineSubspace.direction_sup ha hb, ← hdir, sup_idem]
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq L.1.direction
    (Submodule.span K {b -ᵥ a})
  have hspan : Module.finrank K (Submodule.span K {b -ᵥ a}) ≤ 1 := by
    simpa only [Set.ncard_singleton] using
      finrank_span_le_ncard ({b -ᵥ a} : Set (Point K)) (Set.finite_singleton _)
  rw [L.2] at hdim
  omega

/-- A line is coplanar with itself. -/
theorem coplanar_self (L : Line K) : Coplanar L L := coplanar_of_direction_eq rfl

/-- Skew lines are distinct. -/
theorem ne_of_not_coplanar {L M : Line K} (h : ¬ Coplanar L M) : L ≠ M := by
  rintro rfl
  exact h (coplanar_self L)

/-- Skew lines have different directions. -/
theorem direction_ne_of_not_coplanar {L M : Line K} (h : ¬ Coplanar L M) :
    L.1.direction ≠ M.1.direction := fun heq => h (coplanar_of_direction_eq heq)

/-- Coplanar affine lines either meet or have the same direction. -/
theorem inter_nonempty_or_direction_eq_of_coplanar {L M : Line K} (hLM : Coplanar L M) :
    ((L.1 : Set (Point K)) ∩ M.1).Nonempty ∨ L.1.direction = M.1.direction := by
  by_cases hdir : L.1.direction = M.1.direction
  · exact Or.inr hdir
  left
  obtain ⟨P, hP, hLP, hMP⟩ := hLM
  have hsup : L.1.direction ⊔ M.1.direction ≤ P.direction :=
    sup_le (AffineSubspace.direction_le hLP) (AffineSubspace.direction_le hMP)
  have hlt : L.1.direction < L.1.direction ⊔ M.1.direction := by
    apply lt_of_le_of_ne le_sup_left
    intro heq
    have hML : M.1.direction ≤ L.1.direction := heq ▸ le_sup_right
    exact hdir (Submodule.eq_of_le_of_finrank_eq hML (M.2.trans L.2.symm)).symm
  have hlo := Submodule.finrank_lt_finrank_of_lt hlt
  have hhi := Submodule.finrank_mono hsup
  rw [L.2] at hlo
  rw [hP] at hhi
  have heq : L.1.direction ⊔ M.1.direction = P.direction :=
    Submodule.eq_of_le_of_finrank_eq hsup (by omega)
  obtain ⟨a, ha⟩ := line_nonempty L
  obtain ⟨b, hb⟩ := line_nonempty M
  have hab : b -ᵥ a ∈ L.1.direction ⊔ M.1.direction := by
    rw [heq]
    exact AffineSubspace.vsub_mem_direction (hMP hb) (hLP ha)
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hab
  refine ⟨u +ᵥ a, AffineSubspace.vadd_mem_of_mem_direction hu ha, ?_⟩
  have hpoint : u +ᵥ a = (-v) +ᵥ b := by
    change u + v = b - a at huv
    change u + a = -v + b
    linear_combination huv
  rw [hpoint]
  exact AffineSubspace.vadd_mem_of_mem_direction (M.1.direction.neg_mem hv) hb

end ExplicitRIP.GuthZahl.RuledSurfaces
end
