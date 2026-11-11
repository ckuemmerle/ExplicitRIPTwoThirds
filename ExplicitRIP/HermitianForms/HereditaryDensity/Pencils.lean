/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.HermitianForms.HereditaryDensity.Quadratic
public import ExplicitRIP.Frozen.Defs.IsContactPencil
public import ExplicitRIP.HermitianForms.Anchors.LineConicAvoidance

/-!
# Contact pencils and line avoidance

A distinct contacting pair determines its unique pencil, as in [KM, Section 4.1]. The
selected-point bound applies the norm-graph line estimate of [KM, Lemma 7(a)] in Hermitian
coordinates and transports it to sphere coordinates.
-/

public section
namespace ExplicitRIP.Edges

variable (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]

/-- A common neighbor of an adjacent pair lies on their affine line. -/
theorem mem_lineSet_of_adj {x y z : V4 (ZMod p)}
    (hxy : (hermitianGraph p).Adj x y) (hxz : (hermitianGraph p).Adj x z)
    (hyz : (hermitianGraph p).Adj y z) : z ∈ lineSet x y := by
  classical
  let D : Finset (ZMod p) := Finset.univ.filter (fun t => t ≠ 0 ∧ t ≠ 1)
  let f : ZMod p → V4 (ZMod p) := fun t => x + t • (y - x)
  have hf : Function.Injective f := by
    intro s t hst
    exact smul_left_injective (ZMod p) (sub_ne_zero.mpr hxy.ne.symm) (add_left_cancel hst)
  have hq : Hfsrg.quad p (y - x) = 0 := by
    rw [Hfsrg.quad_sub_comm]
    exact ((Hfsrg.adj_iff p x y).mp hxy).2
  have hsmul (t : ZMod p) (v : V4 (ZMod p)) :
      Hfsrg.quad p (t • v) = t ^ 2 * Hfsrg.quad p v := by
    dsimp [Hfsrg.quad]; ring
  have hsub : (↑(D.image f) : Set (V4 (ZMod p))) ⊆ (hermitianGraph p).commonNeighbors x y := by
    intro v hv
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hv
    have ht' := (Finset.mem_filter.mp ht).2
    rw [SimpleGraph.mem_commonNeighbors, Hfsrg.adj_iff, Hfsrg.adj_iff]
    have hfx : f 0 = x := by simp [f]
    have hfy : f 1 = y := by simp [f]
    have he1 : x - f t = (-t) • (y - x) := by dsimp [f]; module
    have he2 : y - f t = (1 - t) • (y - x) := by dsimp [f]; module
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro h
      exact ht'.1 (hf (h.symm.trans hfx.symm))
    · rw [he1, hsmul, hq, mul_zero]
    · intro h
      exact ht'.2 (hf (h.symm.trans hfy.symm))
    · rw [he2, hsmul, hq, mul_zero]
  have hcard : (D.image f).card = p - 2 := by
    rw [Finset.card_image_of_injective _ hf]
    exact (Fintype.card_subtype _).symm.trans (Hfsrg.card_avoid_zero_one p)
  have heq : (↑(D.image f) : Set (V4 (ZMod p))) = (hermitianGraph p).commonNeighbors x y := by
    apply Set.eq_of_subset_of_ncard_le hsub
    rw [Set.ncard_coe_finset, hcard, ← Nat.card_coe_set_eq, Hfsrg.card_common_of_adj p x y hxy]
  have hz : z ∈ D.image f := by
    change z ∈ (↑(D.image f) : Set (V4 (ZMod p)))
    rw [heq]
    exact ⟨hxz, hyz⟩
  obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hz
  exact ⟨t, ht.symm⟩

/-- All common contacts of two distinct contacting parameters lie on their line. -/
theorem mem_lineSet_of_contact {x y z : V4 (ZMod p)} (hne : x ≠ y)
    (hxy : SphereContact x y) (hxz : SphereContact x z) (hyz : SphereContact y z) :
    z ∈ lineSet x y := by
  classical
  by_cases hzx : z = x
  · exact hzx ▸ left_mem_lineSet x y
  by_cases hzy : z = y
  · exact hzy ▸ right_mem_lineSet x y
  let e := LightCone.sphereEquiv p
  have hadj (a b : V4 (ZMod p)) (hab : a ≠ b) (hc : SphereContact a b) :
      (hermitianGraph p).Adj (e.symm a) (e.symm b) := by
    rw [adj_iff_sphereContact]
    exact ⟨e.symm.injective.ne hab, by
      simpa only [← LightCone.sphereEquiv_apply, e, LinearEquiv.apply_symm_apply] using hc⟩
  obtain ⟨t, ht⟩ := mem_lineSet_of_adj p (hadj x y hne hxy)
    (hadj x z (Ne.symm hzx) hxz) (hadj y z (Ne.symm hzy) hyz)
  refine ⟨t, ?_⟩
  have h := congrArg e ht
  simpa only [map_add, map_smul, map_sub, LinearEquiv.apply_symm_apply] using h

/-- The line of a distinct contacting pair is maximal among pairwise-contacting sets. -/
theorem isContactPencil_lineSet {x y : V4 (ZMod p)} (hne : x ≠ y)
    (hxy : SphereContact x y) : IsContactPencil (lineSet x y) := by
  refine ⟨fun _ hz _ hw => contact_of_mem_lineSet hxy hz hw, ?_⟩
  intro z hz h
  apply hz
  apply mem_lineSet_of_contact p hne hxy
  · exact h x (Set.mem_insert_of_mem _ (left_mem_lineSet x y)) z (Set.mem_insert _ _)
  · exact h y (Set.mem_insert_of_mem _ (right_mem_lineSet x y)) z (Set.mem_insert _ _)

theorem pencil_subset_lineSet {P : Set (V4 (ZMod p))} (hP : IsContactPencil P)
    {x y : V4 (ZMod p)} (hx : x ∈ P) (hy : y ∈ P) (hne : x ≠ y) : P ⊆ lineSet x y := by
  intro z hz
  exact mem_lineSet_of_contact p hne (hP.1 x hx y hy) (hP.1 x hx z hz) (hP.1 y hy z hz)

theorem pencil_eq_lineSet {P : Set (V4 (ZMod p))} (hP : IsContactPencil P)
    {x y : V4 (ZMod p)} (hx : x ∈ P) (hy : y ∈ P) (hne : x ≠ y) : P = lineSet x y := by
  apply Set.Subset.antisymm (pencil_subset_lineSet p hP hx hy hne)
  intro z hz
  by_contra hn
  apply hP.2 z hn
  intro a ha b hb
  apply contact_of_mem_lineSet (hP.1 x hx y hy)
  · rcases ha with rfl | ha
    · exact hz
    · exact pencil_subset_lineSet p hP hx hy hne ha
  · rcases hb with rfl | hb
    · exact hz
    · exact pencil_subset_lineSet p hP hx hy hne hb

open Classical in
/-- Pulling a sphere-coordinate line back preserves the selected-point cap. -/
theorem line_cap (T : Finset (ZMod p)) {x y : V4 (ZMod p)} (hne : x ≠ y) :
    ((hermitianSelectedVertices p T).filter (fun v => sphereCoords p v ∈ lineSet x y)).card ≤
      3 * T.card := by
  classical
  let e := LightCone.sphereEquiv p
  apply (Finset.card_le_card ?_).trans ((ExplicitRIP.Hermitian.line_conic_avoidance p T).1
    (e.symm x) (e.symm (y - x)) (by
      simpa only [LinearEquiv.map_ne_zero_iff, sub_ne_zero] using hne.symm))
  intro v hv
  obtain ⟨hv, t, ht⟩ := Finset.mem_filter.mp hv
  refine Finset.mem_filter.mpr ⟨hv, t, ?_⟩
  have h := congrArg e.symm ht
  simpa only [← LightCone.sphereEquiv_apply, e, LinearEquiv.symm_apply_apply,
    map_add, map_smul] using h

end ExplicitRIP.Edges
