/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Contact.NormSelection
public import ExplicitRIP.Frozen.Defs.ContactGraph
public import ExplicitRIP.HermitianForms.HereditaryDensity.PencilCounting
public import ExplicitRIP.HermitianForms.HereditaryDensity.ConicCaps

/-!
# Pencils and conic caps in contact coordinates

Line and conic avoidance apply directly to the norm-graph selection. Every contact edge is
covered by its pencil, so bounded pencil occupancy controls edges by the two-rich pencil count.
-/

public section

open scoped Matrix

namespace ExplicitRIP.Contact.Density

open Finset Edges

variable (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]

theorem adj_iff (x y : V4 (ZMod p)) :
    (contactGraph p).Adj x y ↔ x ≠ y ∧ SphereContact x y := by
  rw [contact_iff]
  change (x ≠ y ∧ (mq (x - y) = 0 ∨ mq (y - x) = 0)) ↔ _
  rw [mq_sub_comm y x, or_self]

open Classical in
/-- A complementary conic contains at most six points per norm-graph translate. -/
theorem conic_cap (T : Finset (ZMod p)) {A B : Set (V4 (ZMod p))}
    (h : IsComplementaryConicPair A B) :
    ((selectedVertices p T).filter (· ∈ A)).card ≤ 6 * T.card := by
  classical
  obtain ⟨x₀, u, w, hlin, g, hg, hdeg, hparam⟩ := Edges.conic_param p h
  apply (card_le_card ?_).trans
    ((Hermitian.line_conic_avoidance p T).2 x₀ u w hlin g hg hdeg)
  intro x hx
  obtain ⟨hx, hxA⟩ := mem_filter.mp hx
  exact mem_filter.mpr ⟨hx, hparam x hxA⟩

open Classical in
theorem pencil_cap (T : Finset (ZMod p)) (V : Finset (V4 (ZMod p)))
    (hV : V ⊆ selectedVertices p T) {P : Set (V4 (ZMod p))}
    (hP : P ∈ pencilFamily V) : (V.filter (· ∈ P)).card ≤ 3 * T.card := by
  classical
  obtain ⟨hPc, hcard⟩ := (mem_pencilFamily _ _).mp hP
  obtain ⟨x, hx, y, hy, hxy⟩ := one_lt_card.mp (by omega : 1 < (V.filter (· ∈ P)).card)
  have hsub := pencil_subset_lineSet p hPc (mem_filter.mp hx).2 (mem_filter.mp hy).2 hxy
  apply (card_le_card ?_).trans
    ((Hermitian.line_conic_avoidance p T).1 x (y - x) (sub_ne_zero.mpr hxy.symm))
  intro z hz
  exact mem_filter.mpr ⟨hV (mem_filter.mp hz).1, hsub (mem_filter.mp hz).2⟩

open Classical in
/-- Covering contact edges by their pencils gives an elementary squared-occupancy bound. -/
theorem edge_count_le_sum_pencil_sq (V : Finset (V4 (ZMod p))) :
    inducedEdgeCount (contactGraph p) V ≤
      ∑ P ∈ pencilFamily V, ((V.filter (· ∈ P)).card) ^ 2 := by
  classical
  let Ps := pencilFamily V
  let pieces (P : Set (V4 (ZMod p))) := (V.filter (· ∈ P)).sym2
  have hcover : V.sym2.filter (fun e => e ∈ (contactGraph p).edgeSet) ⊆ Ps.biUnion pieces := by
    intro e he
    obtain ⟨x, y⟩ := e
    obtain ⟨hmem, hadj⟩ := mem_filter.mp he
    obtain ⟨hx, hy⟩ := mk_mem_sym2_iff.mp hmem
    have ha := (adj_iff p x y).mp hadj
    let P := lineSet x y
    have hP : P ∈ Ps := by
      apply (mem_pencilFamily _ _).mpr
      refine ⟨isContactPencil_lineSet p ha.1 ha.2, ?_⟩
      apply Nat.succ_le_of_lt
      apply one_lt_card.mpr
      exact ⟨x, mem_filter.mpr ⟨hx, left_mem_lineSet _ _⟩,
        y, mem_filter.mpr ⟨hy, right_mem_lineSet _ _⟩, ha.1⟩
    exact mem_biUnion.mpr ⟨P, hP, mk_mem_sym2_iff.mpr
      ⟨mem_filter.mpr ⟨hx, left_mem_lineSet _ _⟩,
        mem_filter.mpr ⟨hy, right_mem_lineSet _ _⟩⟩⟩
  apply (card_le_card hcover).trans
  apply card_biUnion_le.trans
  apply sum_le_sum
  intro P _
  dsimp only [pieces]
  rw [sym2_eq_image]
  exact card_image_le.trans (by rw [card_product, pow_two])

open Classical in
/-- Two translates put at most six selected points on any pencil. -/
theorem edge_count_le_rich_two (T : Finset (ZMod p)) (hT : T.card ≤ 2)
    (V : Finset (V4 (ZMod p))) (hV : V ⊆ selectedVertices p T) :
    inducedEdgeCount (contactGraph p) V ≤ 36 * richPencilCount V 2 := by
  classical
  calc
    _ ≤ ∑ P ∈ pencilFamily V, ((V.filter (· ∈ P)).card) ^ 2 :=
      edge_count_le_sum_pencil_sq p V
    _ ≤ ∑ _P ∈ pencilFamily V, 36 := by
      apply sum_le_sum
      intro P hP
      have hcap := (pencil_cap p T V hV hP).trans (Nat.mul_le_mul_left 3 hT)
      nlinarith only [hcap]
    _ = 36 * richPencilCount V 2 := by
      rw [sum_const, smul_eq_mul, pencilFamily_card, Nat.mul_comm]

end ExplicitRIP.Contact.Density
