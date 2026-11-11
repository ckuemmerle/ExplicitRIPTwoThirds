/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Frozen.Defs.InducedEdgeCount

/-!
# Finite edge counting

Elementary counting lemmas for conic removal and pencil summation in density estimates for the
Hermitian norm-graph selection. Constants are intentionally not optimized.
-/

public section
namespace ExplicitRIP.Edges

open Finset
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

@[simp] theorem inducedEdgeCount_empty : inducedEdgeCount G ∅ = 0 := by
  simp [inducedEdgeCount]

theorem inducedEdgeCount_le_sq (U : Finset V) : inducedEdgeCount G U ≤ U.card ^ 2 := by
  unfold inducedEdgeCount
  apply (card_filter_le _ _).trans
  rw [sym2_eq_image]
  exact card_image_le.trans (by rw [card_product, pow_two])

theorem inducedEdgeCount_eq_zero (U : Finset V)
    (h : ∀ x ∈ U, ∀ y ∈ U, ¬G.Adj x y) : inducedEdgeCount G U = 0 := by
  unfold inducedEdgeCount
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨x, y⟩ := e
  obtain ⟨he, hadj⟩ := mem_filter.mp he
  obtain ⟨hx, hy⟩ := mk_mem_sym2_iff.mp he
  exact h x hx y hy hadj

/-- Splitting the vertex set costs at most its cross edges. -/
theorem inducedEdgeCount_union_le (A B : Finset V) :
    inducedEdgeCount G (A ∪ B) ≤ inducedEdgeCount G A + inducedEdgeCount G B +
      ((A ×ˢ B).filter (fun q => G.Adj q.1 q.2)).card := by
  let E (U : Finset V) := U.sym2.filter (fun e => e ∈ G.edgeSet)
  let X := ((A ×ˢ B).filter (fun q => G.Adj q.1 q.2)).image (fun q => s(q.1, q.2))
  have hsub : E (A ∪ B) ⊆ E A ∪ E B ∪ X := by
    intro e he
    obtain ⟨x, y⟩ := e
    obtain ⟨he, hadj⟩ := mem_filter.mp he
    obtain ⟨hx, hy⟩ := mk_mem_sym2_iff.mp he
    rcases mem_union.mp hx with hx | hx <;> rcases mem_union.mp hy with hy | hy
    · exact mem_union_left _ (mem_union_left _
        (mem_filter.mpr ⟨mk_mem_sym2_iff.mpr ⟨hx, hy⟩, hadj⟩))
    · exact mem_union_right _ (mem_image.mpr ⟨(x, y),
        mem_filter.mpr ⟨mem_product.mpr ⟨hx, hy⟩, hadj⟩, rfl⟩)
    · apply mem_union_right
      exact mem_image.mpr ⟨(y, x), mem_filter.mpr
        ⟨mem_product.mpr ⟨hy, hx⟩, (show G.Adj x y from hadj).symm⟩, Sym2.eq_swap⟩
    · exact mem_union_left _ (mem_union_right _
        (mem_filter.mpr ⟨mk_mem_sym2_iff.mpr ⟨hx, hy⟩, hadj⟩))
  exact (card_le_card hsub).trans ((card_union_le _ _).trans
    (Nat.add_le_add (card_union_le _ _) card_image_le))

omit [DecidableEq V] in
theorem cross_card_eq_sum (A B : Finset V) :
    ((A ×ˢ B).filter (fun q => G.Adj q.1 q.2)).card =
      ∑ y ∈ B, (A.filter (fun x => G.Adj x y)).card := by
  simp only [card_eq_sum_ones, sum_filter, sum_product]
  exact sum_comm

end ExplicitRIP.Edges
