/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Contact.HereditaryDensity.TwoTranslates

/-!
# Hereditary density of the norm-graph selection

Partition a selected set by its translate labels and cover its edges by pairs of parts. Each
pair satisfies the two-translate estimate. Its cardinality to the power three halves is at most
its cardinality times the square root of the whole set's cardinality. Summing ordered pairs costs
at most twice the number of translates times the whole cardinality.
-/

public section

namespace ExplicitRIP.Contact.Density

open Finset Edges

theorem hereditary_density :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)], ∀ T : Finset (ZMod p),
      ∀ U ⊆ selectedVertices p T, U.card ≤ p ^ 2 →
        (open Classical in (inducedEdgeCount (contactGraph p) U : ℝ)) ≤
          C * T.card * (U.card : ℝ) ^ (3 / 2 : ℝ) := by
  classical
  obtain ⟨C, hC, htwo⟩ := two_translate_density
  refine ⟨2 * C, by positivity, fun p _ _ T U hU hsize => ?_⟩
  let part (t : ZMod p) := U.filter (fun x => translateLabel p x = t)
  let W (q : ZMod p × ZMod p) := part q.1 ∪ part q.2
  let E (V : Finset (V4 (ZMod p))) := V.sym2.filter (fun e => e ∈ (contactGraph p).edgeSet)
  have hlabel (x : V4 (ZMod p)) (hx : x ∈ U) : translateLabel p x ∈ T :=
    (mem_selectedVertices_iff p T x).mp (hU hx)
  have hpart : ∑ t ∈ T, (part t).card = U.card :=
    (card_eq_sum_card_fiberwise hlabel).symm
  have hWsub (q : ZMod p × ZMod p) : W q ⊆ U :=
    union_subset (filter_subset _ _) (filter_subset _ _)
  have hWcard (q : ZMod p × ZMod p) : (W q).card ≤ U.card := card_le_card (hWsub q)
  have hcover : E U ⊆ (T ×ˢ T).biUnion (fun q => E (W q)) := by
    intro e he
    obtain ⟨x, y⟩ := e
    obtain ⟨hmem, hadj⟩ := mem_filter.mp he
    obtain ⟨hx, hy⟩ := mk_mem_sym2_iff.mp hmem
    refine mem_biUnion.mpr ⟨(translateLabel p x, translateLabel p y),
      mem_product.mpr ⟨hlabel x hx, hlabel y hy⟩, ?_⟩
    exact mem_filter.mpr ⟨mk_mem_sym2_iff.mpr
      ⟨mem_union_left _ (mem_filter.mpr ⟨hx, rfl⟩),
        mem_union_right _ (mem_filter.mpr ⟨hy, rfl⟩)⟩, hadj⟩
  have hedge : inducedEdgeCount (contactGraph p) U ≤
      ∑ q ∈ T ×ˢ T, inducedEdgeCount (contactGraph p) (W q) :=
    (card_le_card hcover).trans card_biUnion_le
  have hpairs : ∑ q ∈ T ×ˢ T, ((W q).card : ℝ) ≤ 2 * T.card * U.card := by
    calc
      _ ≤ ∑ q ∈ T ×ˢ T, ((part q.1).card + (part q.2).card : ℝ) := by
        apply sum_le_sum
        intro q _
        exact_mod_cast card_union_le (part q.1) (part q.2)
      _ = 2 * T.card * U.card := by
        have hpartR : ∑ t ∈ T, ((part t).card : ℝ) = U.card := by exact_mod_cast hpart
        rw [sum_product]
        simp only [sum_add_distrib, sum_const, nsmul_eq_mul, hpartR]
        rw [← mul_sum, hpartR]
        ring
  have hbound (q : ZMod p × ZMod p) :
      (inducedEdgeCount (contactGraph p) (W q) : ℝ) ≤
        C * Real.sqrt U.card * (W q).card := by
    have hpair : ({q.1, q.2} : Finset (ZMod p)).card ≤ 2 := by
      simpa only [card_singleton] using card_insert_le q.1 ({q.2} : Finset (ZMod p))
    have hsel : W q ⊆ selectedVertices p {q.1, q.2} := by
      intro x hx
      apply (mem_selectedVertices_iff p _ x).mpr
      rcases mem_union.mp hx with hx | hx
      · rw [(mem_filter.mp hx).2]
        exact mem_insert_self _ _
      · rw [(mem_filter.mp hx).2]
        exact mem_insert_of_mem (mem_singleton_self _)
    have h := htwo p {q.1, q.2} hpair (W q) hsel ((hWcard q).trans hsize)
    have hs : Real.sqrt (W q).card ≤ Real.sqrt U.card :=
      Real.sqrt_le_sqrt (by exact_mod_cast hWcard q)
    calc
      _ ≤ C * ((W q).card : ℝ) ^ (3 / 2 : ℝ) := h
      _ = C * Real.sqrt (W q).card * (W q).card := by
        rw [rpow_three_halves _ (Nat.cast_nonneg _)]
        ring
      _ ≤ C * Real.sqrt U.card * (W q).card := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hC.le)
          (Nat.cast_nonneg _)
  calc
    (inducedEdgeCount (contactGraph p) U : ℝ) ≤
        ∑ q ∈ T ×ˢ T, (inducedEdgeCount (contactGraph p) (W q) : ℝ) := by
      exact_mod_cast hedge
    _ ≤ ∑ q ∈ T ×ˢ T, C * Real.sqrt U.card * (W q).card :=
      sum_le_sum (fun q _ => hbound q)
    _ = C * Real.sqrt U.card * ∑ q ∈ T ×ˢ T, ((W q).card : ℝ) :=
      (mul_sum _ _ _).symm
    _ ≤ C * Real.sqrt U.card * (2 * T.card * U.card) :=
      mul_le_mul_of_nonneg_left hpairs (mul_nonneg hC.le (Real.sqrt_nonneg _))
    _ = (2 * C) * T.card * (U.card : ℝ) ^ (3 / 2 : ℝ) := by
      rw [rpow_three_halves _ (Nat.cast_nonneg _)]
      ring

end ExplicitRIP.Contact.Density
