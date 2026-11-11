/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Frozen.Defs.InducedEdgeCount

/-!
# Rectangle counts and fixed-size subset incidence

Finite incidence counting implements fixed-size subset averaging.

Source: [KM, proof of Lemma 3].
-/

@[expose] public section

open scoped BigOperators

namespace ExplicitRIP.Dens

variable {V : Type*}

/-- The sum of adjacency entries in an ordered rectangle. -/
noncomputable def rectangleSum (G : SimpleGraph V) [DecidableRel G.Adj]
    (I J : Finset V) : ℝ :=
  ∑ i ∈ I, ∑ j ∈ J, G.adjMatrix ℝ i j

theorem rectangleSum_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (I J : Finset V) : 0 ≤ rectangleSum G I J := by
  unfold rectangleSum
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  simp only [SimpleGraph.adjMatrix_apply]
  split_ifs <;> norm_num

theorem rectangleSum_comm (G : SimpleGraph V) [DecidableRel G.Adj]
    (I J : Finset V) : rectangleSum G I J = rectangleSum G J I := by
  simp only [rectangleSum, SimpleGraph.adjMatrix_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  simp only [G.adj_comm]

theorem rectangleSum_eq_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (I J : Finset V) :
    rectangleSum G I J = (((I ×ˢ J).filter (fun p => G.Adj p.1 p.2)).card : ℝ) := by
  simp only [rectangleSum, SimpleGraph.adjMatrix_apply, Finset.card_eq_sum_ones,
    Nat.cast_sum, Finset.sum_filter, Finset.sum_product, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]

/-- An ordered rectangle counts each edge of the union at most twice. -/
theorem rectangleSum_le_twice_inducedEdgeCount [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (I J : Finset V) : rectangleSum G I J ≤ 2 * (inducedEdgeCount G (I ∪ J) : ℝ) := by
  let S := (I ×ˢ J).filter (fun p => G.Adj p.1 p.2)
  let E := (I ∪ J).sym2.filter (fun e => e ∈ G.edgeSet)
  have hmap : (S : Set (V × V)).MapsTo (fun p => s(p.1, p.2)) E := by
    intro p hp
    obtain ⟨hp, hAdj⟩ := Finset.mem_filter.mp hp
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mk_mem_sym2_iff.mpr
      ⟨Finset.mem_union_left J hi, Finset.mem_union_right I hj⟩, hAdj⟩
  have hfiber (e : Sym2 V) : (S.filter (fun p => s(p.1, p.2) = e)).card ≤ 2 := by
    obtain ⟨v, w⟩ := e
    have hsub : S.filter (fun p => s(p.1, p.2) = s(v, w)) ⊆ {(v, w), (w, v)} := by
      intro p hp
      have hp' := (Sym2.mk_eq_mk_iff (p := p) (q := (v, w))).mp
        (Finset.mem_filter.mp hp).2
      simpa only [Finset.mem_insert, Finset.mem_singleton, Prod.swap_prod_mk] using hp'
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  have hcard : S.card ≤ 2 * E.card := by
    rw [Finset.card_eq_sum_card_fiberwise hmap]
    calc
      _ ≤ ∑ _e ∈ E, 2 := Finset.sum_le_sum (fun e _ => hfiber e)
      _ = 2 * E.card := by simp [mul_comm]
  rw [rectangleSum_eq_card]
  exact_mod_cast hcard

/-- Each vertex appears in the same number of fixed-size subsets. -/
theorem sum_powersetCard_sum (J : Finset V) (a : ℕ) (ha : 1 ≤ a) (f : V → ℝ) :
    (∑ K ∈ J.powersetCard a, ∑ j ∈ K, f j) =
      (Nat.choose (J.card - 1) (a - 1) : ℝ) * ∑ j ∈ J, f j := by
  classical
  have hcount (j : V) (hj : j ∈ J) :
      ((J.powersetCard a).filter (fun K => j ∈ K)).card =
        Nat.choose (J.card - 1) (a - 1) := by
    simpa only [Finset.singleton_subset_iff, Finset.card_singleton] using
      Finset.card_filter_powersetCard_subset ({j} : Finset V) J a
        (Finset.singleton_subset_iff.mpr hj) (by simpa using ha)
  calc
    _ = ∑ K ∈ J.powersetCard a, ∑ j ∈ J, if j ∈ K then f j else 0 := by
      apply Finset.sum_congr rfl
      intro K hK
      have hKJ := (Finset.mem_powersetCard.mp hK).1
      rw [← Finset.sum_filter]
      congr 1
      ext j
      simp only [Finset.mem_filter]
      exact ⟨fun h => ⟨hKJ h, h⟩, fun h => h.2⟩
    _ = ∑ j ∈ J, ∑ K ∈ J.powersetCard a, if j ∈ K then f j else 0 :=
      Finset.sum_comm
    _ = ∑ j ∈ J, (Nat.choose (J.card - 1) (a - 1) : ℝ) * f j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcount j hj]
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- The exact, unnormalized subset-averaging identity for rectangles. -/
theorem sum_powersetCard_rectangleSum (G : SimpleGraph V) [DecidableRel G.Adj]
    (I J : Finset V) (a : ℕ) (ha : 1 ≤ a) :
    (∑ K ∈ J.powersetCard a, rectangleSum G I K) =
      (Nat.choose (J.card - 1) (a - 1) : ℝ) * rectangleSum G I J := by
  simp only [rectangleSum]
  rw [Finset.sum_comm]
  simp_rw [sum_powersetCard_sum J a ha, ← Finset.mul_sum]

end ExplicitRIP.Dens
