/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.HermitianForms.HostSRG.Norm
public import ExplicitRIP.HermitianForms.HostSRG.Transforms

/-!
# Common neighbors

Normalized pairs in the Hermitian-forms model of `VO₄⁻(p)` have `p - 2` common neighbors when
adjacent and `p(p - 1)` when distinct and nonadjacent. Coordinate automorphisms transport these
counts to arbitrary pairs, giving the common-neighbor parameters of [KM, Section 3].
-/

@[expose] public section

namespace ExplicitRIP.Hfsrg

open scoped BigOperators

variable (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]

def diag (t : ZMod p) : Vertex p := (1, 0, 0, t)

omit [Fact (p % 4 = 3)] in
theorem diag_ne_zero (t : ZMod p) : diag p t ≠ 0 := by
  intro h
  exact one_ne_zero (congrArg Prod.fst h)

omit [Fact (p % 4 = 3)] in
@[simp] theorem quad_diag (t : ZMod p) : quad p (diag p t) = t := by
  simp [quad, diag]

omit [Fact (p % 4 = 3)] in
theorem diagonal_equations (t : ZMod p) (x : Vertex p) :
    quad p x = 0 ∧ quad p (x - diag p t) = 0 ↔
      x.2.2.2 = t * (1 - x.1) ∧ x.2.1 ^ 2 + x.2.2.1 ^ 2 = t * x.1 * (1 - x.1) := by
  simp only [quad, diag, Prod.fst_sub, Prod.snd_sub, sub_zero]
  constructor
  · rintro ⟨h1, h2⟩
    have hw : x.2.2.2 = t * (1 - x.1) := by linear_combination h1 - h2
    refine ⟨hw, ?_⟩
    rw [hw] at h1
    linear_combination -h1
  · rintro ⟨hw, hz⟩
    rw [hw]
    constructor <;> linear_combination -hz

theorem mem_common_diag_iff (t : ZMod p) (x : Vertex p) :
    x ∈ (hermitianGraph p).commonNeighbors 0 (diag p t) ↔
      x ≠ 0 ∧ x ≠ diag p t ∧ x.2.2.2 = t * (1 - x.1) ∧
        x.2.1 ^ 2 + x.2.2.1 ^ 2 = t * x.1 * (1 - x.1) := by
  rw [SimpleGraph.mem_commonNeighbors, adj_iff, adj_iff]
  rw [zero_sub, quad_neg, quad_sub_comm p (diag p t) x]
  rw [ne_comm (a := (0 : Vertex p)), ne_comm (a := diag p t)]
  constructor
  · rintro ⟨⟨h0, hq⟩, ⟨hD, hqD⟩⟩
    exact ⟨h0, hD, (diagonal_equations p t x).mp ⟨hq, hqD⟩⟩
  · rintro ⟨h0, hD, hq⟩
    obtain ⟨hq0, hqD⟩ := (diagonal_equations p t x).mpr hq
    exact ⟨⟨h0, hq0⟩, ⟨hD, hqD⟩⟩

theorem mem_common_diag_zero_iff (x : Vertex p) :
    x ∈ (hermitianGraph p).commonNeighbors 0 (diag p 0) ↔
      x.1 ≠ 0 ∧ x.1 ≠ 1 ∧ x.2.1 = 0 ∧ x.2.2.1 = 0 ∧ x.2.2.2 = 0 := by
  rw [mem_common_diag_iff]
  simp only [zero_mul, Rank1.sum_sq_eq_zero_iff]
  constructor
  · rintro ⟨h0, h1, hw, hb, hc⟩
    refine ⟨?_, ?_, hb, hc, hw⟩
    · intro ha
      exact h0 (Prod.ext ha (Prod.ext hb (Prod.ext hc hw)))
    · intro ha
      exact h1 (Prod.ext ha (Prod.ext hb (Prod.ext hc hw)))
  · rintro ⟨h0, h1, hb, hc, hw⟩
    refine ⟨?_, ?_, hw, hb, hc⟩
    · exact fun h => h0 (congrArg Prod.fst h)
    · exact fun h => h1 (congrArg Prod.fst h)

def adjacentCommonEquiv :
    ((hermitianGraph p).commonNeighbors 0 (diag p 0)) ≃
      {u : ZMod p // u ≠ 0 ∧ u ≠ 1} where
  toFun x := ⟨x.val.1, (mem_common_diag_zero_iff p x.val).mp x.property |>.1,
    (mem_common_diag_zero_iff p x.val).mp x.property |>.2.1⟩
  invFun u := ⟨(u.val, 0, 0, 0), (mem_common_diag_zero_iff p _).mpr
    ⟨u.property.1, u.property.2, rfl, rfl, rfl⟩⟩
  left_inv x := by
    obtain ⟨_, _, hb, hc, hw⟩ := (mem_common_diag_zero_iff p x.val).mp x.property
    exact Subtype.ext (Prod.ext rfl (Prod.ext hb.symm (Prod.ext hc.symm hw.symm)))
  right_inv _ := rfl

omit [Fact (p % 4 = 3)] in
theorem card_avoid_zero_one : Fintype.card {u : ZMod p // u ≠ 0 ∧ u ≠ 1} = p - 2 := by
  classical
  rw [Fintype.card_subtype]
  have hf : Finset.univ.filter (fun u : ZMod p => u ≠ 0 ∧ u ≠ 1) =
      (Finset.univ.erase 0).erase 1 := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    tauto
  rw [hf, Finset.card_erase_of_mem (by simp),
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
  omega

theorem card_common_diag_zero :
    Nat.card ((hermitianGraph p).commonNeighbors 0 (diag p 0)) = p - 2 := by
  rw [Nat.card_congr (adjacentCommonEquiv p), Nat.card_eq_fintype_card, card_avoid_zero_one]

theorem mem_common_diag_of_ne_zero (t : ZMod p) (ht : t ≠ 0) (x : Vertex p) :
    x ∈ (hermitianGraph p).commonNeighbors 0 (diag p t) ↔
      x.2.2.2 = t * (1 - x.1) ∧ x.2.1 ^ 2 + x.2.2.1 ^ 2 = t * x.1 * (1 - x.1) := by
  rw [mem_common_diag_iff]
  constructor
  · exact fun h => h.2.2
  · intro h
    have hq := (diagonal_equations p t x).mpr h
    refine ⟨?_, ?_, h⟩
    · intro hx
      apply ht
      simpa only [hx, zero_sub, quad_neg, quad_diag] using hq.2
    · intro hx
      apply ht
      simpa only [hx, quad_diag] using hq.1

def nonadjacentCommonEquiv (t : ZMod p) (ht : t ≠ 0) :
    ((hermitianGraph p).commonNeighbors 0 (diag p t)) ≃
      (Σ u : ZMod p, {z : ZMod p × ZMod p // z.1 ^ 2 + z.2 ^ 2 = t * u * (1 - u)}) where
  toFun x := ⟨x.val.1, ⟨(x.val.2.1, x.val.2.2.1),
    ((mem_common_diag_of_ne_zero p t ht x.val).mp x.property).2⟩⟩
  invFun u := ⟨(u.1, u.2.val.1, u.2.val.2, t * (1 - u.1)),
    (mem_common_diag_of_ne_zero p t ht _).mpr ⟨rfl, u.2.property⟩⟩
  left_inv x := Subtype.ext (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl
    ((mem_common_diag_of_ne_zero p t ht x.val).mp x.property).1.symm)))
  right_inv _ := rfl

theorem card_common_diag_of_ne_zero (t : ZMod p) (ht : t ≠ 0) :
    Nat.card ((hermitianGraph p).commonNeighbors 0 (diag p t)) = p * (p - 1) := by
  classical
  rw [Nat.card_congr (nonadjacentCommonEquiv p t ht), Nat.card_eq_fintype_card,
    Fintype.card_sigma]
  simp_rw [card_sq_add_sq, mul_eq_zero, ht, false_or, sub_eq_zero, eq_comm (a := (1 : ZMod p))]
  have hs : (∑ u : ZMod p, if u = 0 ∨ u = 1 then 1 else p + 1) =
      2 + (p - 2) * (p + 1) := by
    rw [Finset.sum_ite]
    have h01 : (Finset.univ.filter (fun u : ZMod p => u = 0 ∨ u = 1)).card = 2 := by
      have he : Finset.univ.filter (fun u : ZMod p => u = 0 ∨ u = 1) = {0, 1} := by
        ext u
        simp
      rw [he]
      simp
    have hn : (Finset.univ.filter (fun u : ZMod p => ¬ (u = 0 ∨ u = 1))).card = p - 2 := by
      simpa only [not_or, ← Fintype.card_subtype] using card_avoid_zero_one p
    simp only [Finset.sum_const, nsmul_eq_mul, h01, hn, mul_one, Nat.cast_id]
  rw [hs]
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hsub : p - 2 + 2 = p := Nat.sub_add_cancel hp
  have hsub' : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
  nlinarith

theorem normalize_pair (x y : Vertex p) (hxy : x ≠ y) :
    ∃ e : hermitianGraph p ≃g hermitianGraph p, ∃ t : ZMod p,
      e x = 0 ∧ e y = diag p t := by
  obtain ⟨e, he, t, ht⟩ := normalize p (y - x) (sub_ne_zero.mpr hxy.symm)
  refine ⟨(translateIso p (-x)).trans e, t, ?_, ?_⟩
  · change e (x + -x) = 0
    simpa only [add_neg_cancel] using he
  · change e (y + -x) = diag p t
    simpa only [sub_eq_add_neg, diag] using ht

theorem adj_zero_diag_iff (t : ZMod p) :
    (hermitianGraph p).Adj 0 (diag p t) ↔ t = 0 := by
  rw [adj_iff, zero_sub, quad_neg, quad_diag]
  exact and_iff_right (Ne.symm (diag_ne_zero p t))

theorem card_common_of_adj (x y : Vertex p) (hxy : (hermitianGraph p).Adj x y) :
    Nat.card ((hermitianGraph p).commonNeighbors x y) = p - 2 := by
  obtain ⟨e, t, hx, hy⟩ := normalize_pair p x y hxy.ne
  have ht : t = 0 := (adj_zero_diag_iff p t).mp (by
    simpa only [hx, hy] using e.map_adj_iff.mpr hxy)
  have hcard := card_commonNeighbors_iso p e x y
  rw [hx, hy, ht, card_common_diag_zero] at hcard
  exact hcard.symm

theorem card_common_of_not_adj (x y : Vertex p) (hne : x ≠ y)
    (hxy : ¬ (hermitianGraph p).Adj x y) :
    Nat.card ((hermitianGraph p).commonNeighbors x y) = p * (p - 1) := by
  obtain ⟨e, t, hx, hy⟩ := normalize_pair p x y hne
  have ht : t ≠ 0 := by
    intro ht
    apply hxy
    apply e.map_adj_iff.mp
    rw [hx, hy]
    exact (adj_zero_diag_iff p t).mpr ht
  have hcard := card_commonNeighbors_iso p e x y
  rw [hx, hy, card_common_diag_of_ne_zero p t ht] at hcard
  exact hcard.symm

end ExplicitRIP.Hfsrg
