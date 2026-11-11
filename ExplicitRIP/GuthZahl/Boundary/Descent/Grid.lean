/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Boundary.Descent.Polynomial

/-!
# Linear subspaces in the determinant quadric

Every two-dimensional subspace of singular two-by-two matrices belongs to
one of the two families obtained by fixing a row or column ratio.
-/

@[expose] public section

namespace ExplicitRIP.GuthZahl.Boundary.Descent

variable {K : Type*} [Field K]

/-- The homogeneous matrix plane with a fixed row or column ratio. -/
def gridMap (side : Bool) (t : Option K) : (Fin 2 → K) →ₗ[K] (Fin 4 → K) where
  toFun u := match side, t with
    | false, some c => ![u 0, u 1, c * u 0, c * u 1]
    | false, none => ![0, 0, u 0, u 1]
    | true, some c => ![u 0, c * u 0, u 1, c * u 1]
    | true, none => ![0, u 0, 0, u 1]
  map_add' u v := by cases side <;> cases t <;> ext i <;> fin_cases i <;> simp <;> ring
  map_smul' c u := by cases side <;> cases t <;> ext i <;> fin_cases i <;> simp <;> ring

/-- The image of the matrix-plane parametrization. -/
def gridSpace (side : Bool) (t : Option K) : Submodule K (Fin 4 → K) :=
  LinearMap.range (gridMap side t)

theorem gridMap_injective (side : Bool) (t : Option K) :
    Function.Injective (gridMap side t) := by
  intro u v h
  cases side <;> cases t
  · ext i; fin_cases i
    · exact congrFun h 2
    · exact congrFun h 3
  · ext i; fin_cases i
    · exact congrFun h 0
    · exact congrFun h 1
  · ext i; fin_cases i
    · exact congrFun h 1
    · exact congrFun h 3
  · ext i; fin_cases i
    · exact congrFun h 0
    · exact congrFun h 2

theorem finrank_gridSpace (side : Bool) (t : Option K) :
    Module.finrank K (gridSpace side t) = 2 := by
  rw [gridSpace, LinearMap.finrank_range_of_inj (gridMap_injective side t)]
  exact Module.finrank_fin_fun K

theorem mem_gridSpace (side : Bool) (t : Option K) (v : Fin 4 → K) :
    v ∈ gridSpace side t ↔ match side, t with
      | false, some c => v 2 = c * v 0 ∧ v 3 = c * v 1
      | false, none => v 0 = 0 ∧ v 1 = 0
      | true, some c => v 1 = c * v 0 ∧ v 3 = c * v 2
      | true, none => v 0 = 0 ∧ v 2 = 0 := by
  cases side <;> cases t
  · constructor
    · rintro ⟨u, rfl⟩; exact ⟨rfl, rfl⟩
    · rintro ⟨h0, h1⟩
      refine ⟨![v 2, v 3], ?_⟩
      ext i; fin_cases i <;> simp [gridMap, h0, h1]
  · constructor
    · rintro ⟨u, rfl⟩; exact ⟨rfl, rfl⟩
    · rintro ⟨h2, h3⟩
      refine ⟨![v 0, v 1], ?_⟩
      ext i; fin_cases i <;> simp [gridMap, h2, h3]
  · constructor
    · rintro ⟨u, rfl⟩; exact ⟨rfl, rfl⟩
    · rintro ⟨h0, h2⟩
      refine ⟨![v 1, v 3], ?_⟩
      ext i; fin_cases i <;> simp [gridMap, h0, h2]
  · constructor
    · rintro ⟨u, rfl⟩; exact ⟨rfl, rfl⟩
    · rintro ⟨h1, h3⟩
      refine ⟨![v 0, v 2], ?_⟩
      ext i; fin_cases i <;> simp [gridMap, h1, h3]

theorem cross_eq_zero_of_determinant_zero (U : Submodule K (Fin 4 → K))
    (hU : ∀ v ∈ U, determinantFour v = 0) {a b : Fin 4 → K}
    (ha : a ∈ U) (hb : b ∈ U) :
    a 0 * b 3 + b 0 * a 3 - a 1 * b 2 - b 1 * a 2 = 0 := by
  have ha0 := hU a ha
  have hb0 := hU b hb
  have hab := hU (a + b) (U.add_mem ha hb)
  simp only [determinantFour, Pi.add_apply] at ha0 hb0 hab
  linear_combination hab - ha0 - hb0

/-- A linear space of singular matrices has a fixed row or column ratio. -/
theorem exists_gridSpace_le (U : Submodule K (Fin 4 → K))
    (hU : ∀ v ∈ U, determinantFour v = 0) :
    ∃ side t, U ≤ gridSpace side t := by
  classical
  by_cases hfirst : ∃ a ∈ U, a 0 ≠ 0
  · obtain ⟨a, ha, ha0⟩ := hfirst
    have hqa : a 0 * a 3 - a 1 * a 2 = 0 := hU a ha
    by_cases hsecond : ∃ b ∈ U, b 0 = 0 ∧ b 1 ≠ 0
    · obtain ⟨b, hb, hb0, hb1⟩ := hsecond
      have hb2 : b 2 = 0 := by
        have hqb := hU b hb
        simp only [determinantFour, hb0, zero_mul, zero_sub, neg_eq_zero] at hqb
        exact (mul_eq_zero.mp hqb).resolve_left hb1
      have hab := cross_eq_zero_of_determinant_zero U hU ha hb
      simp only [hb0, hb2, zero_mul, mul_zero, add_zero, sub_zero] at hab
      refine ⟨false, some (a 2 / a 0), ?_⟩
      intro v hv
      have hbv := cross_eq_zero_of_determinant_zero U hU hb hv
      simp only [hb0, hb2, zero_mul, mul_zero, zero_add, sub_zero] at hbv
      have hv2 : a 0 * v 2 - a 2 * v 0 = 0 := by
        apply (mul_eq_zero.mp (show b 1 * (a 0 * v 2 - a 2 * v 0) = 0 from ?_)).resolve_left hb1
        linear_combination v 0 * hab - a 0 * hbv
      have hav := cross_eq_zero_of_determinant_zero U hU ha hv
      have hv3 : a 0 * v 3 - a 2 * v 1 = 0 := by
        apply (mul_eq_zero.mp (show a 0 * (a 0 * v 3 - a 2 * v 1) = 0 from ?_)).resolve_left ha0
        linear_combination a 0 * hav - v 0 * hqa + a 1 * hv2
      rw [mem_gridSpace]
      constructor
      · apply (mul_left_cancel₀ ha0)
        field_simp
        linear_combination hv2
      · apply (mul_left_cancel₀ ha0)
        field_simp
        linear_combination hv3
    · refine ⟨true, some (a 1 / a 0), ?_⟩
      intro v hv
      have hv1 : a 0 * v 1 - a 1 * v 0 = 0 := by
        have hb : v - (v 0 / a 0) • a ∈ U := U.sub_mem hv (U.smul_mem _ ha)
        have hb0 : (v - (v 0 / a 0) • a) 0 = 0 := by
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          field_simp
          ring
        have hb1 : (v - (v 0 / a 0) • a) 1 = 0 := by
          by_contra h
          exact hsecond ⟨_, hb, hb0, h⟩
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hb1
        field_simp at hb1
        linear_combination hb1
      have hav := cross_eq_zero_of_determinant_zero U hU ha hv
      have hv3 : a 0 * v 3 - a 1 * v 2 = 0 := by
        apply (mul_eq_zero.mp (show a 0 * (a 0 * v 3 - a 1 * v 2) = 0 from ?_)).resolve_left ha0
        linear_combination a 0 * hav - v 0 * hqa + a 2 * hv1
      rw [mem_gridSpace]
      constructor
      · apply (mul_left_cancel₀ ha0)
        field_simp
        linear_combination hv1
      · apply (mul_left_cancel₀ ha0)
        field_simp
        linear_combination hv3
  · have h0 (v : Fin 4 → K) (hv : v ∈ U) : v 0 = 0 := by
      by_contra h
      exact hfirst ⟨v, hv, h⟩
    by_cases hsecond : ∃ a ∈ U, a 1 ≠ 0
    · obtain ⟨a, ha, ha1⟩ := hsecond
      have ha2 : a 2 = 0 := by
        have h := hU a ha
        simp only [determinantFour, h0 a ha, zero_mul, zero_sub, neg_eq_zero] at h
        exact (mul_eq_zero.mp h).resolve_left ha1
      refine ⟨true, none, ?_⟩
      intro v hv
      rw [mem_gridSpace]
      refine ⟨h0 v hv, ?_⟩
      have h := cross_eq_zero_of_determinant_zero U hU ha hv
      simp only [h0 a ha, h0 v hv, ha2, zero_mul, mul_zero, add_zero,
        zero_sub, sub_zero, neg_eq_zero] at h
      exact (mul_eq_zero.mp h).resolve_left ha1
    · refine ⟨false, none, ?_⟩
      intro v hv
      rw [mem_gridSpace]
      refine ⟨h0 v hv, ?_⟩
      by_contra h
      exact hsecond ⟨v, hv, h⟩

/-- A two-dimensional space of singular matrices is exactly a grid plane. -/
theorem exists_gridSpace_eq (U : Submodule K (Fin 4 → K))
    (hdim : Module.finrank K U = 2) (hU : ∀ v ∈ U, determinantFour v = 0) :
    ∃ side t, U = gridSpace side t := by
  obtain ⟨side, t, h⟩ := exists_gridSpace_le U hU
  exact ⟨side, t, Submodule.eq_of_le_of_finrank_eq h
    (hdim.trans (finrank_gridSpace side t).symm)⟩

/-- Different ratios on the same side give disjoint matrix planes. -/
theorem disjoint_gridSpace (side : Bool) {s t : Option K} (hst : s ≠ t) :
    Disjoint (gridSpace side s) (gridSpace side t) := by
  rw [Submodule.disjoint_def]
  intro v hs ht
  rw [mem_gridSpace] at hs ht
  cases side <;> cases s <;> cases t
  · exact False.elim (hst rfl)
  · rcases hs with ⟨h0, h1⟩
    rcases ht with ⟨h2, h3⟩
    ext i; fin_cases i <;> simp_all
  · rcases ht with ⟨h0, h1⟩
    rcases hs with ⟨h2, h3⟩
    ext i; fin_cases i <;> simp_all
  · rename_i s t
    have hne : s - t ≠ 0 := sub_ne_zero.mpr (fun h => hst (congrArg some h))
    have h0 : v 0 = 0 := by
      apply (mul_eq_zero.mp (show (s - t) * v 0 = 0 from ?_)).resolve_left hne
      linear_combination ht.1 - hs.1
    have h1 : v 1 = 0 := by
      apply (mul_eq_zero.mp (show (s - t) * v 1 = 0 from ?_)).resolve_left hne
      linear_combination ht.2 - hs.2
    ext i; fin_cases i <;> simp_all
  · exact False.elim (hst rfl)
  · rcases hs with ⟨h0, h2⟩
    rcases ht with ⟨h1, h3⟩
    ext i; fin_cases i <;> simp_all
  · rcases ht with ⟨h0, h2⟩
    rcases hs with ⟨h1, h3⟩
    ext i; fin_cases i <;> simp_all
  · rename_i s t
    have hne : s - t ≠ 0 := sub_ne_zero.mpr (fun h => hst (congrArg some h))
    have h0 : v 0 = 0 := by
      apply (mul_eq_zero.mp (show (s - t) * v 0 = 0 from ?_)).resolve_left hne
      linear_combination ht.1 - hs.1
    have h2 : v 2 = 0 := by
      apply (mul_eq_zero.mp (show (s - t) * v 2 = 0 from ?_)).resolve_left hne
      linear_combination ht.2 - hs.2
    ext i; fin_cases i <;> simp_all

/-- Among five different planes on a determinant quadric, three are pairwise disjoint. -/
theorem exists_disjoint_triple {ι : Type*} [Fintype ι]
    (U : ι → Submodule K (Fin 4 → K)) (hinj : Function.Injective U)
    (hcard : 5 ≤ Fintype.card ι) (hdim : ∀ i, Module.finrank K (U i) = 2)
    (hzero : ∀ i v, v ∈ U i → determinantFour v = 0) :
    ∃ i j k : ι, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      Disjoint (U i) (U j) ∧ Disjoint (U i) (U k) ∧ Disjoint (U j) (U k) := by
  classical
  choose side t heq using fun i => exists_gridSpace_eq (U i) (hdim i) (hzero i)
  obtain ⟨s, hs⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card side
    (n := 2) (by simp only [Fintype.card_bool]; omega)
  obtain ⟨i, j, k, hi, hj, hk, hij, hik, hjk⟩ := Finset.two_lt_card_iff.mp hs
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj hk
  have hd (a b : ι) (ha : side a = s) (hb : side b = s) (hab : a ≠ b) :
      Disjoint (U a) (U b) := by
    rw [heq a, heq b, ha, hb]
    apply disjoint_gridSpace
    intro ht
    apply hab
    apply hinj
    rw [heq a, heq b, ha, hb, ht]
  exact ⟨i, j, k, hij, hik, hjk, hd i j hi hj hij, hd i k hi hk hik, hd j k hj hk hjk⟩

end ExplicitRIP.GuthZahl.Boundary.Descent

end
