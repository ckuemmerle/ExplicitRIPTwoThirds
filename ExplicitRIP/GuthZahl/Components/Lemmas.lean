/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Components.Defs
import ExplicitRIP.GuthZahl.Basic

/-!
# Elementary lemmas for the Guth–Zahl components argument

Lost rich points lie on the other factors, a degree-squared pigeonhole selects a
component, and contained intersecting lines supply tangent directions at every order.
Principal opens on an irreducible hypersurface can be intersected by multiplication.
-/

public section

namespace ExplicitRIP.GuthZahl

open Classical in
/-- Discarded lines are charged to the product of other factors too. -/
theorem unique_factor_point_loss {K : Type*} [Field K] {m : ℕ}
    (Ls : Finset (Line K)) (F : Fin m → Poly K)
    (hcover : ∀ L ∈ Ls, ∃ i, LineOn (F i) L)
    (i : Fin m) (L : Line K) (hL : L ∈ uniqueFactorLines Ls F i) :
    ((richPoints Ls 2 ∩ (L.1 : Set (Point K))) \ richPoints (uniqueFactorLines Ls F i) 2) ⊆
      {x : Point K | x ∈ L.1 ∧
        MvPolynomial.eval x (∏ j ∈ Finset.univ.erase i, F j) = 0} := by
  intro x hx
  obtain ⟨M, hM, hML⟩ := Finset.exists_mem_ne
    (lt_of_lt_of_le (by decide : 1 < 2) hx.1.1) L
  obtain ⟨hMs, hxM⟩ := Finset.mem_filter.mp hM
  have hMu : M ∉ uniqueFactorLines Ls F i := by
    intro hMu
    apply hx.2
    exact Finset.one_lt_card.mpr ⟨L, Finset.mem_filter.mpr ⟨hL, hx.1.2⟩,
      M, Finset.mem_filter.mpr ⟨hMu, hxM⟩, hML.symm⟩
  have hother : ∃ j, j ≠ i ∧ LineOn (F j) M := by
    obtain ⟨j, hj⟩ := hcover M hMs
    by_cases hji : j = i
    · subst j
      by_contra hnone
      apply hMu
      exact Finset.mem_filter.mpr ⟨hMs, hj,
        fun k hki hk => hnone ⟨k, hki, hk⟩⟩
    · exact ⟨j, hji, hj⟩
  obtain ⟨j, hji, hj⟩ := hother
  have hxj : MvPolynomial.eval x (F j) = 0 := by
    have he := congrArg (Polynomial.eval (0 : K))
      (hj x hxM 0 (Submodule.zero_mem _))
    simpa only [eval_restrictLine, zero_smul, add_zero, Polynomial.eval_zero] using he
  refine ⟨hx.1.2, ?_⟩
  rw [map_prod]
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩) hxj

open Classical in
/-- A finite numerical lemma, independent of fields and geometry. -/
theorem degree_squared_pigeonhole (m n D : ℕ) (a d : Fin m → ℕ)
    (hn : 0 < n) (hD : 0 < D) (hd : ∀ i, 0 < d i)
    (hsum : (∑ i, d i) ≤ D) (hcard : n ≤ 2 * ∑ i, a i) :
    ∃ i, 0 < a i ∧ n * (d i) ^ 2 ≤ 2 * D ^ 2 * a i := by
  by_contra hnone
  push Not at hnone
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := by
    by_contra hempty
    have he := Finset.not_nonempty_iff_eq_empty.mp hempty
    have ha : (∑ i, a i) = 0 := by rw [he, Finset.sum_empty]
    rw [ha, mul_zero] at hcard
    exact (Nat.not_le_of_lt hn) hcard
  have hlt : ∀ i : Fin m, 2 * D ^ 2 * a i < n * (d i) ^ 2 := by
    intro i
    by_cases hai : 0 < a i
    · exact hnone i hai
    · have hai0 : a i = 0 := Nat.eq_zero_of_not_pos hai
      rw [hai0, mul_zero]
      exact Nat.mul_pos hn (pow_pos (hd i) 2)
  have hsquares : (∑ i, (d i) ^ 2) ≤ D ^ 2 := by
    exact (Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => Nat.zero_le (d i))).trans
      (Nat.pow_le_pow_left hsum 2)
  have hsumlt : 2 * D ^ 2 * (∑ i, a i) < n * (∑ i, (d i) ^ 2) := by
    simpa only [Finset.mul_sum] using
      (Finset.sum_lt_sum_of_nonempty hne (fun i _ => hlt i))
  have hltcard : 2 * (∑ i, a i) < n := by
    apply (mul_lt_mul_iff_left₀ (pow_pos hD 2)).mp
    calc
      2 * (∑ i, a i) * D ^ 2 = 2 * D ^ 2 * (∑ i, a i) := by ring
      _ < n * (∑ i, (d i) ^ 2) := hsumlt
      _ ≤ n * D ^ 2 := Nat.mul_le_mul_left n hsquares
  exact (not_lt_of_ge hcard) hltcard

open Classical in
/-- Internal rich points of contained lines are two-direction points at every order. -/
theorem rich_point_two_tangent_directions {K : Type*} [Field K]
    (f : Poly K) (Ls : Finset (Line K)) (hLs : ∀ L ∈ Ls, LineOn f L)
    (x : Point K) (hx : x ∈ richPoints Ls 2) (r : ℕ) :
    TwoTangentDirections f x r := by
  obtain ⟨L, hL, M, hM, hLM⟩ := Finset.one_lt_card.mp
    (lt_of_lt_of_le (by decide : 1 < 2) hx)
  obtain ⟨hLsL, hxL⟩ := Finset.mem_filter.mp hL
  obtain ⟨hLsM, hxM⟩ := Finset.mem_filter.mp hM
  obtain ⟨_, _, v, hv, hv0⟩ := line_exists_base_direction L
  obtain ⟨_, _, w, hw, hw0⟩ := line_exists_base_direction M
  refine ⟨v, w, hv0, hw0, ?_, ?_, ?_⟩
  · rintro ⟨a, ha⟩
    have hwL : w ∈ L.1.direction := by
      rw [ha]
      exact L.1.direction.smul_mem a hv
    have hLspan := eq_span_singleton_of_mem_of_finrank_eq_one L.2 hwL hw0
    have hMspan := eq_span_singleton_of_mem_of_finrank_eq_one M.2 hw hw0
    exact hLM (Subtype.ext (AffineSubspace.ext_of_direction_eq
      (hLspan.trans hMspan.symm) ⟨x, hxL, hxM⟩))
  · intro j _
    rw [hLs L hLsL x hxL v hv, Polynomial.coeff_zero]
  · intro j _
    rw [hLs M hLsM x hxM w hw, Polynomial.coeff_zero]

open Classical in
/-- Intersection of two nonempty principal opens on an irreducible hypersurface. -/
theorem principalOpen_intersection {K : Type*} [Field K] [IsAlgClosed K]
    (f g h : Poly K) (hf : Irreducible f) (hg : ¬ f ∣ g) (hh : ¬ f ∣ h) :
    ¬ f ∣ g * h ∧ (principalOpen f (g * h)).Nonempty ∧
      principalOpen f (g * h) = principalOpen f g ∩ principalOpen f h := by
  have hprod : ¬ f ∣ g * h := by
    intro hdiv
    rcases (UniqueFactorizationMonoid.irreducible_iff_prime.mp hf).dvd_or_dvd hdiv with
      hg' | hh'
    · exact hg hg'
    · exact hh hh'
  refine ⟨hprod, principalOpen_nonempty f (g * h) hf hprod, ?_⟩
  ext x
  simp only [principalOpen, Set.mem_ofPred_eq, Set.mem_inter_iff, map_mul, mul_ne_zero_iff]
  tauto

end ExplicitRIP.GuthZahl

end
