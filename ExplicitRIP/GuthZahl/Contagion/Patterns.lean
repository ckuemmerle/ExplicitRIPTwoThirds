/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Contagion.Defs
import ExplicitRIP.GuthZahl.Basic

/-!
# Generic zero patterns on lines and irreducible surfaces

On a line, the zero pattern is constant away from the zeros of the tests that do not
contain the line. On an irreducible surface, the product of the tests not divisible
by its equation gives a nonempty principal open with the surface's generic pattern.
-/

public section

namespace ExplicitRIP.GuthZahl

/-- Outside at most the sum of the test degrees, a line has one zero pattern. -/
theorem line_generic_pattern_exception {K : Type*} [Field K] {J : ℕ}
    (qs : Fin J → Poly K) (L : Line K) :
    ∃ E : Set (Point K), E.Finite ∧ E ⊆ (L.1 : Set (Point K)) ∧
      E.ncard ≤ ∑ j, (qs j).totalDegree ∧
      ∀ x ∈ L.1, x ∉ E → zeroPattern qs x = lineGenericPattern qs L := by
  classical
  let Z : Fin J → Set (Point K) := fun j =>
    if LineOn (qs j) L then ∅ else {x | x ∈ L.1 ∧ MvPolynomial.eval x (qs j) = 0}
  have hZ (j : Fin J) : (Z j).Finite ∧ (Z j).ncard ≤ (qs j).totalDegree := by
    by_cases h : LineOn (qs j) L
    · simp only [Z, ite_eq_left h, Set.finite_empty, Set.ncard_empty, true_and]
      exact Nat.zero_le _
    · simpa only [Z, ite_eq_right h] using line_hypersurface_bound (qs j) L h
  refine ⟨⋃ j, Z j, Set.finite_iUnion (fun j => (hZ j).1), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    by_cases h : LineOn (qs j) L
    · simp only [Z, ite_eq_left h, Set.mem_empty_iff_false] at hj
    · exact (show x ∈ L.1 ∧ MvPolynomial.eval x (qs j) = 0 from
        by simpa only [Z, ite_eq_right h, Set.mem_ofPred_eq] using hj).1
  · exact (Set.ncard_iUnion_le_of_fintype Z).trans
      (Finset.sum_le_sum fun j _ => (hZ j).2)
  · intro x hx hxE
    funext j
    by_cases h : LineOn (qs j) L
    · have hx0 : MvPolynomial.eval x (qs j) = 0 := by
        have he := congrArg (Polynomial.eval (0 : K)) (h x hx 0 L.1.direction.zero_mem)
        simpa only [eval_restrictLine, zero_smul, add_zero, Polynomial.eval_zero] using he
      simp only [zeroPattern, lineGenericPattern, hx0, h, decide_true]
    · have hx0 : MvPolynomial.eval x (qs j) ≠ 0 := by
        intro hz
        apply hxE
        apply Set.mem_iUnion.mpr
        exact ⟨j, by simpa only [Z, ite_eq_right h, Set.mem_ofPred_eq] using And.intro hx hz⟩
      simp only [zeroPattern, lineGenericPattern, hx0, h, decide_false]

/-- If a Boolean condition holds at more points than the sum of the test degrees, it accepts the
generic line pattern. Extended cardinality also includes infinite sets of such points. -/
theorem line_generic_pattern_accepted {K : Type*} [Field K] {J : ℕ}
    (qs : Fin J → Poly K) (B : Set (Fin J → Bool)) (L : Line K)
    (hmany : ((∑ j, (qs j).totalDegree : ℕ) : ℕ∞) <
      {x : Point K | x ∈ L.1 ∧ zeroPattern qs x ∈ B}.encard) :
    lineGenericPattern qs L ∈ B := by
  classical
  obtain ⟨E, hEfin, _, hEcard, hpattern⟩ := line_generic_pattern_exception qs L
  by_contra hnot
  have hsub : {x : Point K | x ∈ L.1 ∧ zeroPattern qs x ∈ B} ⊆ E := by
    intro x hx
    by_contra hxE
    exact hnot ((hpattern x hx.1 hxE) ▸ hx.2)
  exact (not_le_of_gt hmany) ((Set.encard_mono hsub).trans
    (Set.encard_le_coe_iff_finite_ncard_le.mpr ⟨hEfin, hEcard⟩))

/-- Take g to be the product of precisely the tests not divisible by f. -/
theorem surface_generic_pattern_open {K : Type*} [Field K] [IsAlgClosed K]
    {J : ℕ} (f : Poly K) (hf : Irreducible f) (qs : Fin J → Poly K) :
    ∃ g : Poly K, ¬ f ∣ g ∧ (principalOpen f g).Nonempty ∧
      ∀ x ∈ principalOpen f g, zeroPattern qs x = surfaceGenericPattern f qs := by
  classical
  let S : Finset (Fin J) := Finset.univ.filter (fun j => ¬ f ∣ qs j)
  let g : Poly K := ∏ j ∈ S, qs j
  have hfg : ¬ f ∣ g := by
    apply (UniqueFactorizationMonoid.irreducible_iff_prime.mp hf).not_dvd_finsetProd
    intro j hj
    exact (Finset.mem_filter.mp hj).2
  refine ⟨g, hfg, principalOpen_nonempty f g hf hfg, ?_⟩
  intro x hx
  funext j
  by_cases hj : f ∣ qs j
  · have hxq : MvPolynomial.eval x (qs j) = 0 := by
      obtain ⟨q, hq⟩ := hj
      rw [hq, map_mul, hx.1, zero_mul]
    simp only [zeroPattern, surfaceGenericPattern, hxq, hj, decide_true]
  · have hmem : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
    have hxg : (∏ i ∈ S, MvPolynomial.eval x (qs i)) ≠ 0 := by
      simpa only [g, MvPolynomial.eval_prod] using hx.2
    have hxq : MvPolynomial.eval x (qs j) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hxg) j hmem
    simp only [zeroPattern, surfaceGenericPattern, hxq, hj, decide_false]

end ExplicitRIP.GuthZahl

end
