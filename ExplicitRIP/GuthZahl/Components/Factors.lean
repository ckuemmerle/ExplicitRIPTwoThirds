/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Components.Defs
import ExplicitRIP.GuthZahl.Basic.Restriction
import ExplicitRIP.GuthZahl.Components.Factors.Degree

/-!
# Irreducible factor data for the Guth–Zahl component argument

Every nonzero polynomial is a nonzero scalar times powers of pairwise relatively prime
irreducibles. Their degrees have sum at most the original total degree, and a line is
algebraically contained in the product exactly when it is contained in a factor.
-/

public section

namespace ExplicitRIP.GuthZahl

open Classical in
/-- Actual factorization data, including multiplicities and the scalar unit. -/
theorem irreducible_factor_data {K : Type*} [Field K] (P : Poly K) (hP : P ≠ 0) :
    ∃ m : ℕ, ∃ F : Fin m → Poly K, ∃ e : Fin m → ℕ, ∃ c : K,
      c ≠ 0 ∧ (∀ i, Irreducible (F i) ∧ 1 ≤ e i) ∧
      (∀ i j, i ≠ j → IsRelPrime (F i) (F j)) ∧
      P = MvPolynomial.C c * ∏ i, F i ^ e i := by
  classical
  let : NormalizationMonoid (Poly K) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid.toNormalizationMonoid
  let s := UniqueFactorizationMonoid.normalizedFactors P
  let q := s.toFinset.equivFin.symm
  let F : Fin s.toFinset.card → Poly K := fun i => (q i).1
  let e : Fin s.toFinset.card → ℕ := fun i => s.count (F i)
  have hmem (i : Fin s.toFinset.card) : F i ∈ s :=
    Multiset.mem_toFinset.mp (q i).2
  obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.prod_normalizedFactors hP
  obtain ⟨c, hc, huc⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp u.isUnit
  refine ⟨s.toFinset.card, F, e, c, hc.ne_zero, ?_, ?_, ?_⟩
  · intro i
    exact ⟨UniqueFactorizationMonoid.irreducible_of_normalized_factor _ (hmem i),
      Multiset.count_pos.mpr (hmem i)⟩
  · intro i j hij
    apply (UniqueFactorizationMonoid.irreducible_of_normalized_factor _
      (hmem i)).isRelPrime_iff_not_dvd.mpr
    intro hdvd
    have heq : F i = F j :=
      UniqueFactorizationMonoid.normalizedFactors_eq_of_dvd P _ (hmem i) _ (hmem j) hdvd
    exact hij (q.injective (Subtype.ext heq))
  · have hprod : (∏ i, F i ^ e i) = s.prod := by
      calc
        _ = ∏ x : s.toFinset, x.1 ^ s.count x.1 :=
          Fintype.prod_equiv q _ _ (fun _ => rfl)
        _ = ∏ x ∈ s.toFinset, x ^ s.count x :=
          Finset.prod_coe_sort s.toFinset (fun x => x ^ s.count x)
        _ = s.prod := (Finset.prod_multiset_count s).symm
    rw [hprod, ← huc, mul_comm]
    exact hu.symm

open Classical in
/-- Algebraic line containment, even over finite fields, and the degree ledger. -/
theorem irreducible_factor_line_degree {K : Type*} [Field K]
    (P : Poly K) (m : ℕ) (F : Fin m → Poly K) (e : Fin m → ℕ) (c : K)
    (hc : c ≠ 0) (hF : ∀ i, Irreducible (F i) ∧ 1 ≤ e i)
    (hP : P = MvPolynomial.C c * ∏ i, F i ^ e i) :
    (∑ i, (F i).totalDegree) ≤ P.totalDegree ∧
      (∀ i, 1 ≤ (F i).totalDegree) ∧
      ∀ L : Line K, LineOn P L ↔ ∃ i, LineOn (F i) L := by
  classical
  have hF0 (i : Fin m) : F i ≠ 0 := (hF i).1.ne_zero
  have he0 (i : Fin m) : e i ≠ 0 := Nat.ne_of_gt (hF i).2
  have hP0 : P ≠ 0 := by
    rw [hP]
    exact mul_ne_zero (MvPolynomial.C_ne_zero.mpr hc)
      (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hF0 i))
  refine ⟨?_, fun i => Factors.one_le_totalDegree_of_irreducible (hF i).1, ?_⟩
  · rw [← Factors.totalDegree_prod Finset.univ F (fun i _ => hF0 i)]
    apply MvPolynomial.totalDegree_le_of_dvd_of_isDomain _ hP0
    rw [hP]
    apply dvd_mul_of_dvd_right
    exact Finset.prod_dvd_prod_of_dvd F (fun i => F i ^ e i)
      (fun i _ => dvd_pow_self _ (he0 i))
  · intro L
    obtain ⟨a, ha, v, hv, hv0⟩ := line_exists_base_direction L
    simp_rw [lineOn_iff_restrictLine_eq_zero _ L a ha v hv hv0]
    rw [hP]
    simp only [restrictLine, map_mul, map_prod, map_pow, MvPolynomial.eval₂Hom_C,
      mul_eq_zero, Polynomial.C_eq_zero, hc, false_or,
      Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, pow_eq_zero_iff (he0 _)]

end ExplicitRIP.GuthZahl

end
