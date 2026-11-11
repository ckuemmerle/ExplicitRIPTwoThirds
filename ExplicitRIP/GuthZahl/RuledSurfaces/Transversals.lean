/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.RuledSurfaces.QuadraticInterpolation
public import ExplicitRIP.GuthZahl.RuledSurfaces.LeadingRestriction
public import ExplicitRIP.GuthZahl.RuledSurfaces.AffineGeometry

/-!
# Common transversals of three skew lines

A quadric containing three skew lines contains every common transversal. Three
affine intersections give three roots. If one intersection is at infinity,
parallelism kills the quadratic coefficient and two affine roots suffice.
-/

public section

namespace ExplicitRIP.GuthZahl.RuledSurfaces

variable {K : Type*} [Field K]

/-- More distinct zero points than the restriction degree force containment. -/
theorem lineOn_of_restriction_degree_lt_card {ι : Type*} [Fintype ι]
    {f : Poly K} {L : Line K} {a v : Point K}
    (ha : a ∈ L.1) (hv : v ∈ L.1.direction) (hv0 : v ≠ 0)
    (x : ι → Point K) (hx : Function.Injective x) (hxL : ∀ i, x i ∈ L.1)
    (hzero : ∀ i, MvPolynomial.eval (x i) f = 0)
    (hdegree : (restrictLine f a v).natDegree < Fintype.card ι) : LineOn f L := by
  classical
  choose t ht using fun i => (mem_line_iff_exists_smul ha hv hv0 (x i)).mp (hxL i)
  have htinj : Function.Injective t := by
    intro i j hij
    apply hx
    rw [← ht i, ← ht j, hij]
  apply (lineOn_iff_restrictLine_eq_zero f _ _ ha _ hv hv0).mpr
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ htinj
  · intro i
    rw [eval_restrictLine, ht i]
    exact hzero i
  · exact hdegree

/-- More distinct zeros than total degree on a line force containment. -/
theorem lineOn_of_totalDegree_lt_card {ι : Type*} [Fintype ι]
    {f : Poly K} {L : Line K} (x : ι → Point K) (hx : Function.Injective x)
    (hxL : ∀ i, x i ∈ L.1) (hzero : ∀ i, MvPolynomial.eval (x i) f = 0)
    (hdegree : f.totalDegree < Fintype.card ι) : LineOn f L := by
  obtain ⟨a, v, ha, hv, hv0, hparam⟩ := exists_line_parametrization L
  exact lineOn_of_restriction_degree_lt_card ha hv hv0 x hx hxL hzero
    ((restrictLine_natDegree_le _ _ _).trans_lt hdegree)

/-- Points chosen on pairwise skew lines are distinct. -/
theorem injective_points_on_skew_lines {ι : Type*} (Ls : ι → Line K)
    (hskew : ∀ i j, i ≠ j → ¬ Coplanar (Ls i) (Ls j))
    (x : ι → Point K) (hx : ∀ i, x i ∈ (Ls i).1) : Function.Injective x := by
  intro i j hij
  by_contra hne
  have hneL := ne_of_not_coplanar (hskew i j hne)
  apply hskew i j hne
  have hxj := hx j
  rw [← hij] at hxj
  exact coplanar_of_mem_of_ne (hx i) hxj hneL

/-- Three affine intersections with skew lines force a quadratic polynomial to contain a line. -/
theorem lineOn_of_three_affine_intersections {q : Poly K} (hdegree : q.totalDegree ≤ 2)
    (A B C L : Line K) (hAB : ¬ Coplanar A B) (hAC : ¬ Coplanar A C)
    (hBC : ¬ Coplanar B C) (hA : LineOn q A) (hB : LineOn q B) (hC : LineOn q C)
    (hLA : ((L.1 : Set (Point K)) ∩ A.1).Nonempty)
    (hLB : ((L.1 : Set (Point K)) ∩ B.1).Nonempty)
    (hLC : ((L.1 : Set (Point K)) ∩ C.1).Nonempty) : LineOn q L := by
  obtain ⟨a, haL, haA⟩ := hLA
  obtain ⟨b, hbL, hbB⟩ := hLB
  obtain ⟨c, hcL, hcC⟩ := hLC
  have hab : a ≠ b := by
    rintro rfl
    exact hAB (coplanar_of_mem_of_ne haA hbB (ne_of_not_coplanar hAB))
  have hac : a ≠ c := by
    rintro rfl
    exact hAC (coplanar_of_mem_of_ne haA hcC (ne_of_not_coplanar hAC))
  have hbc : b ≠ c := by
    rintro rfl
    exact hBC (coplanar_of_mem_of_ne hbB hcC (ne_of_not_coplanar hBC))
  apply lineOn_of_totalDegree_lt_card ![a, b, c]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i
    fin_cases i <;> assumption
  · intro i
    fin_cases i
    · exact eval_eq_zero_of_lineOn hA haA
    · exact eval_eq_zero_of_lineOn hB hbB
    · exact eval_eq_zero_of_lineOn hC hcC
  · simpa only [Fintype.card_fin] using Nat.lt_succ_of_le hdegree

/-- A parallel contained line and two other affine intersections force quadratic containment. -/
theorem lineOn_of_parallel_and_two_intersections {q : Poly K} (hdegree : q.totalDegree ≤ 2)
    (P A B L : Line K) (hAB : ¬ Coplanar A B)
    (hP : LineOn q P) (hA : LineOn q A) (hB : LineOn q B)
    (hparallel : L.1.direction = P.1.direction)
    (hLA : ((L.1 : Set (Point K)) ∩ A.1).Nonempty)
    (hLB : ((L.1 : Set (Point K)) ∩ B.1).Nonempty) : LineOn q L := by
  obtain ⟨x, hxL, hxA⟩ := hLA
  obtain ⟨y, hyL, hyB⟩ := hLB
  have hxy : x ≠ y := by
    rintro rfl
    exact hAB (coplanar_of_mem_of_ne hxA hyB (ne_of_not_coplanar hAB))
  obtain ⟨a, v, ha, hv, hv0, hparam⟩ := exists_line_parametrization L
  have hcoeff := coeff_restrictLine_eq_zero_of_parallel hdegree hP hparallel a v hv
  have hdeg : (restrictLine q a v).natDegree ≤ 1 := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    by_cases heq : n = 2
    · simpa only [heq] using hcoeff
    · apply Polynomial.coeff_eq_zero_of_natDegree_lt
      exact (restrictLine_natDegree_le _ _ _).trans hdegree |>.trans_lt (by omega)
  apply lineOn_of_restriction_degree_lt_card ha hv hv0 ![x, y]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i
    fin_cases i <;> assumption
  · intro i
    fin_cases i
    · exact eval_eq_zero_of_lineOn hA hxA
    · exact eval_eq_zero_of_lineOn hB hyB
  · simpa only [Fintype.card_fin] using Nat.lt_succ_of_le hdeg

/-- A quadratic polynomial through three skew lines contains every common transversal. -/
theorem lineOn_of_coplanar_skew_triple {q : Poly K} (hdegree : q.totalDegree ≤ 2)
    (A B C : Line K) (hAB : ¬ Coplanar A B) (hAC : ¬ Coplanar A C)
    (hBC : ¬ Coplanar B C) (hA : LineOn q A) (hB : LineOn q B) (hC : LineOn q C)
    (L : Line K) (hLA : Coplanar L A) (hLB : Coplanar L B) (hLC : Coplanar L C) :
    LineOn q L := by
  have hmeet {P Q : Line K} (hPQ : ¬ Coplanar P Q)
      (hpar : L.1.direction = P.1.direction) (hLQ : Coplanar L Q) :
      ((L.1 : Set (Point K)) ∩ Q.1).Nonempty := by
    rcases inter_nonempty_or_direction_eq_of_coplanar hLQ with h | h
    · exact h
    · exact False.elim (hPQ (coplanar_of_direction_eq (hpar.symm.trans h)))
  rcases inter_nonempty_or_direction_eq_of_coplanar hLA with hia | hpa
  · rcases inter_nonempty_or_direction_eq_of_coplanar hLB with hib | hpb
    · rcases inter_nonempty_or_direction_eq_of_coplanar hLC with hic | hpc
      · exact lineOn_of_three_affine_intersections hdegree A B C L hAB hAC hBC
          hA hB hC hia hib hic
      · exact lineOn_of_parallel_and_two_intersections hdegree C A B L hAB
          hC hA hB hpc hia hib
    · exact lineOn_of_parallel_and_two_intersections hdegree B A C L hAC
        hB hA hC hpb hia (hmeet hBC hpb hLC)
  · exact lineOn_of_parallel_and_two_intersections hdegree A B C L hBC
      hA hB hC hpa (hmeet hAB hpa hLB) (hmeet hAC hpa hLC)

/-- Three skew lines determine a quadric containing all of their common transversals. -/
theorem exists_quadric_containing_common_transversals [Infinite K] (A B C : Line K)
    (hAB : ¬ Coplanar A B) (hAC : ¬ Coplanar A C) (hBC : ¬ Coplanar B C) :
    ∃ q : Poly K, Irreducible q ∧ q.totalDegree = 2 ∧ LineOn q A ∧ LineOn q B ∧
      LineOn q C ∧ ∀ L : Line K,
        Coplanar L A → Coplanar L B → Coplanar L C → LineOn q L := by
  obtain ⟨q, hq, hdegree, hA, hB, hC⟩ :=
    exists_irreducible_quadric_of_skew_triple A B C hAB hAC hBC
  exact ⟨q, hq, hdegree, hA, hB, hC,
    lineOn_of_coplanar_skew_triple hdegree.le A B C hAB hAC hBC hA hB hC⟩

end ExplicitRIP.GuthZahl.RuledSurfaces
end
