/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Components.Defs
import ExplicitRIP.GuthZahl.Basic
import ExplicitRIP.GuthZahl.Components.Lemmas
import ExplicitRIP.GuthZahl.Components.Factors
import ExplicitRIP.GuthZahl.Components.CommonLineCounts
import ExplicitRIP.GuthZahl.Components.Selection.Counting
import ExplicitRIP.GuthZahl.Sampling.Moments

/-!
# Retained richness and deterministic component selection

The root bound controls rich points lost from a unique-factor family. Removing
multiply-contained lines then permits selection by the squared component degrees.
-/

public section

namespace ExplicitRIP.GuthZahl

open Classical in
/-- The root bound controls the rich points lost to the other factors, giving the
retained-richness estimate. -/
theorem unique_factor_richness_loss {K : Type*} [Field K] {m : ℕ}
    (Ls : Finset (Line K)) (F : Fin m → Poly K)
    (hcover : ∀ L ∈ Ls, ∃ i, LineOn (F i) L)
    (i : Fin m) (L : Line K) (hL : L ∈ uniqueFactorLines Ls F i) :
    (richPoints Ls 2 ∩ (L.1 : Set (Point K))).ncard ≤
      (richPoints (uniqueFactorLines Ls F i) 2 ∩ (L.1 : Set (Point K))).ncard +
        ∑ j, (F j).totalDegree := by
  let Q := ∏ j ∈ Finset.univ.erase i, F j
  have hQ : ¬ LineOn Q L := by
    obtain ⟨a, ha, v, hv, hv0⟩ := line_exists_base_direction L
    have hrestr : ∀ j ∈ Finset.univ.erase i, restrictLine (F j) a v ≠ 0 := by
      intro j hj hzero
      exact (Finset.mem_filter.mp hL).2.2 j (Finset.mem_erase.mp hj).1
        ((lineOn_iff_restrictLine_eq_zero (F j) L a ha v hv hv0).mpr hzero)
    intro h
    apply (Finset.prod_ne_zero_iff.mpr hrestr)
    simpa only [Q, restrictLine, map_prod] using h a ha v hv
  obtain ⟨hzeros, hbound⟩ := line_hypersurface_bound Q L hQ
  have hdegree : Q.totalDegree ≤ ∑ j, (F j).totalDegree :=
    (MvPolynomial.totalDegree_finsetProd (Finset.univ.erase i) F).trans
      (Finset.sum_le_sum_of_subset (Finset.erase_subset i Finset.univ))
  have hremaining :
      (richPoints (uniqueFactorLines Ls F i) 2 ∩ (L.1 : Set (Point K))).Finite :=
    (richPoints_finite (uniqueFactorLines Ls F i) 2 le_rfl).inter_of_left _
  have hsub : richPoints Ls 2 ∩ (L.1 : Set (Point K)) ⊆
      (richPoints (uniqueFactorLines Ls F i) 2 ∩ (L.1 : Set (Point K))) ∪
        {x : Point K | x ∈ L.1 ∧ MvPolynomial.eval x Q = 0} := by
    intro x hx
    by_cases hretained : x ∈ richPoints (uniqueFactorLines Ls F i) 2
    · exact Or.inl ⟨hretained, hx.2⟩
    · exact Or.inr (unique_factor_point_loss Ls F hcover i L hL ⟨hx, hretained⟩)
  calc
    _ ≤ ((richPoints (uniqueFactorLines Ls F i) 2 ∩ (L.1 : Set (Point K))) ∪
        {x : Point K | x ∈ L.1 ∧ MvPolynomial.eval x Q = 0}).ncard :=
      Set.ncard_le_ncard hsub (hremaining.union hzeros)
    _ ≤ (richPoints (uniqueFactorLines Ls F i) 2 ∩ (L.1 : Set (Point K))).ncard +
        {x : Point K | x ∈ L.1 ∧ MvPolynomial.eval x Q = 0}.ncard :=
      Set.ncard_union_le _ _
    _ ≤ _ := Nat.add_le_add_left (hbound.trans hdegree) _

open Classical in
/-- Deterministic component selection. The two displayed degree inequalities are arithmetic data
for a supplied interpolant; `popular_lines_charSquare` constructs that interpolant. -/
theorem component_for_contagion {K : Type*} [Field K] [IsAlgClosed K]
    (M r : ℕ) (hM : 1 ≤ M) (Ls : Finset (Line K)) (hne : Ls.Nonempty)
    (P : Poly K) (hP : P ≠ 0) (hcontain : ∀ L ∈ Ls, LineOn P L)
    (A : ℝ) (hA : 0 < A)
    (hpop : ∀ L ∈ Ls,
      A ≤ ((richPoints Ls 2 ∩ (L.1 : Set (Point K))).ncard : ℝ))
    (hdegreeSquared : 2 * M * P.totalDegree ^ 2 ≤ Ls.card)
    (hdegree : (2 * M * P.totalDegree : ℕ) ≤ A) :
    ∃ f : Poly K, ∃ G : Finset (Line K), Irreducible f ∧ G ⊆ Ls ∧
      f.totalDegree ≤ P.totalDegree ∧ A / 2 ≤ (G.card : ℝ) ∧
      M * f.totalDegree ^ 2 ≤ G.card ∧
      ∀ L ∈ G, LineOn f L ∧
        M * f.totalDegree ≤ {x : Point K | x ∈ L.1 ∧ TwoTangentDirections f x r}.encard := by
  obtain ⟨m, F, e, c, hc, hF, hcop, hfactor⟩ := irreducible_factor_data P hP
  obtain ⟨hsum, hpositive, hfactorLines⟩ :=
    irreducible_factor_line_degree P m F e c hc hF hfactor
  have hcover : ∀ L ∈ Ls, ∃ i, LineOn (F i) L :=
    fun L hL => (hfactorLines L).mp (hcontain L hL)
  have hdegrees (i : Fin m) : (F i).totalDegree ≤ P.totalDegree :=
    (Finset.single_le_sum (fun j _ => Nat.zero_le (F j).totalDegree)
      (Finset.mem_univ i)).trans hsum
  have hD : 0 < P.totalDegree := by
    obtain ⟨L, hL⟩ := hne
    obtain ⟨i, _⟩ := hcover L hL
    exact (hpositive i).trans (hdegrees i)
  -- At least half of the original lines belong to unique-factor families.
  have hmultiple : (multipleFactorLines Ls F).card ≤ P.totalDegree ^ 2 :=
    (multiply_contained_lines_bound Ls F (fun i => (hF i).1.ne_zero) hcop).trans
      (Nat.pow_le_pow_left hsum 2)
  have hcount := Components.Selection.card_le_multiple_add_sum_unique Ls F hcover
  have htwice : 2 * (multipleFactorLines Ls F).card ≤ Ls.card := by
    calc
      _ ≤ 2 * P.totalDegree ^ 2 := Nat.mul_le_mul_left 2 hmultiple
      _ ≤ 2 * M * P.totalDegree ^ 2 :=
        Nat.mul_le_mul_right _ (by omega : 2 ≤ 2 * M)
      _ ≤ _ := hdegreeSquared
  have hhalf : Ls.card ≤ 2 * ∑ i, (uniqueFactorLines Ls F i).card := by
    omega
  obtain ⟨i, hi, hselected⟩ := degree_squared_pigeonhole m Ls.card P.totalDegree
    (fun i => (uniqueFactorLines Ls F i).card) (fun i => (F i).totalDegree)
    (Finset.card_pos.mpr hne) hD hpositive hsum hhalf
  have hsize : M * (F i).totalDegree ^ 2 ≤ (uniqueFactorLines Ls F i).card := by
    apply (mul_le_mul_iff_right₀ (by positivity : 0 < 2 * P.totalDegree ^ 2)).mp
    calc
      2 * P.totalDegree ^ 2 * (M * (F i).totalDegree ^ 2) =
          (2 * M * P.totalDegree ^ 2) * (F i).totalDegree ^ 2 := by ring
      _ ≤ Ls.card * (F i).totalDegree ^ 2 :=
        Nat.mul_le_mul_right _ hdegreeSquared
      _ ≤ _ := hselected
  -- The degree bound leaves at least half the original richness on each retained line.
  have hMD : ((M * P.totalDegree : ℕ) : ℝ) ≤ A / 2 := by
    have heq : ((2 * M * P.totalDegree : ℕ) : ℝ) =
        2 * ((M * P.totalDegree : ℕ) : ℝ) := by push_cast; ring
    rw [heq] at hdegree
    linarith only [hdegree]
  have hDhalf : (P.totalDegree : ℝ) ≤ A / 2 := by
    have hMreal : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hdiv : (P.totalDegree : ℝ) ≤ (A / 2) / (M : ℝ) := by
      apply (le_div_iff₀ (lt_of_lt_of_le zero_lt_one hMreal)).mpr
      simpa only [Nat.cast_mul, mul_comm] using hMD
    exact hdiv.trans (div_le_self (half_pos hA).le hMreal)
  have hretained (j : Fin m) (L : Line K) (hL : L ∈ uniqueFactorLines Ls F j) :
      A / 2 ≤ ((richPoints (uniqueFactorLines Ls F j) 2 ∩
        (L.1 : Set (Point K))).ncard : ℝ) := by
    have hloss := unique_factor_richness_loss Ls F hcover j L hL
    have hlossR : ((richPoints Ls 2 ∩ (L.1 : Set (Point K))).ncard : ℝ) ≤
        ((richPoints (uniqueFactorLines Ls F j) 2 ∩ (L.1 : Set (Point K))).ncard : ℝ) +
          ((∑ k, (F k).totalDegree : ℕ) : ℝ) := by exact_mod_cast hloss
    have hsumR : ((∑ k, (F k).totalDegree : ℕ) : ℝ) ≤ A / 2 :=
      (Nat.cast_le.mpr hsum).trans hDhalf
    have hpopL := hpop L (Finset.mem_filter.mp hL).1
    linarith only [hpopL, hlossR, hsumR]
  refine ⟨F i, uniqueFactorLines Ls F i, (hF i).1,
    Finset.filter_subset _ _, hdegrees i, ?_, hsize, ?_⟩
  · obtain ⟨L, hL⟩ := Finset.card_pos.mp hi
    have hret := hretained i L hL
    have hbound := (rich_points_on_line_le (uniqueFactorLines Ls F i) L hL).trans
      (Nat.sub_le _ _)
    exact hret.trans (Nat.cast_le.mpr hbound)
  · intro L hL
    refine ⟨(Finset.mem_filter.mp hL).2.1, ?_⟩
    have hMd : ((M * (F i).totalDegree : ℕ) : ℝ) ≤ A / 2 :=
      (Nat.cast_le.mpr (Nat.mul_le_mul_left M (hdegrees i))).trans hMD
    have hrich : M * (F i).totalDegree ≤
        (richPoints (uniqueFactorLines Ls F i) 2 ∩ (L.1 : Set (Point K))).ncard := by
      exact_mod_cast hMd.trans (hretained i L hL)
    have hsub : richPoints (uniqueFactorLines Ls F i) 2 ∩ (L.1 : Set (Point K)) ⊆
        {x : Point K | x ∈ L.1 ∧ TwoTangentDirections (F i) x r} := by
      intro x hx
      exact ⟨hx.2, rich_point_two_tangent_directions (F i) (uniqueFactorLines Ls F i)
        (fun N hN => (Finset.mem_filter.mp hN).2.1) x hx.1 r⟩
    calc
      (M : ℕ∞) * (F i).totalDegree = ((M * (F i).totalDegree : ℕ) : ℕ∞) :=
        (Nat.cast_mul _ _).symm
      _ ≤ ((richPoints (uniqueFactorLines Ls F i) 2 ∩
          (L.1 : Set (Point K))).ncard : ℕ∞) := Nat.cast_le.mpr hrich
      _ ≤ (richPoints (uniqueFactorLines Ls F i) 2 ∩
          (L.1 : Set (Point K))).encard := Set.ncard_le_encard _
      _ ≤ _ := Set.encard_le_encard hsub

end ExplicitRIP.GuthZahl

end
