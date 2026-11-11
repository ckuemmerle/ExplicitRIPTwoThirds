/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Sampling.DegreeReduction.Selection
public import ExplicitRIP.GuthZahl.Sampling.DegreeReduction.WitnessCapture
public import ExplicitRIP.GuthZahl.Sampling.Removal

/-!
# Partial degree reduction

Sampling with parameter `4096 n / A²` supplies an interpolant whose degree
is strictly below the number of roots on every successful line.
-/

public section

namespace ExplicitRIP.GuthZahl

open Classical in
/-- Take q=4096*n/A^2. The sample interpolant has degree <=512*n/A, while a successful line has
>=2048*n/A distinct roots. -/
theorem partial_degree_reduction {K : Type*} [Field K]
    (Ls : Finset (Line K)) (A : ℝ) (hA : 0 < A)
    (hscale : 128 * Real.sqrt Ls.card ≤ A)
    (hpop : ∀ L ∈ Ls,
      A ≤ ((richPoints Ls 2 ∩ (L.1 : Set (Point K))).ncard : ℝ)) :
    ∃ f : Poly K, f ≠ 0 ∧ (f.totalDegree : ℝ) ≤ 512 * Ls.card / A ∧
      (f.totalDegree : ℝ) ≤ A / 4 ∧
      4 * (Ls.filter (fun L => ¬ LineOn f L)).card ≤ Ls.card := by
  by_cases hempty : Ls = ∅
  · subst Ls
    refine ⟨1, one_ne_zero, ?_, ?_, ?_⟩
    · simp only [MvPolynomial.totalDegree_one, Nat.cast_zero, Finset.card_empty,
        mul_zero, zero_div, le_refl]
    · simpa only [MvPolynomial.totalDegree_one, Nat.cast_zero] using
        (div_nonneg hA.le (by norm_num : (0 : ℝ) ≤ 4))
    · simp only [Finset.filter_empty, Finset.card_empty, mul_zero, le_refl]
  have hn : (0 : ℝ) < Ls.card := by
    exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hempty)
  have hAn : A ≤ Ls.card := by
    obtain ⟨L, hL⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    exact (hpop L hL).trans (Nat.cast_le.mpr
      ((rich_points_on_line_le Ls L hL).trans (Nat.sub_le _ _)))
  have hscaleSq : 16384 * (Ls.card : ℝ) ≤ A ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ 128 * Real.sqrt Ls.card) hscale 2
    norm_num only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg Ls.card)] at h
    exact h
  let q : ℝ := 4096 * Ls.card / A ^ 2
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hq1 : q ≤ 1 := by
    apply (div_le_one (sq_pos_of_pos hA)).mpr
    nlinarith only [hscaleSq, hn]
  have hqA : q * A = 4096 * Ls.card / A := by
    dsimp only [q]
    field_simp
  have hμ : 128 ≤ q * A := by
    rw [hqA]
    apply (le_div_iff₀ hA).mpr
    nlinarith only [hAn, hn]
  have hwitness (L : Line K) : ∃ W : Finset (Line K), L ∈ Ls →
      W ⊆ Ls ∧ A ≤ (W.card : ℝ) ∧
      ∀ (f : Poly K) (T : Finset (Line K)), (∀ M ∈ T, LineOn f M) →
        ¬ LineOn f L → (T ∩ W).card ≤ f.totalDegree := by
    by_cases hL : L ∈ Ls
    · obtain ⟨W, hsub, hcard, hroots⟩ := Sampling.DegreeReduction.exists_witness_set Ls L hL
      refine ⟨W, fun _ => ⟨hsub, ?_, hroots⟩⟩
      rw [hcard]
      exact hpop L hL
    · exact ⟨∅, fun h => False.elim (hL h)⟩
  choose W hW using hwitness
  obtain ⟨T, _, hsize, hbad⟩ := sample_hits_many_witness_sets Ls W A q hA hq hq1 hμ
    (fun L hL => ⟨(hW L hL).1, (hW L hL).2.1⟩)
  obtain ⟨f, hf, hdegree, hlines⟩ := interpolation_sqrt T
  have hsqrt : Real.sqrt T.card ≤ 128 * Ls.card / A := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 4 * q * Ls.card := hsize
      _ = _ := by dsimp only [q]; ring
  have hdeg : (f.totalDegree : ℝ) ≤ 512 * Ls.card / A := by
    calc
      _ ≤ 4 * Real.sqrt T.card := hdegree
      _ ≤ 4 * (128 * Ls.card / A) := mul_le_mul_of_nonneg_left hsqrt (by norm_num)
      _ = _ := by ring
  have hquarter : 512 * (Ls.card : ℝ) / A ≤ A / 4 := by
    apply (div_le_iff₀ hA).mpr
    nlinarith only [hscaleSq, hn]
  have hgap : (f.totalDegree : ℝ) < q * A / 2 := by
    calc
      _ ≤ 512 * Ls.card / A := hdeg
      _ < 2048 * Ls.card / A := by
        apply div_lt_div_of_pos_right _ hA
        nlinarith only [hn]
      _ = _ := by rw [hqA]; ring
  refine ⟨f, hf, hdeg, hdeg.trans hquarter, ?_⟩
  apply le_trans (Nat.mul_le_mul_left 4 (Finset.card_le_card ?_)) hbad
  intro L hL
  obtain ⟨hLs, hout⟩ := Finset.mem_filter.mp hL
  refine Finset.mem_filter.mpr ⟨hLs, ?_⟩
  have hroots : ((T ∩ W L).card : ℝ) ≤ f.totalDegree :=
    Nat.cast_le.mpr ((hW L hLs).2.2 f T hlines hout)
  -- The generic sampling theorem uses classical equality on its carrier.
  have hinter :
      @Inter.inter (Finset (Line K))
        (@Finset.instInter (Line K) (fun a b => propDecidable (a = b))) T (W L) =
      T ∩ W L := by
    ext M
    simp only [Finset.mem_inter]
  rw [hinter]
  exact hroots.trans_lt hgap

end ExplicitRIP.GuthZahl

end
