/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Sampling.DegreeReduction.Partial
import ExplicitRIP.GuthZahl.Basic.Restriction

/-!
# Explicit degree reduction for popular lines

At each stage, partial degree reduction removes at least three quarters of
the lines. The remaining lines retain three quarters of their richness.
Multiplying the successive interpolants gives degree at most `768 n / A`.
-/

public section

namespace ExplicitRIP.GuthZahl

open Classical in
/-- Strong induction on n using n'<=n/4 and A'=3A/4. 512 + 768/3 = 768 closes the degree budget. -/
theorem degree_reduction_explicit {K : Type*} [Field K]
    (Ls : Finset (Line K)) (A : ℝ) (hA : 0 < A)
    (hscale : 128 * Real.sqrt Ls.card ≤ A)
    (hpop : ∀ L ∈ Ls,
      A ≤ ((richPoints Ls 2 ∩ (L.1 : Set (Point K))).ncard : ℝ)) :
    ∃ f : Poly K, f ≠ 0 ∧ (f.totalDegree : ℝ) ≤ 768 * Ls.card / A ∧
      ∀ L ∈ Ls, LineOn f L := by
  revert A
  refine Finset.strongInductionOn Ls ?_
  intro Ls ih A hA hscale hpop
  by_cases hempty : Ls = ∅
  · subst Ls
    refine ⟨1, one_ne_zero, ?_, ?_⟩
    · simp only [MvPolynomial.totalDegree_one, Nat.cast_zero, Finset.card_empty,
        mul_zero, zero_div, le_refl]
    · intro L hL
      exact False.elim (Finset.notMem_empty L hL)
  have hn : 0 < Ls.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hempty)
  obtain ⟨f, hf, hdegree, hquarter, hremaining⟩ :=
    partial_degree_reduction Ls A hA hscale hpop
  let Rs := Ls.filter (fun L => ¬ LineOn f L)
  have hRcard : 4 * Rs.card ≤ Ls.card := hremaining
  have hRlt : Rs.card < Ls.card := by omega
  have hRsub : Rs ⊂ Ls := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro heq
    have := congrArg Finset.card heq
    omega
  have hRreal : 4 * (Rs.card : ℝ) ≤ Ls.card := by exact_mod_cast hRcard
  have hsqrt : Real.sqrt Rs.card ≤ Real.sqrt Ls.card / 2 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hs := Real.sq_sqrt (Nat.cast_nonneg Ls.card)
    nlinarith only [hRreal, hs]
  have hAscale : 128 * Real.sqrt Rs.card ≤ 3 * A / 4 := by
    have h := mul_le_mul_of_nonneg_left hsqrt (by norm_num : (0 : ℝ) ≤ 128)
    linarith only [h, hscale, hA]
  have hApop : ∀ L ∈ Rs,
      3 * A / 4 ≤ ((richPoints Rs 2 ∩ (L.1 : Set (Point K))).ncard : ℝ) := by
    intro L hL
    obtain ⟨hLs, hout⟩ := Finset.mem_filter.mp hL
    have hloss := rich_points_after_polynomial_removal Ls f L hLs hout
    have hloss' : ((richPoints Ls 2 ∩ (L.1 : Set (Point K))).ncard : ℝ) ≤
        (richPoints Rs 2 ∩ (L.1 : Set (Point K))).ncard + (f.totalDegree : ℝ) := by
      exact_mod_cast hloss
    linarith only [hpop L hLs, hloss', hquarter]
  obtain ⟨g, hg, hgdegree, hglines⟩ :=
    ih Rs hRsub (3 * A / 4) (by positivity) hAscale hApop
  refine ⟨f * g, mul_ne_zero hf hg, ?_, ?_⟩
  · have hmul : ((f * g).totalDegree : ℝ) ≤ f.totalDegree + (g.totalDegree : ℝ) := by
      exact_mod_cast MvPolynomial.totalDegree_mul f g
    have hgbound : 768 * (Rs.card : ℝ) / (3 * A / 4) ≤ 256 * Ls.card / A := by
      have heq : 768 * (Rs.card : ℝ) / (3 * A / 4) = (256 * (4 * Rs.card)) / A := by
        field_simp
        ring
      rw [heq]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hRreal (by norm_num)) hA.le
    calc
      _ ≤ (f.totalDegree : ℝ) + g.totalDegree := hmul
      _ ≤ 512 * Ls.card / A + 256 * Ls.card / A :=
        add_le_add hdegree (hgdegree.trans hgbound)
      _ = _ := by ring
  · intro L hL
    by_cases hLf : LineOn f L
    · exact lineOn_of_dvd (dvd_mul_right f g) hLf
    · exact lineOn_of_dvd (dvd_mul_left g f)
        (hglines L (Finset.mem_filter.mpr ⟨hL, hLf⟩))

open Classical in
/-- Probabilistic degree reduction for lines, the case `D = 1` of [GZ, Proposition 12.4],
with explicit constants. -/
theorem degree_reduction :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧ ∀ (K : Type*) [Field K]
      (Ls : Finset (Line K)) (A : ℝ), 0 < A → C₀ * Real.sqrt Ls.card ≤ A →
      (∀ L ∈ Ls, A ≤ ((richPoints Ls 2 ∩ (L.1 : Set (Point K))).ncard : ℝ)) →
      ∃ f : Poly K, f ≠ 0 ∧ (f.totalDegree : ℝ) ≤ C₁ * Ls.card / A ∧
        ∀ L ∈ Ls, LineOn f L := by
  refine ⟨128, 768, by norm_num, by norm_num, ?_⟩
  intro K _ Ls A hA hscale hpop
  exact degree_reduction_explicit Ls A hA hscale hpop

end ExplicitRIP.GuthZahl

end
