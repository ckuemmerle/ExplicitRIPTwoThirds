/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Defs
import ExplicitRIP.GuthZahl.Contagion.Boolean
import ExplicitRIP.GuthZahl.Jets.NormalForm
import ExplicitRIP.GuthZahl.Components.Selection
import ExplicitRIP.GuthZahl.Components.Lemmas
import ExplicitRIP.GuthZahl.Trapping.Main
import ExplicitRIP.GuthZahl.Structure.Tangency
import ExplicitRIP.GuthZahl.Structure.Constants
import ExplicitRIP.GuthZahl.Structure.Peeling
import ExplicitRIP.GuthZahl.Sampling.DegreeReduction
import ExplicitRIP.GuthZahl.RuledSurfaces

/-!
# The line case of [GZ, Theorem 3.8]

Boolean contagion and uniform trapping promote a popular irreducible component
to a doubly ruled surface. Degree reduction and deletion give the structure
dichotomy throughout the characteristic-square range.
-/

public section

namespace ExplicitRIP.GuthZahl

open Classical in
/-- Two-stage contagion (points to lines to an irreducible surface). -/
theorem flecnode_contagion (r : ℕ) :
    ∃ M : ℕ, 0 < M ∧ ∀ (K : Type*) [Field K] [IsAlgClosed K]
      (f : Poly K) (Ls : Finset (Line K)), Irreducible f →
      M * f.totalDegree ^ 2 ≤ Ls.card →
      (∀ L ∈ Ls, LineOn f L ∧
        M * f.totalDegree ≤ {x : Point K | x ∈ L.1 ∧ TwoTangentDirections f x r}.encard) →
      ∃ g : Poly K, ¬ f ∣ g ∧ (principalOpen f g).Nonempty ∧
        ∀ x ∈ principalOpen f g, TwoTangentDirections f x r := by
  obtain ⟨b, hb, hnormal⟩ := two_flecnode_normal_form r
  refine ⟨4 * b ^ 2 + 1, by omega, ?_⟩
  intro K _ _ f Ls hf hcard hLs
  obtain ⟨J, hJ, qs, B, hdeg, hiff⟩ := hnormal K f
  have haccepted (L : Line K) (hL : L ∈ Ls) : LineOn f L ∧
      (((4 * b ^ 2 + 1) * f.totalDegree : ℕ) : ℕ∞) ≤
        {x : Point K | x ∈ L.1 ∧ zeroPattern qs x ∈ B}.encard := by
    simpa only [← hiff, Nat.cast_mul] using hLs L hL
  obtain ⟨g, hfg, hne, hg⟩ :=
    bounded_boolean_contagion b J hb hJ f hf qs hdeg B Ls hcard haccepted
  exact ⟨g, hfg, hne, fun x hx => (hiff x).mpr (hg x hx)⟩

open Classical in
/-- A sufficiently rich family on a low-degree hypersurface has many lines on one irreducible doubly
ruled component. -/
theorem popular_surface_from_low_degree :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ (p : ℕ) [Fact p.Prime]
      (K : Type*) [Field K] [IsAlgClosed K] [CharP K p]
      (Ls : Finset (Line K)), Ls.Nonempty →
      ∀ (P : Poly K), P ≠ 0 → P.totalDegree < p →
      (∀ L ∈ Ls, LineOn P L) → ∀ A : ℝ, 0 < A →
      (∀ L ∈ Ls, A ≤ ((richPoints Ls 2 ∩ (L.1 : Set (Point K))).ncard : ℝ)) →
      2 * M * P.totalDegree ^ 2 ≤ Ls.card → (2 * M * P.totalDegree : ℕ) ≤ A →
      ∃ f : Poly K, Irreducible f ∧ DoublyRuled f ∧
        A / 2 ≤ ((Ls.filter (LineOn f)).card : ℝ) := by
  obtain ⟨r, _, htrap⟩ := uniform_generic_trapping
  obtain ⟨M, hM, hcontagion⟩ := flecnode_contagion r
  refine ⟨M, hM, ?_⟩
  intro p _ K _ _ _ Ls hne P hP hDp hcontain A hA hpop hsquared hdegree
  obtain ⟨f, G, hf, hG, hDf, hGcard, hsize, hlines⟩ :=
    component_for_contagion M r hM Ls hne P hP hcontain A hA hpop hsquared hdegree
  obtain ⟨g, hfg, _, hg⟩ := htrap p K f hf (hDf.trans_lt hDp)
  obtain ⟨h, hfh, _, hh⟩ := hcontagion K f G hf hsize hlines
  obtain ⟨hprod, hopen, heq⟩ := principalOpen_intersection f g h hf hfg hfh
  refine ⟨f, hf, ⟨g * h, hprod, hopen, ?_⟩, ?_⟩
  · intro x hx
    rw [heq] at hx
    exact Structure.two_lines_of_trapped_directions f x r (hh x hx.2) (hg x hx.1)
  · apply hGcard.trans
    exact_mod_cast Finset.card_le_card (show G ⊆ Ls.filter (LineOn f) from
      fun L hL => Finset.mem_filter.mpr ⟨hG hL, (hlines L hL).1⟩)

open Classical in
/-- For at most `p²` lines, a sufficiently large richness threshold produces an irreducible doubly
ruled surface containing many of them. The threshold makes the interpolating polynomial have
degree below `p`. -/
theorem popular_lines_charSquare :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [IsAlgClosed K] [CharP K p]
        (Ls : Finset (Line K)) (A : ℝ), Ls.Nonempty → Ls.card ≤ p ^ 2 →
        C₀ * Real.sqrt Ls.card ≤ A →
        (∀ L ∈ Ls, A ≤ ((richPoints Ls 2 ∩ (L.1 : Set (Point K))).ncard : ℝ)) →
        ∃ f : Poly K, Irreducible f ∧ DoublyRuled f ∧
          A / 2 ≤ ((Ls.filter (LineOn f)).card : ℝ) := by
  obtain ⟨M, hM, hpopular⟩ := popular_surface_from_low_degree
  refine ⟨1536 * ((M : ℝ) + 1), by positivity, ?_⟩
  intro p _ K _ _ _ Ls A hne hn hscale hpop
  have hcard : 0 < Ls.card := Finset.card_pos.mpr hne
  have hs : 0 < Real.sqrt (Ls.card : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hcard)
  have hA : 0 < A := (mul_pos (by positivity) hs).trans_le hscale
  have hscale' : 128 * Real.sqrt (Ls.card : ℝ) ≤ A := by
    apply le_trans _ hscale
    exact mul_le_mul_of_nonneg_right (by nlinarith only [Nat.cast_nonneg (α := ℝ) M]) hs.le
  obtain ⟨P, hP, hdegree, hcontain⟩ := degree_reduction_explicit Ls A hA hscale' hpop
  obtain ⟨hchar, hsquared, hlinear⟩ :=
    Structure.degree_reduction_thresholds M Ls.card P.totalDegree p hM hcard hn A hA
      hscale hdegree
  exact hpopular p K Ls hne P hP hchar hcontain A hA hpop hsquared hlinear

open Classical in
/-- The line-only structure dichotomy for at most `p²` lines. The constants in the formal proof
are chosen so that enlarging the popularity threshold makes the degree-reduction polynomial
have degree strictly below `p` throughout the range `n ≤ p²`. -/
theorem guthZahl_lines_charSquare :
    ∃ C : ℝ, 0 < C ∧
      ∀ (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [IsAlgClosed K] [CharP K p]
        (Ls : Finset (Line K)), Ls.card ≤ p ^ 2 →
        ∀ A : ℝ, C * Real.sqrt Ls.card ≤ A →
          ((richPoints Ls 2).ncard : ℝ) ≤ C * A * Ls.card ∨
          ∃ f : Poly K, Irreducible f ∧ DoublyRuled f ∧ f.totalDegree ≤ 2 ∧
            A ≤ ((Ls.filter (LineOn f)).card : ℝ) := by
  obtain ⟨C₀, hC₀, hpopular⟩ := popular_lines_charSquare
  let C := max C₀ 2
  have hC₂ : 2 ≤ C := le_max_right _ _
  have hC₀C : C₀ ≤ C := le_max_left _ _
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) hC₂
  refine ⟨C, hC, ?_⟩
  intro p _ K _ _ _ Ls hn A hscale
  by_cases hne : Ls.Nonempty
  · have hcard : 0 < Ls.card := Finset.card_pos.mpr hne
    have hs : 0 < Real.sqrt (Ls.card : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hcard)
    have hA : 0 < A := (mul_pos hC hs).trans_le hscale
    by_cases hp : p = 2
    · left
      have hn₄ : (Ls.card : ℝ) ≤ 4 := by norm_num [hp] at hn; exact_mod_cast hn
      have hs₁ : 1 ≤ Real.sqrt (Ls.card : ℝ) := by
        apply Real.le_sqrt_of_sq_le
        norm_num only [one_pow]
        exact_mod_cast hcard
      have hA₂ : 2 ≤ A := hC₂.trans
        ((le_mul_of_one_le_right hC.le hs₁).trans hscale)
      have hCA : 4 ≤ C * A := by
        calc
          4 = (2 : ℝ) * 2 := by norm_num
          _ ≤ C * A := mul_le_mul hC₂ hA₂ (by norm_num) hC.le
      calc
        _ ≤ (Ls.card : ℝ) ^ 2 := Structure.richPoints_ncard_le_card_sq Ls
        _ ≤ C * A * Ls.card := by
          simpa only [pow_two] using
            mul_le_mul_of_nonneg_right (hn₄.trans hCA) (Nat.cast_nonneg Ls.card)
    · have htwo : (2 : K) ≠ 0 := by
        intro hzero
        have hdiv : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp (by simpa using hzero)
        have hle := Nat.le_of_dvd (by decide : 0 < 2) hdiv
        have hprime : p.Prime := Fact.out
        exact hp (Nat.le_antisymm hle hprime.two_le)
      rcases Structure.count_or_popular_subset Ls (2 * A) with hcount | ⟨Rs, hRs, hRne, hRpop⟩
      · left
        exact hcount.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hC₂ hA.le) (Nat.cast_nonneg Ls.card))
      · right
        have hRcard := Finset.card_le_card hRs
        have hRscale : C₀ * Real.sqrt (Rs.card : ℝ) ≤ 2 * A := by
          calc
            _ ≤ C₀ * Real.sqrt (Ls.card : ℝ) :=
              mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast hRcard)) hC₀.le
            _ ≤ C * Real.sqrt (Ls.card : ℝ) :=
              mul_le_mul_of_nonneg_right hC₀C hs.le
            _ ≤ A := hscale
            _ ≤ 2 * A := by linarith only [hA]
        obtain ⟨f, hf, hruled, hfcard⟩ :=
          hpopular p K Rs (2 * A) hRne (hRcard.trans hn) hRscale hRpop
        refine ⟨f, hf, hruled, doublyRuled_degree_le_two htwo f hf hruled, ?_⟩
        have hfilter : (Rs.filter (LineOn f)).card ≤ (Ls.filter (LineOn f)).card :=
          Finset.card_le_card (Finset.filter_subset_filter (LineOn f) hRs)
        have hcardR : ((Rs.filter (LineOn f)).card : ℝ) ≤ (Ls.filter (LineOn f)).card := by
          exact_mod_cast hfilter
        linarith only [hfcard, hcardR]
  · have hempty : Ls = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst Ls
    left
    simp only [richPoints, Finset.filter_empty, Finset.card_empty,
      Nat.reduceLeDiff, Set.ofPred_false, Set.ncard_empty, Nat.cast_zero, mul_zero, le_refl]

end ExplicitRIP.GuthZahl

end
