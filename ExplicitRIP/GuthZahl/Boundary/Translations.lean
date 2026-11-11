/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Boundary.Defs
public import ExplicitRIP.GuthZahl.Basic.Restriction

/-!
# Boundary translations for chart lines

The normalized chart parametrization identifies the corresponding carriers and finite
incidence counts. Containment, ruling predicates, and plane forms are translated over their
exact field hypotheses. Coefficient extension preserves rich points of richness at least two
and commutes with algebraic polynomial restriction.
-/

public section

namespace ExplicitRIP.GuthZahl
open ExplicitRIP.Zahl (ChartLine)

open Classical in
private theorem chart_parameter {K : Type*} [Field K] (l : ChartLine K) (t : K) :
    chartOrigin l + t • chartDirection l = Zahl.linePoint l t := by
  ext j
  fin_cases j <;> simp [chartOrigin, chartDirection, Zahl.linePoint, mul_comm]

open Classical in
private theorem chartDirection_ne_zero {K : Type*} [Field K] (l : ChartLine K) :
    chartDirection l ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [chartDirection] at this

open Classical in
/-- Same-field carrier translations, valid over every field. -/
theorem chartLift_points {K : Type*} [Field K] (l : ChartLine K) :
    ((chartLift l).1 : Set (Point K)) = Zahl.linePoints l := by
  ext x
  change x ∈ AffineSubspace.mk' (chartOrigin l) (Submodule.span K {chartDirection l}) ↔
    ∃ t, Zahl.linePoint l t = x
  rw [AffineSubspace.mem_mk', Submodule.mem_span_singleton]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [← chart_parameter, ht]
    change chartOrigin l + (x - chartOrigin l) = x
    abel
  · rintro ⟨t, rfl⟩
    refine ⟨t, ?_⟩
    rw [← chart_parameter]
    change t • chartDirection l = chartOrigin l + t • chartDirection l - chartOrigin l
    abel

open Classical in
private theorem chart_mem_iff {K : Type*} [Field K] (l : ChartLine K) (x : Point K) :
    x ∈ Zahl.linePoints l ↔ x 1 = l.s + l.u * x 0 ∧ x 2 = l.t + l.v * x 0 := by
  constructor
  · rintro ⟨t, rfl⟩
    simp [Zahl.linePoint]
  · intro hx
    refine ⟨x 0, ?_⟩
    ext j
    fin_cases j <;> simp [Zahl.linePoint, hx.1, hx.2]

open Classical in
theorem chartLift_injective {K : Type*} [Field K] :
    Function.Injective (chartLift : ChartLine K → Line K) := by
  intro l m h
  have hs : Zahl.linePoints l = Zahl.linePoints m := by
    rw [← chartLift_points, ← chartLift_points, h]
  have h0 : l.s = m.s ∧ l.t = m.t := by
    simpa [Zahl.linePoint] using (chart_mem_iff m (Zahl.linePoint l 0)).mp
      (hs ▸ (Set.mem_range_self 0))
  have h1 : l.s + l.u = m.s + m.u ∧ l.t + l.v = m.t + m.v := by
    simpa [Zahl.linePoint] using (chart_mem_iff m (Zahl.linePoint l 1)).mp
      (hs ▸ (Set.mem_range_self 1))
  obtain ⟨hS, hT⟩ := h0
  have hU : l.u = m.u := add_left_cancel (hS ▸ h1.1)
  have hV : l.v = m.v := add_left_cancel (hT ▸ h1.2)
  cases l
  cases m
  simp_all

open Classical in
theorem chartFamily_card {K : Type*} [Field K] (L : Finset (ChartLine K)) :
    (chartFamily L).card = L.card :=
  Finset.card_image_of_injective L chartLift_injective

open Classical in
theorem chartFamily_richPoints {K : Type*} [Field K]
    (L : Finset (ChartLine K)) (r : ℕ) :
    richPoints (chartFamily L) r = Zahl.richPoints L r := by
  ext x
  change r ≤ ((L.image chartLift).filter (fun l => x ∈ l.1)).card ↔ _
  rw [Finset.filter_image]
  simp only [← SetLike.mem_coe, chartLift_points]
  rw [Finset.card_image_of_injective _ chartLift_injective]
  rfl

open Classical in
theorem chartFamily_richCount {K : Type*} [Field K]
    (L : Finset (ChartLine K)) (r : ℕ) :
    (richPoints (chartFamily L) r).ncard = Zahl.richCount L r := by
  rw [chartFamily_richPoints]
  rfl

open Classical in
/-- The algebraic identity holds without an infinite-field assumption. -/
theorem chartLift_LineOn_iff_restriction {K : Type*} [Field K]
    (f : Poly K) (l : ChartLine K) :
    LineOn f (chartLift l) ↔ chartRestriction f l = 0 := by
  apply lineOn_iff_restrictLine_eq_zero
  · exact AffineSubspace.self_mem_mk' _ _
  · change chartDirection l ∈ (AffineSubspace.mk' _ _).direction
    rw [AffineSubspace.direction_mk']
    exact Submodule.subset_span (Set.mem_singleton _)
  · exact chartDirection_ne_zero l

open Classical in
/-- Pointwise containment may be used here because K is infinite. -/
theorem chartLift_LineOn_iff_hypersurfaceContains {K : Type*} [Field K] [Infinite K]
    (f : Poly K) (l : ChartLine K) :
    LineOn f (chartLift l) ↔ Zahl.hypersurfaceContains f l := by
  rw [chartLift_LineOn_iff_restriction]
  constructor
  · intro h x hx
    obtain ⟨t, rfl⟩ := hx
    have he := eval_restrictLine f (chartOrigin l) (chartDirection l) t
    rw [chart_parameter] at he
    change MvPolynomial.eval (Zahl.linePoint l t) f = 0
    rw [← he, ← chartRestriction, h, Polynomial.eval_zero]
  · intro h
    apply Polynomial.funext
    intro t
    rw [Polynomial.eval_zero]
    change Polynomial.eval t (restrictLine f (chartOrigin l) (chartDirection l)) = 0
    rw [eval_restrictLine, chart_parameter]
    exact h _ (Set.mem_range_self t)

open Classical in
theorem chartFamily_filter_card {K : Type*} [Field K] [Infinite K]
    (f : Poly K) (L : Finset (ChartLine K)) :
    ((chartFamily L).filter (LineOn f)).card =
      (L.filter (Zahl.hypersurfaceContains f)).card := by
  change ((L.image chartLift).filter (LineOn f)).card = _
  rw [Finset.filter_image, Finset.card_image_of_injective _ chartLift_injective]
  congr 1
  ext l
  simp only [Finset.mem_filter, chartLift_LineOn_iff_hypersurfaceContains]

open Classical in
/-- All directions are allowed in both ruling predicates; the counted lines are chart lines, but
the ruling witnesses need not lie in that chart. -/
theorem doublyRuled_iff_zahl {K : Type*} [Field K] [Infinite K] (f : Poly K) :
    DoublyRuled f ↔ Zahl.doublyRuledHypersurface f := by
  constructor
  · rintro ⟨g, _hfg, hne, hlines⟩
    refine ⟨g, hne, ?_⟩
    intro x hfx hgx
    obtain ⟨L, M, hLM, hxL, hxM, hfL, hfM⟩ := hlines x ⟨hfx, hgx⟩
    obtain ⟨_a, _ha, v, hv, hv0⟩ := line_exists_base_direction L
    obtain ⟨_b, _hb, w, hw, hw0⟩ := line_exists_base_direction M
    refine ⟨v, w, hv0, hw0, ?_, ?_⟩
    · rintro ⟨c, hc⟩
      have hwL : w ∈ L.1.direction := by
        rw [hc]
        exact L.1.direction.smul_mem c hv
      have hdL := eq_span_singleton_of_mem_of_finrank_eq_one L.2 hwL hw0
      have hdM := eq_span_singleton_of_mem_of_finrank_eq_one M.2 hw hw0
      exact hLM (Subtype.ext (AffineSubspace.ext_of_direction_eq
        (hdL.trans hdM.symm) ⟨x, hxL, hxM⟩))
    · intro t
      constructor
      · apply (lineOn_iff_eval_eq_zero f L).mp hfL
        simpa only [vadd_eq_add, add_comm] using
          AffineSubspace.vadd_mem_of_mem_direction (L.1.direction.smul_mem t hv) hxL
      · apply (lineOn_iff_eval_eq_zero f M).mp hfM
        simpa only [vadd_eq_add, add_comm] using
          AffineSubspace.vadd_mem_of_mem_direction (M.1.direction.smul_mem t hw) hxM
  · rintro ⟨g, hne, hdirs⟩
    have hfg : ¬ f ∣ g := by
      rintro ⟨q, rfl⟩
      obtain ⟨x, hx, hnx⟩ := hne
      exact hnx (by change MvPolynomial.eval x (f * q) = 0; rw [map_mul, hx, zero_mul])
    refine ⟨g, hfg, hne, ?_⟩
    intro x hx
    obtain ⟨v, w, hv0, hw0, hnprop, hvan⟩ := hdirs x hx.1 hx.2
    let L : Line K := ⟨AffineSubspace.mk' x (Submodule.span K {v}), by
      rw [AffineSubspace.direction_mk']; exact finrank_span_singleton hv0⟩
    let M : Line K := ⟨AffineSubspace.mk' x (Submodule.span K {w}), by
      rw [AffineSubspace.direction_mk']; exact finrank_span_singleton hw0⟩
    have hxL : x ∈ L.1 := AffineSubspace.self_mem_mk' _ _
    have hxM : x ∈ M.1 := AffineSubspace.self_mem_mk' _ _
    have hvL : v ∈ L.1.direction := by
      change v ∈ (AffineSubspace.mk' x _).direction
      rw [AffineSubspace.direction_mk']
      exact Submodule.subset_span (Set.mem_singleton _)
    have hwM : w ∈ M.1.direction := by
      change w ∈ (AffineSubspace.mk' x _).direction
      rw [AffineSubspace.direction_mk']
      exact Submodule.subset_span (Set.mem_singleton _)
    refine ⟨L, M, ?_, hxL, hxM, ?_, ?_⟩
    · intro hLM
      have hwL : w ∈ L.1.direction := by
        rw [hLM]
        exact hwM
      change w ∈ (AffineSubspace.mk' x (Submodule.span K {v})).direction at hwL
      rw [AffineSubspace.direction_mk', Submodule.mem_span_singleton] at hwL
      obtain ⟨c, hc⟩ := hwL
      exact hnprop ⟨c, hc.symm⟩
    · apply (lineOn_iff_restrictLine_eq_zero f L x hxL v hvL hv0).mpr
      apply Polynomial.funext
      intro t
      rw [Polynomial.eval_zero, eval_restrictLine]
      exact (hvan t).1
    · apply (lineOn_iff_restrictLine_eq_zero f M x hxM w hwM hw0).mpr
      apply Polynomial.funext
      intro t
      rw [Polynomial.eval_zero, eval_restrictLine]
      exact (hvan t).2

open Classical in
private theorem eval_planePolynomial {K : Type*} [Field K]
    (normal : Point K) (offset : K) (x : Point K) :
    MvPolynomial.eval x (planePolynomial normal offset) =
      (∑ j : Fin 3, normal j * x j) - offset := by
  simp only [planePolynomial, map_sub, map_sum, map_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X]

open Classical in
private theorem chartRestriction_planePolynomial {K : Type*} [Field K]
    (normal : Point K) (offset : K) (l : ChartLine K) :
    chartRestriction (planePolynomial normal offset) l =
      Polynomial.C (normal 1 * l.s + normal 2 * l.t - offset) +
        Polynomial.C (normal 0 + normal 1 * l.u + normal 2 * l.v) * Polynomial.X := by
  simp [chartRestriction, restrictLine, planePolynomial, chartOrigin, chartDirection,
    Fin.sum_univ_succ]
  ring

open Classical in
/-- The chart plane-containment predicate agrees with algebraic containment in the corresponding
linear hypersurface. -/
theorem planeContains_iff_LineOn {K : Type*} [Field K]
    (normal : Point K) (offset : K) (l : ChartLine K) :
    Zahl.planeContains normal offset l ↔ LineOn (planePolynomial normal offset) (chartLift l) := by
  constructor
  · intro h
    have h0 : normal 1 * l.s + normal 2 * l.t = offset := by
      simpa [Zahl.linePoint, Fin.sum_univ_succ] using h _ (Set.mem_range_self 0)
    have h1 : normal 0 + (normal 1 * (l.s + l.u) + normal 2 * (l.t + l.v)) = offset := by
      simpa [Zahl.linePoint, Fin.sum_univ_succ] using h _ (Set.mem_range_self 1)
    have hA : normal 1 * l.s + normal 2 * l.t - offset = 0 := by
      linear_combination h0
    have hB : normal 0 + normal 1 * l.u + normal 2 * l.v = 0 := by
      linear_combination h1 - h0
    rw [chartLift_LineOn_iff_restriction, chartRestriction_planePolynomial, hA, hB]
    simp only [Polynomial.C_0, zero_mul, add_zero]
  · intro h x hx
    obtain ⟨t, rfl⟩ := hx
    have he := congrArg (Polynomial.eval t)
      ((chartLift_LineOn_iff_restriction _ _).mp h)
    change Polynomial.eval t (restrictLine (planePolynomial normal offset)
      (chartOrigin l) (chartDirection l)) = _ at he
    rw [eval_restrictLine, chart_parameter, eval_planePolynomial, Polynomial.eval_zero] at he
    exact sub_eq_zero.mp he

open Classical in
private theorem polynomial_affine_form {K : Type*} [Field K]
    (f : Poly K) (hd : f.totalDegree ≤ 1) :
    f = MvPolynomial.C (f.coeff 0) +
      ∑ j : Fin 3, MvPolynomial.C (f.coeff (Finsupp.single j 1)) * MvPolynomial.X j := by
  classical
  ext m
  by_cases hm0 : m = 0
  · subst m
    simp [MvPolynomial.coeff_C, MvPolynomial.coeff_X]
  · have hmpos : 0 < m.sum (fun _ n => n) := by
      exact Finset.sum_pos (fun i hi => Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi))
        (Finsupp.support_nonempty_iff.mpr hm0)
    by_cases hm1 : m.sum (fun _ n => n) = 1
    · obtain ⟨j, rfl⟩ := (Finsupp.sum_eq_one_iff m).mp hm1
      simp [MvPolynomial.coeff_C, MvPolynomial.coeff_X,
        Finsupp.single_eq_single_iff, Ne.symm hm0]
    · have hcoeff : f.coeff m = 0 := by
        apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
        change f.totalDegree < m.sum (fun _ n => n)
        omega
      have hne (j : Fin 3) : Finsupp.single j 1 ≠ m := by
        intro h
        subst m
        simp at hm1
      simp [MvPolynomial.coeff_C, MvPolynomial.coeff_X, Ne.symm hm0, hne, hcoeff]

open Classical in
theorem degree_one_plane_form {K : Type*} [Field K]
    (f : Poly K) (hd : f.totalDegree = 1) :
    ∃ normal : Point K, normal ≠ 0 ∧ ∃ offset : K, f = planePolynomial normal offset := by
  let normal : Point K := fun j => f.coeff (Finsupp.single j 1)
  have hform := polynomial_affine_form f hd.le
  have hn : normal ≠ 0 := by
    intro h
    have hz (j : Fin 3) : f.coeff (Finsupp.single j 1) = 0 := congrFun h j
    simp only [hz, MvPolynomial.C_0, zero_mul, Finset.sum_const_zero, add_zero] at hform
    have hdeg := congrArg MvPolynomial.totalDegree hform
    rw [hd, MvPolynomial.totalDegree_C] at hdeg
    exact Nat.one_ne_zero hdeg
  refine ⟨normal, hn, -f.coeff 0, ?_⟩
  rw [planePolynomial]
  simpa only [normal, map_neg, sub_neg_eq_add, add_comm] using hform

open Classical in
private theorem mapChart_injective {F K : Type*} [Field F] [Field K] (φ : F →+* K) :
    Function.Injective (mapChart φ) := by
  rintro ⟨s, t, u, v⟩ ⟨s', t', u', v'⟩ h
  simpa only [mapChart, ChartLine.mk.injEq, φ.injective.eq_iff] using h

open Classical in
private theorem mapPoint_injective {F K : Type*} [Field F] [Field K] (φ : F →+* K) :
    Function.Injective (mapPoint φ) := by
  intro x y h
  ext j
  exact φ.injective (congrFun h j)

open Classical in
/-- Extend coefficients, never the finite rational point set. -/
theorem mapChartFamily_card {F K : Type*} [Field F] [Field K]
    (φ : F →+* K) (L : Finset (ChartLine F)) : (mapChartFamily φ L).card = L.card :=
  Finset.card_image_of_injective L (mapChart_injective φ)

open Classical in
private theorem mapPoint_mem_linePoints_iff {F K : Type*} [Field F] [Field K]
    (φ : F →+* K) (l : ChartLine F) (x : Point F) :
    mapPoint φ x ∈ Zahl.linePoints (mapChart φ l) ↔ x ∈ Zahl.linePoints l := by
  rw [chart_mem_iff, chart_mem_iff]
  simp only [mapPoint, mapChart, ← map_mul, ← map_add, φ.injective.eq_iff]

open Classical in
private theorem mapChartFamily_incidence_card {F K : Type*} [Field F] [Field K]
    (φ : F →+* K) (L : Finset (ChartLine F)) (x : Point F) :
    ((mapChartFamily φ L).filter (fun l => mapPoint φ x ∈ Zahl.linePoints l)).card =
      (L.filter (fun l => x ∈ Zahl.linePoints l)).card := by
  change ((L.image (mapChart φ)).filter _).card = _
  rw [Finset.filter_image, Finset.card_image_of_injective _ (mapChart_injective φ)]
  congr 1
  ext l
  simp only [Finset.mem_filter, mapPoint_mem_linePoints_iff]

open Classical in
private theorem chart_intersection_descends {F K : Type*} [Field F] [Field K]
    (φ : F →+* K) (l m : ChartLine F) (hlm : l ≠ m) (x : Point K)
    (hl : x ∈ Zahl.linePoints (mapChart φ l))
    (hm : x ∈ Zahl.linePoints (mapChart φ m)) :
    ∃ y : Point F, mapPoint φ y = x := by
  obtain ⟨hl1, hl2⟩ := (chart_mem_iff _ _).mp hl
  obtain ⟨hm1, hm2⟩ := (chart_mem_iff _ _).mp hm
  change x 1 = φ l.s + φ l.u * x 0 at hl1
  change x 2 = φ l.t + φ l.v * x 0 at hl2
  change x 1 = φ m.s + φ m.u * x 0 at hm1
  change x 2 = φ m.t + φ m.v * x 0 at hm2
  have hpre : ∃ a : F, φ a = x 0 := by
    by_cases hu : l.u = m.u
    · have hs : l.s = m.s := by
        apply φ.injective
        exact add_right_cancel (by simpa only [hu] using hl1.symm.trans hm1)
      have hv : l.v ≠ m.v := by
        intro hv
        have ht : l.t = m.t := by
          apply φ.injective
          exact add_right_cancel (by simpa only [hv] using hl2.symm.trans hm2)
        exact hlm (by cases l; cases m; simp_all)
      refine ⟨(m.t - l.t) / (l.v - m.v), ?_⟩
      rw [map_div₀, map_sub, map_sub]
      apply (div_eq_iff (sub_ne_zero.mpr (fun h => hv (φ.injective h)))).mpr
      linear_combination hl2 - hm2
    · refine ⟨(m.s - l.s) / (l.u - m.u), ?_⟩
      rw [map_div₀, map_sub, map_sub]
      apply (div_eq_iff (sub_ne_zero.mpr (fun h => hu (φ.injective h)))).mpr
      linear_combination hl1 - hm1
  obtain ⟨a, ha⟩ := hpre
  refine ⟨Zahl.linePoint l a, ?_⟩
  ext j
  fin_cases j
  · simpa [mapPoint, Zahl.linePoint] using ha
  · simpa [mapPoint, Zahl.linePoint, map_add, map_mul, ha] using hl1.symm
  · simpa [mapPoint, Zahl.linePoint, map_add, map_mul, ha] using hl2.symm

open Classical in
/-- A point on two distinct base-defined lines is already base-defined. -/
theorem mapChartFamily_richPoints {F K : Type*} [Field F] [Field K]
    (φ : F →+* K) (L : Finset (ChartLine F)) (r : ℕ) (hr : 2 ≤ r) :
    Zahl.richPoints (mapChartFamily φ L) r = mapPoint φ '' Zahl.richPoints L r := by
  ext x
  constructor
  · intro hx
    obtain ⟨l', hl', m', hm', hlm'⟩ := Finset.one_lt_card.mp
      (lt_of_lt_of_le (by decide : 1 < 2) (hr.trans hx))
    obtain ⟨hl'L, hxl⟩ := Finset.mem_filter.mp hl'
    obtain ⟨hm'L, hxm⟩ := Finset.mem_filter.mp hm'
    obtain ⟨l, hlL, rfl⟩ := Finset.mem_image.mp hl'L
    obtain ⟨m, hmL, rfl⟩ := Finset.mem_image.mp hm'L
    have hlm : l ≠ m := fun h => hlm' (congrArg (mapChart φ) h)
    obtain ⟨y, rfl⟩ := chart_intersection_descends φ l m hlm x hxl hxm
    refine ⟨y, ?_, rfl⟩
    change r ≤ (L.filter (fun l => y ∈ Zahl.linePoints l)).card
    rw [← mapChartFamily_incidence_card φ]
    exact hx
  · rintro ⟨y, hy, rfl⟩
    change r ≤ ((mapChartFamily φ L).filter
      (fun l => mapPoint φ y ∈ Zahl.linePoints l)).card
    rw [mapChartFamily_incidence_card]
    exact hy

open Classical in
theorem mapChartFamily_richCount {F K : Type*} [Field F] [Field K]
    (φ : F →+* K) (L : Finset (ChartLine F)) (r : ℕ) (hr : 2 ≤ r) :
    Zahl.richCount (mapChartFamily φ L) r = Zahl.richCount L r := by
  unfold Zahl.richCount
  rw [mapChartFamily_richPoints φ L r hr]
  exact Set.ncard_image_of_injective _ (mapPoint_injective φ)

open Classical in
/-- Algebraic containment commutes with injective scalar extension, even when the original field
is finite and deg f is large. -/
theorem chartRestriction_map {F K : Type*} [Field F] [Field K]
    (φ : F →+* K) (f : Poly F) (l : ChartLine F) :
    chartRestriction (MvPolynomial.map φ f) (mapChart φ l) =
      Polynomial.map φ (chartRestriction f l) := by
  unfold chartRestriction restrictLine
  rw [MvPolynomial.eval₂Hom_map_hom, ← Polynomial.coe_mapRingHom, MvPolynomial.map_eval₂Hom]
  apply MvPolynomial.eval₂Hom_congr
  · ext c
    simp
  · funext j
    fin_cases j <;> simp [chartOrigin, chartDirection, mapChart]
  · rfl

end ExplicitRIP.GuthZahl
end
