/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Defs

/-!
# Normalized affine lines and their intersections

Coordinate proofs of injectivity, coplanarity, line and plane intersection
bounds, and the exact polynomial restriction of a split quadric.
-/

public section

namespace ExplicitRIP.Zahl

open Polynomial

@[simp] theorem linePoint_apply_zero {K : Type*} [CommRing K]
    (l : ChartLine K) (x : K) : linePoint l x 0 = x := rfl

@[simp] theorem linePoint_apply_one {K : Type*} [CommRing K]
    (l : ChartLine K) (x : K) : linePoint l x 1 = l.s + l.u * x := rfl

@[simp] theorem linePoint_apply_two {K : Type*} [CommRing K]
    (l : ChartLine K) (x : K) : linePoint l x 2 = l.t + l.v * x := rfl

theorem linePoint_injective {K : Type*} [CommRing K] (l : ChartLine K) :
    Function.Injective (linePoint l) := by
  intro x y h
  exact congrFun h 0

theorem linePoint_mem_linePoints {K : Type*} [CommRing K]
    (l : ChartLine K) (x : K) : linePoint l x ∈ linePoints l :=
  Set.mem_range_self x

theorem mem_linePoints_iff {K : Type*} [CommRing K]
    (l : ChartLine K) (w : Point K) :
    w ∈ linePoints l ↔ w 1 = l.s + l.u * w 0 ∧ w 2 = l.t + l.v * w 0 := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    refine ⟨w 0, ?_⟩
    funext j
    fin_cases j
    · rfl
    · exact h1.symm
    · exact h2.symm

/-- Equality of the four coefficients determines a normalized chart line. -/
theorem ChartLine.ext_of_coefficients {K : Type*} {l m : ChartLine K}
    (hs : l.s = m.s) (ht : l.t = m.t) (hu : l.u = m.u) (hv : l.v = m.v) : l = m := by
  cases l
  cases m
  cases hs
  cases ht
  cases hu
  cases hv
  rfl

private theorem affine_coeff_eq_of_eval_eq {K : Type*} [Field K]
    {s t u v x y : K} (hxy : x ≠ y)
    (hx : s + u * x = t + v * x) (hy : s + u * y = t + v * y) :
    s = t ∧ u = v := by
  have hprod : (u - v) * (x - y) = 0 := by
    linear_combination hx - hy
  have huv : u = v :=
    sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hxy))
  refine ⟨?_, huv⟩
  rw [huv] at hx
  exact add_right_cancel hx

/-- The normalized coefficients are determined by the affine point set. -/
theorem linePoints_injective {K : Type*} [Field K] :
    Function.Injective (linePoints : ChartLine K → Set (Point K)) := by
  intro l m h
  have h0 := (mem_linePoints_iff m (linePoint l 0)).mp
    (h ▸ linePoint_mem_linePoints l 0)
  have h1 := (mem_linePoints_iff m (linePoint l 1)).mp
    (h ▸ linePoint_mem_linePoints l 1)
  simp only [linePoint_apply_zero, linePoint_apply_one, linePoint_apply_two] at h0 h1
  obtain ⟨hs, hu⟩ := affine_coeff_eq_of_eval_eq zero_ne_one h0.1 h1.1
  obtain ⟨ht, hv⟩ := affine_coeff_eq_of_eval_eq zero_ne_one h0.2 h1.2
  cases l
  cases m
  congr 1

/-- The literal determinant means affine intersection or parallelism. -/
theorem coplanar_iff_intersects_or_parallel {K : Type*} [Field K]
    (l m : ChartLine K) :
    Coplanar l m ↔ Intersects l m ∨ Parallel l m := by
  constructor
  · intro h
    by_cases hu : l.u = m.u
    · by_cases hv : l.v = m.v
      · exact Or.inr ⟨hu, hv⟩
      · have hs : l.s = m.s := by
          have hz : (l.s - m.s) * (l.v - m.v) = 0 := by
            simpa only [Coplanar, hu, sub_self, mul_zero, sub_zero] using h
          exact sub_eq_zero.mp
            ((mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hv))
        left
        refine ⟨linePoint l ((m.t - l.t) / (l.v - m.v)),
          linePoint_mem_linePoints l _, ?_⟩
        apply (mem_linePoints_iff m _).mpr
        simp only [linePoint_apply_zero, linePoint_apply_one, linePoint_apply_two]
        constructor
        · rw [hs, hu]
        · field_simp [sub_ne_zero.mpr hv]
          ring
    · left
      refine ⟨linePoint l ((m.s - l.s) / (l.u - m.u)),
        linePoint_mem_linePoints l _, ?_⟩
      apply (mem_linePoints_iff m _).mpr
      simp only [linePoint_apply_zero, linePoint_apply_one, linePoint_apply_two]
      constructor
      · field_simp [sub_ne_zero.mpr hu]
        ring
      · dsimp [Coplanar] at h
        field_simp [sub_ne_zero.mpr hu]
        linear_combination -h
  · rintro (⟨w, hl, hm⟩ | ⟨hu, hv⟩)
    · obtain ⟨hls, hlt⟩ := (mem_linePoints_iff l w).mp hl
      obtain ⟨hms, hmt⟩ := (mem_linePoints_iff m w).mp hm
      dsimp [Coplanar]
      linear_combination (l.v - m.v) * (hms - hls) -
        (l.u - m.u) * (hmt - hlt)
    · simp only [Coplanar, hu, hv, sub_self, mul_zero]

theorem plane_form_linePoint {K : Type*} [Field K]
    (normal : Point K) (l : ChartLine K) (x : K) :
    (∑ j : Fin 3, normal j * linePoint l x j) =
      normal 1 * l.s + normal 2 * l.t +
        (normal 0 + normal 1 * l.u + normal 2 * l.v) * x := by
  simp only [Fin.sum_univ_three, linePoint_apply_zero, linePoint_apply_one,
    linePoint_apply_two]
  ring

theorem planeContains_iff {K : Type*} [Field K]
    (normal : Point K) (offset : K) (l : ChartLine K) :
    planeContains normal offset l ↔
      normal 1 * l.s + normal 2 * l.t = offset ∧
        normal 0 + normal 1 * l.u + normal 2 * l.v = 0 := by
  constructor
  · intro h
    have h0 := h (linePoint l 0) (linePoint_mem_linePoints l 0)
    have h1 := h (linePoint l 1) (linePoint_mem_linePoints l 1)
    rw [plane_form_linePoint] at h0 h1
    simp only [mul_zero, add_zero] at h0
    simp only [mul_one] at h1
    refine ⟨h0, ?_⟩
    linear_combination h1 - h0
  · rintro ⟨h0, h1⟩ w ⟨x, rfl⟩
    rw [plane_form_linePoint, h0, h1, zero_mul, add_zero]

/-- Two lines contained in one genuine affine plane are coplanar. -/
theorem coplanar_of_planeContains {K : Type*} [Field K]
    (normal : Point K) (hnormal : normal ≠ 0) (offset : K)
    (l m : ChartLine K) (hl : planeContains normal offset l)
    (hm : planeContains normal offset m) : Coplanar l m := by
  obtain ⟨hl0, hl1⟩ := (planeContains_iff normal offset l).mp hl
  obtain ⟨hm0, hm1⟩ := (planeContains_iff normal offset m).mp hm
  have hb : normal 1 * (l.s - m.s) + normal 2 * (l.t - m.t) = 0 := by
    linear_combination hl0 - hm0
  have hd : normal 1 * (l.u - m.u) + normal 2 * (l.v - m.v) = 0 := by
    linear_combination hl1 - hm1
  dsimp [Coplanar]
  by_contra hdet
  have hn1 : normal 1 *
      ((l.s - m.s) * (l.v - m.v) - (l.t - m.t) * (l.u - m.u)) = 0 := by
    linear_combination (l.v - m.v) * hb - (l.t - m.t) * hd
  have hn2 : normal 2 *
      ((l.s - m.s) * (l.v - m.v) - (l.t - m.t) * (l.u - m.u)) = 0 := by
    linear_combination (l.s - m.s) * hd - (l.u - m.u) * hb
  have h1 : normal 1 = 0 := (mul_eq_zero.mp hn1).resolve_right hdet
  have h2 : normal 2 = 0 := (mul_eq_zero.mp hn2).resolve_right hdet
  have h0 : normal 0 = 0 := by
    simpa only [h1, h2, zero_mul, add_zero] using hl1
  apply hnormal
  funext j
  fin_cases j
  · exact h0
  · exact h1
  · exact h2

/-- Two distinct chart lines meet in at most one point. -/
theorem linePoints_inter_subsingleton {K : Type*} [Field K]
    {l m : ChartLine K} (hlm : l ≠ m) : (linePoints l ∩ linePoints m).Subsingleton := by
  intro w hw z hz
  obtain ⟨hwl1, hwl2⟩ := (mem_linePoints_iff l w).mp hw.1
  obtain ⟨hwm1, hwm2⟩ := (mem_linePoints_iff m w).mp hw.2
  obtain ⟨hzl1, hzl2⟩ := (mem_linePoints_iff l z).mp hz.1
  obtain ⟨hzm1, hzm2⟩ := (mem_linePoints_iff m z).mp hz.2
  by_cases hcoord : w 0 = z 0
  · funext j
    fin_cases j
    · exact hcoord
    · change w 1 = z 1
      rw [hwl1, hzl1, hcoord]
    · change w 2 = z 2
      rw [hwl2, hzl2, hcoord]
  · obtain ⟨hs, hu⟩ := affine_coeff_eq_of_eval_eq hcoord
      (hwl1.symm.trans hwm1) (hzl1.symm.trans hzm1)
    obtain ⟨ht, hv⟩ := affine_coeff_eq_of_eval_eq hcoord
      (hwl2.symm.trans hwm2) (hzl2.symm.trans hzm2)
    exfalso
    apply hlm
    cases l
    cases m
    congr 1

/-- Two distinct normalized affine lines have at most one common point. -/
theorem line_intersection_ncard_le_one {K : Type*} [Field K]
    (l m : ChartLine K) (hlm : l ≠ m) :
    (linePoints l ∩ linePoints m).Finite ∧
      (linePoints l ∩ linePoints m).ncard ≤ 1 := by
  have hsub := linePoints_inter_subsingleton hlm
  exact ⟨hsub.finite,
    (Set.ncard_le_one hsub.finite).mpr (fun _ hw _ hz => hsub hw hz)⟩

-- Noncontainment suffices for the bound; the statement assumes a nonzero plane normal.
set_option linter.unusedVariables false in
/-- A line outside a plane meets it in at most one point. -/
theorem plane_intersection_ncard_le_one {K : Type*} [Field K]
    (normal : Point K) (hnormal : normal ≠ 0) (offset : K)
    (l : ChartLine K) (hl : ¬ planeContains normal offset l) :
    (linePoints l ∩ {w | (∑ j : Fin 3, normal j * w j) = offset}).Finite ∧
      (linePoints l ∩ {w | (∑ j : Fin 3, normal j * w j) = offset}).ncard ≤ 1 := by
  have hsub : (linePoints l ∩
      {w | (∑ j : Fin 3, normal j * w j) = offset}).Subsingleton := by
    rintro w ⟨⟨x, rfl⟩, hx⟩ z ⟨⟨y, rfl⟩, hy⟩
    by_cases hxy : x = y
    · rw [hxy]
    · exfalso
      apply hl
      apply (planeContains_iff normal offset l).mpr
      rw [Set.mem_ofPred_eq, plane_form_linePoint] at hx hy
      have hx' : normal 1 * l.s + normal 2 * l.t +
          (normal 0 + normal 1 * l.u + normal 2 * l.v) * x = offset + 0 * x := by
        simpa only [zero_mul, add_zero] using hx
      have hy' : normal 1 * l.s + normal 2 * l.t +
          (normal 0 + normal 1 * l.u + normal 2 * l.v) * y = offset + 0 * y := by
        simpa only [zero_mul, add_zero] using hy
      exact affine_coeff_eq_of_eval_eq hxy hx' hy'
  exact ⟨hsub.finite,
    (Set.ncard_le_one hsub.finite).mpr (fun _ hw _ hz => hsub hw hz)⟩

/-- Restriction has degree at most two and evaluates to the quadric value. -/
theorem quadricRestriction_spec {K : Type*} [Field K]
    (Q : SplitQuadric K) (l : ChartLine K) :
    (quadricRestriction Q l).natDegree ≤ 2 ∧
      ∀ x : K, (quadricRestriction Q l).eval x = quadricValue Q (linePoint l x) := by
  let a := Q ![1, 0, l.s, l.t]
  let b := Q ![0, 1, l.u, l.v]
  let f := fun j : Fin 4 => C (a j) + C (b j) * X
  have hf (j : Fin 4) : (f j).natDegree ≤ 1 := by
    apply natDegree_add_le_of_degree_le
    · simp only [natDegree_C, Nat.zero_le]
    · exact (natDegree_mul_le (p := C (b j)) (q := X)).trans (by
        simp only [natDegree_C, natDegree_X, zero_add, le_refl])
  constructor
  · change (f 0 * f 3 - f 1 * f 2).natDegree ≤ 2
    exact (natDegree_sub_le _ _).trans (max_le
      (natDegree_mul_le_of_le (hf 0) (hf 3))
      (natDegree_mul_le_of_le (hf 1) (hf 2)))
  · intro x
    have hvec : homogenize (linePoint l x) =
        ![1, 0, l.s, l.t] + x • ![0, 1, l.u, l.v] := by
      funext j
      fin_cases j <;> simp [homogenize, linePoint, mul_comm]
    have hQ : Q (homogenize (linePoint l x)) = a + x • b := by
      rw [hvec, map_add, map_smul]
    simp only [quadricRestriction, quadricValue, eval_sub, eval_mul, eval_add,
      eval_C, eval_X, hQ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, a, b]
    ring

end ExplicitRIP.Zahl
