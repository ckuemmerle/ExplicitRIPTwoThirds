/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Boundary.Descent.Grid
public import ExplicitRIP.GuthZahl.Boundary.Descent.Scalar
public import ExplicitRIP.GuthZahl.Boundary.Descent.Uniqueness

/-!
# Chart-line families in homogeneous coordinates

Pointwise containment in characteristic different from two gives homogeneous quadratic
containment. Five chart lines therefore supply three disjoint homogeneous
planes, and disjointness is preserved on descent to the base field.
-/

@[expose] public section

namespace ExplicitRIP.GuthZahl.Boundary.Descent

open ExplicitRIP.Zahl (ChartLine)

variable {K : Type*} [Field K]

/-- The homogeneous span associated with the boundary's affine parametrization. -/
def chartPlane (l : ChartLine K) : Submodule K (Fin 4 → K) :=
  LinearMap.range (homogeneousLineMap (chartOrigin l) (chartDirection l))

theorem homogeneousLineMap_chart (l : ChartLine K) (u : Fin 2 → K) :
    homogeneousLineMap (chartOrigin l) (chartDirection l) u =
      ![u 0, u 1, u 0 * l.s + u 1 * l.u, u 0 * l.t + u 1 * l.v] := by
  ext i
  fin_cases i
  · rfl
  · change u 0 * 0 + u 1 * 1 = u 1
    ring
  · rfl
  · rfl

theorem finrank_chartPlane (l : ChartLine K) : Module.finrank K (chartPlane l) = 2 := by
  apply finrank_range_homogeneousLineMap
  intro h
  have hh := congrFun h 0
  exact (one_ne_zero : (1 : K) ≠ 0) hh

theorem chartPlane_injective : Function.Injective (chartPlane (K := K)) := by
  intro l m h
  have h0 : homogeneousLineMap (chartOrigin l) (chartDirection l) ![1, 0] ∈ chartPlane m :=
    h ▸ ⟨![1, 0], rfl⟩
  have h1 : homogeneousLineMap (chartOrigin l) (chartDirection l) ![0, 1] ∈ chartPlane m :=
    h ▸ ⟨![0, 1], rfl⟩
  obtain ⟨a, ha⟩ := h0
  obtain ⟨b, hb⟩ := h1
  rw [homogeneousLineMap_chart, homogeneousLineMap_chart] at ha hb
  have ha0 : a 0 = 1 := congrFun ha 0
  have ha1 : a 1 = 0 := congrFun ha 1
  have hb0 : b 0 = 0 := congrFun hb 0
  have hb1 : b 1 = 1 := congrFun hb 1
  have hs := congrFun ha 2
  have ht := congrFun ha 3
  have hu := congrFun hb 2
  have hv := congrFun hb 3
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    ha0, ha1, hb0, hb1, one_mul, zero_mul,
    add_zero, zero_add] at hs ht hu hv
  cases l
  cases m
  simp_all only

theorem chartPlane_zero (h2 : (2 : K) ≠ 0) (Q : Zahl.SplitQuadric K) (l : ChartLine K)
    (hl : Zahl.quadricContains Q l) :
    ∀ v ∈ chartPlane l, determinantFour (Q v) = 0 := by
  let a := homogeneousLineMap (chartOrigin l) (chartDirection l) ![1, 0]
  let b := homogeneousLineMap (chartOrigin l) (chartDirection l) ![0, 1]
  have hparam (t : K) : Zahl.homogenize (Zahl.linePoint l t) = a + t • b := by
    dsimp only [a, b]
    rw [homogeneousLineMap_chart, homogeneousLineMap_chart]
    ext i
    fin_cases i <;> simp [Zahl.homogenize, Zahl.linePoint] <;> ring
  have hzero (t : K) : determinantFour (Q a + t • Q b) = 0 := by
    rw [← map_smul, ← map_add, ← hparam]
    exact hl (Zahl.linePoint l t) ⟨t, rfl⟩
  rintro v ⟨u, rfl⟩
  have heq : homogeneousLineMap (chartOrigin l) (chartDirection l) u =
      u 0 • a + u 1 • b := by
    dsimp only [a, b]
    rw [homogeneousLineMap_chart, homogeneousLineMap_chart, homogeneousLineMap_chart]
    ext i
    fin_cases i <;> simp
  rw [heq, map_add, map_smul, map_smul]
  exact determinantFour_span_eq_zero h2 (Q a) (Q b) hzero _ _

variable {F : Type*} [Field F]

theorem map_mem_chartPlane (φ : F →+* K) (l : ChartLine F) {v : Fin 4 → F}
    (hv : v ∈ chartPlane l) : (fun i => φ (v i)) ∈ chartPlane (mapChart φ l) := by
  obtain ⟨u, rfl⟩ := hv
  refine ⟨fun i => φ (u i), ?_⟩
  rw [homogeneousLineMap_chart]
  ext i
  fin_cases i <;> simp [homogeneousLineMap_chart, mapChart, map_add, map_mul]

/-- Three of five base lines on an extension-field split quadric are already skew over the base. -/
theorem exists_base_skew_triple (φ : F →+* K) (h2 : (2 : F) ≠ 0)
    (L : Finset (ChartLine F)) (hL : 5 ≤ L.card) (Q : Zahl.SplitQuadric K)
    (hQ : ∀ l ∈ L, Zahl.quadricContains Q (mapChart φ l)) :
    ∃ a ∈ L, ∃ b ∈ L, ∃ c ∈ L,
      Disjoint (chartPlane a) (chartPlane b) ∧
      Disjoint (chartPlane a) (chartPlane c) ∧ Disjoint (chartPlane b) (chartPlane c) := by
  classical
  have h2K : (2 : K) ≠ 0 := by
    intro h
    apply h2
    apply φ.injective
    simpa only [map_ofNat, map_zero] using h
  let U : L → Submodule K (Fin 4 → K) := fun l =>
    (chartPlane (mapChart φ l)).map Q.toLinearMap
  have hinj : Function.Injective U := by
    intro a b hab
    have hplane : chartPlane (mapChart φ a) = chartPlane (mapChart φ b) :=
      Submodule.map_injective_of_injective Q.injective hab
    have hchart := chartPlane_injective hplane
    apply Subtype.ext
    have hs := φ.injective (congrArg ChartLine.s hchart)
    have ht := φ.injective (congrArg ChartLine.t hchart)
    have hu := φ.injective (congrArg ChartLine.u hchart)
    have hv := φ.injective (congrArg ChartLine.v hchart)
    cases a with | mk a ha =>
      cases b with | mk b hb =>
        cases a
        cases b
        simp_all only
  have hdim (l : L) : Module.finrank K (U l) = 2 := by
    dsimp only [U]
    rw [Q.finrank_map_eq, finrank_chartPlane]
  have hzero (l : L) (v : Fin 4 → K) (hv : v ∈ U l) : determinantFour v = 0 := by
    obtain ⟨x, hx, rfl⟩ := hv
    exact chartPlane_zero h2K Q (mapChart φ l) (hQ l l.property) x hx
  obtain ⟨a, b, c, _, _, _, hab, hac, hbc⟩ :=
    exists_disjoint_triple U hinj (by simpa only [Fintype.card_coe] using hL) hdim hzero
  have hd (a b : L) (h : Disjoint (U a) (U b)) :
      Disjoint (chartPlane (a : ChartLine F)) (chartPlane (b : ChartLine F)) := by
    rw [Submodule.disjoint_def]
    intro v hva hvb
    have hz : Q (fun i => φ (v i)) = 0 := (Submodule.disjoint_def.mp h) _
      ⟨_, map_mem_chartPlane φ a hva, rfl⟩ ⟨_, map_mem_chartPlane φ b hvb, rfl⟩
    have hz' : (fun i => φ (v i)) = 0 := Q.injective (hz.trans Q.map_zero.symm)
    ext i
    exact φ.injective ((congrFun hz' i).trans (map_zero φ).symm)
  exact ⟨a, a.property, b, b.property, c, c.property, hd a b hab, hd a c hac, hd b c hbc⟩

end ExplicitRIP.GuthZahl.Boundary.Descent

end
