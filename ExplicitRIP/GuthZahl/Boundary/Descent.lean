/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Boundary.Defs
public import ExplicitRIP.GuthZahl.Boundary.Descent.Projective
public import ExplicitRIP.GuthZahl.Boundary.Descent.Polynomial
public import ExplicitRIP.GuthZahl.Boundary.Descent.Quadric
import ExplicitRIP.GuthZahl.RuledSurfaces.CrossingFamilies
import ExplicitRIP.GuthZahl.RuledSurfaces.Transversals

/-!
# Plane and split-quadric descent

Descent of the geometric alternatives in the line-only Guth–Zahl theorem.
-/

public section

namespace ExplicitRIP.GuthZahl
open ExplicitRIP.Zahl (ChartLine)

open Classical in
/-- An irreducible nonplanar doubly ruled surface of degree at most two has the zero locus of a
split quadric. -/
theorem doublyRuled_degree_two_normal_form {K : Type*} [Field K] [IsAlgClosed K]
    (h2 : (2 : K) ≠ 0) (f : Poly K) (hf : Irreducible f)
    (hr : DoublyRuled f) (_hd : f.totalDegree ≤ 2) (hn : f.totalDegree ≠ 1) :
    ∃ Q : Zahl.SplitQuadric K, ∀ x : Point K,
      MvPolynomial.eval x f = 0 ↔ Zahl.quadricValue Q x = 0 := by
  obtain ⟨A, B, C, hAB, hAC, hBC, hF⟩ :=
    RuledSurfaces.exists_skew_triple_with_infinite_transversals hf hr hn
  obtain ⟨Q, hQA, hQB, hQC⟩ :=
    Boundary.Descent.exists_splitQuadric_of_skew_triple A B C hAB hAC hBC
  let q := Boundary.Descent.determinantPolynomial Q
  have hq : q ≠ 0 := Boundary.Descent.determinantPolynomial_ne_zero h2 Q
  have hdegree : q.totalDegree ≤ 2 := Boundary.Descent.totalDegree_determinantPolynomial_le Q
  have hA : LineOn q A := (lineOn_iff_eval_eq_zero q A).mpr (by
    intro x hx
    exact (Boundary.Descent.eval_determinantPolynomial Q x).trans (hQA x hx))
  have hB : LineOn q B := (lineOn_iff_eval_eq_zero q B).mpr (by
    intro x hx
    exact (Boundary.Descent.eval_determinantPolynomial Q x).trans (hQB x hx))
  have hC : LineOn q C := (lineOn_iff_eval_eq_zero q C).mpr (by
    intro x hx
    exact (Boundary.Descent.eval_determinantPolynomial Q x).trans (hQC x hx))
  have hirq := RuledSurfaces.irreducible_of_three_skew_lines hq hdegree
    A B C hAB hAC hBC hA hB hC
  have hdiv : f ∣ q := RuledSurfaces.dvd_of_infinite_common_lines hf (hF.mono (by
    rintro L ⟨hL, hLA, hLB, hLC⟩
    exact ⟨hL, RuledSurfaces.lineOn_of_coplanar_skew_triple hdegree A B C hAB hAC hBC
      hA hB hC L hLA hLB hLC⟩))
  have hassoc := hf.associated_of_dvd hirq hdiv
  refine ⟨Q, fun x => ?_⟩
  rw [← Boundary.Descent.eval_determinantPolynomial Q x]
  change MvPolynomial.eval x f = 0 ↔ MvPolynomial.eval x q = 0
  constructor
  · intro hx
    obtain ⟨r, heq⟩ := hassoc.dvd
    rw [heq, map_mul, hx, zero_mul]
  · intro hx
    obtain ⟨r, heq⟩ := hassoc.symm.dvd
    rw [heq, map_mul, hx, zero_mul]

open Classical in
/-- A plane containing two distinct base lines descends to the base field. -/
theorem plane_family_descends {F K : Type*} [Field F] [Field K]
    (φ : F →+* K) (L : Finset (ChartLine F)) (_hL : 2 ≤ L.card)
    (normal : Point K) (hn : normal ≠ 0) (offset : K)
    (hplane : ∀ l ∈ L, Zahl.planeContains normal offset (mapChart φ l)) :
    ∃ n : Point F, n ≠ 0 ∧ ∃ b : F, ∀ l ∈ L, Zahl.planeContains n b l := by
  let : Algebra F K := φ.toAlgebra
  obtain ⟨j, hj⟩ : ∃ j, normal j ≠ 0 := by
    by_contra h
    push Not at h
    exact hn (funext h)
  obtain ⟨ψ, hψ⟩ := Module.Projective.exists_dual_ne_zero F hj
  refine ⟨fun i => ψ (normal i), ?_, ψ offset, ?_⟩
  · intro heq
    exact hψ (congrFun heq j)
  · intro l hl w hw
    obtain ⟨t, rfl⟩ := hw
    have heq := hplane l hl (Zahl.linePoint (mapChart φ l) (φ t)) ⟨φ t, rfl⟩
    have hp : Zahl.linePoint (mapChart φ l) (φ t) =
        fun j => φ (Zahl.linePoint l t j) := by
      ext i
      fin_cases i <;> simp [Zahl.linePoint, mapChart]
    rw [hp] at heq
    have hmul (a : K) (b : F) : ψ (a * φ b) = ψ a * b := by
      calc
        ψ (a * φ b) = ψ (b • a) := by
          congr 1
          exact mul_comm a (φ b)
        _ = b * ψ a := ψ.map_smul b a
        _ = ψ a * b := mul_comm _ _
    simpa only [map_sum, hmul] using congrArg ψ heq

open Classical in
/-- Five lines give three in one ruling; three skew base lines determine their split quadric over
F. Geometric splitness alone is insufficient. -/
theorem quadric_family_descends {F K : Type*} [Field F] [Field K]
    (φ : F →+* K) (h2 : (2 : F) ≠ 0) (L : Finset (ChartLine F)) (hL : 5 ≤ L.card)
    (Q : Zahl.SplitQuadric K)
    (hquadric : ∀ l ∈ L, Zahl.quadricContains Q (mapChart φ l)) :
    ∃ Q₀ : Zahl.SplitQuadric F, ∀ l ∈ L, Zahl.quadricContains Q₀ l := by
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ :=
    Boundary.Descent.exists_base_skew_triple φ h2 L hL Q hquadric
  obtain ⟨Q₀, hQ₀⟩ := Boundary.Descent.quadric_descends_of_skew_triple φ h2 Q
    a b c hab hac hbc (hquadric a ha) (hquadric b hb) (hquadric c hc)
  exact ⟨Q₀, fun l hl => hQ₀ l (hquadric l hl)⟩

end ExplicitRIP.GuthZahl

end
