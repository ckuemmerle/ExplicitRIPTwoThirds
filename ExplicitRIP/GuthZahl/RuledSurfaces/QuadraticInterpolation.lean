/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.RuledSurfaces.Restriction
public import ExplicitRIP.GuthZahl.RuledSurfaces.LinearEquation
public import ExplicitRIP.GuthZahl.RuledSurfaces.Polynomial

/-!
# Quadratic interpolation on three lines

The ten monomials of total degree at most two give a ten-dimensional space.
Each of three line restrictions imposes at most three coefficient equations,
so some nonzero quadratic polynomial vanishes on all three lines.
-/

@[expose] public section

namespace ExplicitRIP.GuthZahl.RuledSurfaces

/-- Exponent vectors of the ten monomials of total degree at most two in three variables. -/
noncomputable def quadraticExponents : Fin 10 → (Fin 3 →₀ ℕ) :=
  ![0, Finsupp.single 0 1, Finsupp.single 1 1, Finsupp.single 2 1,
    Finsupp.single 0 2, Finsupp.single 0 1 + Finsupp.single 1 1,
    Finsupp.single 0 1 + Finsupp.single 2 1, Finsupp.single 1 2,
    Finsupp.single 1 1 + Finsupp.single 2 1, Finsupp.single 2 2]

theorem quadraticExponents_injective : Function.Injective quadraticExponents := by
  intro i j hij
  have h0 := congrArg (fun d : Fin 3 →₀ ℕ => d 0) hij
  have h1 := congrArg (fun d : Fin 3 →₀ ℕ => d 1) hij
  have h2 := congrArg (fun d : Fin 3 →₀ ℕ => d 2) hij
  fin_cases i <;> fin_cases j <;>
    norm_num [quadraticExponents, Finsupp.single_apply] at *

theorem quadraticExponents_sum_le_two (i : Fin 10) :
    (quadraticExponents i).sum (fun _ e => e) ≤ 2 := by
  fin_cases i <;>
    norm_num [quadraticExponents, Finsupp.sum_add_index', Finsupp.sum_single_index]

variable {K : Type*} [Field K]

/-- Linear combination of the ten quadratic monomials. -/
noncomputable def quadraticCombination : (Fin 10 →₀ K) →ₗ[K] Poly K :=
  Finsupp.linearCombination K (fun i => MvPolynomial.monomial (quadraticExponents i) 1)

theorem quadraticCombination_injective : Function.Injective (quadraticCombination (K := K)) := by
  have hli := (MvPolynomial.basisMonomials (Fin 3) K).linearIndependent.comp
    quadraticExponents quadraticExponents_injective
  exact hli.finsuppLinearCombination_injective

theorem totalDegree_quadraticCombination_le_two (c : Fin 10 →₀ K) :
    (quadraticCombination c).totalDegree ≤ 2 := by
  classical
  change (c.sum fun i r => r • MvPolynomial.monomial (quadraticExponents i) 1).totalDegree ≤ 2
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  apply (MvPolynomial.totalDegree_smul_le _ _).trans
  exact (MvPolynomial.totalDegree_monomial_le _ _).trans (quadraticExponents_sum_le_two i)

/-- Three affine lines always lie on a nonzero polynomial of total degree at most two. -/
theorem exists_quadratic_on_three_lines [Infinite K] (Ls : Fin 3 → Line K) :
    ∃ q : Poly K, q ≠ 0 ∧ q.totalDegree ≤ 2 ∧ ∀ i, LineOn q (Ls i) := by
  classical
  choose a v ha hv hv0 hparam using fun i : Fin 3 => exists_line_parametrization (Ls i)
  let r : Fin 3 → Poly K →ₐ[K] Polynomial K := fun i =>
    MvPolynomial.aeval (fun j => Polynomial.C (a i j) + Polynomial.C (v i j) * Polynomial.X)
  let F : (Fin 10 →₀ K) →ₗ[K] (Fin 3 → Fin 3 → K) :=
    LinearMap.pi fun i => LinearMap.pi fun j =>
      (Polynomial.lcoeff K j).comp ((r i).toLinearMap.comp quadraticCombination)
  have hdim : Module.finrank K (Fin 3 → Fin 3 → K) < Module.finrank K (Fin 10 →₀ K) := by
    simp [Module.finrank_pi_fintype, Module.finrank_finsupp_self]
  obtain ⟨c, hc, hc0⟩ :=
    (LinearMap.ker F).ne_bot_iff.mp (LinearMap.ker_ne_bot_of_finrank_lt (f := F) hdim)
  have hq0 : quadraticCombination c ≠ 0 := by
    intro hq
    exact hc0 (quadraticCombination_injective (hq.trans (map_zero quadraticCombination).symm))
  refine ⟨quadraticCombination c, hq0, totalDegree_quadraticCombination_le_two c, fun i => ?_⟩
  apply (lineOn_iff_restrictLine_eq_zero _ _ _ (ha i) _ (hv i) (hv0 i)).2
  apply polynomial_eq_zero_of_coeff_le _ 2
  · exact (restrictLine_natDegree_le _ _ _).trans (totalDegree_quadraticCombination_le_two c)
  · intro n hn
    have he := congrFun (congrFun (LinearMap.mem_ker.mp hc) i) (⟨n, by omega⟩ : Fin 3)
    exact he

/-- A nonzero polynomial vanishing on a line is not a unit. -/
theorem not_isUnit_of_lineOn {f : Poly K} {L : Line K} (hL : LineOn f L) : ¬ IsUnit f := by
  intro hf
  obtain ⟨a, ha⟩ := line_nonempty L
  exact (hf.map (MvPolynomial.eval a)).ne_zero (eval_eq_zero_of_lineOn hL ha)

/-- A nonzero nonunit polynomial over a field has positive total degree. -/
theorem totalDegree_pos_of_nonzero_not_isUnit {f : Poly K} (hf0 : f ≠ 0)
    (hfunit : ¬ IsUnit f) : 0 < f.totalDegree := by
  by_contra h
  have heq := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_not_pos h)
  have hc : f.coeff 0 ≠ 0 := by
    intro hz
    exact hf0 (heq.trans (by rw [hz, map_zero]))
  exact hfunit (heq.symm ▸ (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C)

/-- A quadratic polynomial containing three pairwise skew lines is irreducible. -/
theorem irreducible_of_three_skew_lines [Infinite K] {q : Poly K} (hq : q ≠ 0)
    (hdegree : q.totalDegree ≤ 2) (A B C : Line K)
    (hAB : ¬ Coplanar A B) (hAC : ¬ Coplanar A C) (hBC : ¬ Coplanar B C)
    (hA : LineOn q A) (hB : LineOn q B) (hC : LineOn q C) : Irreducible q := by
  refine ⟨not_isUnit_of_lineOn hA, ?_⟩
  intro f g heq
  by_contra hunits
  push Not at hunits
  have hf0 : f ≠ 0 := left_ne_zero_of_mul (heq ▸ hq)
  have hg0 : g ≠ 0 := right_ne_zero_of_mul (heq ▸ hq)
  have hfpos := totalDegree_pos_of_nonzero_not_isUnit hf0 hunits.1
  have hgpos := totalDegree_pos_of_nonzero_not_isUnit hg0 hunits.2
  have hsum : f.totalDegree + g.totalDegree ≤ 2 := by
    rw [← MvPolynomial.totalDegree_mul_of_isDomain hf0 hg0, ← heq]
    exact hdegree
  have hfdeg : f.totalDegree = 1 := by omega
  have hgdeg : g.totalDegree = 1 := by omega
  rw [heq, lineOn_mul_iff] at hA hB hC
  rcases hA with hA | hA
  · have hBg : LineOn g B := hB.resolve_left (fun hB => hAB (coplanar_of_lineOn_linear hfdeg hA hB))
    have hCg : LineOn g C := hC.resolve_left (fun hC => hAC (coplanar_of_lineOn_linear hfdeg hA hC))
    exact hBC (coplanar_of_lineOn_linear hgdeg hBg hCg)
  · have hBf : LineOn f B :=
      hB.resolve_right (fun hB => hAB (coplanar_of_lineOn_linear hgdeg hA hB))
    have hCf : LineOn f C :=
      hC.resolve_right (fun hC => hAC (coplanar_of_lineOn_linear hgdeg hA hC))
    exact hBC (coplanar_of_lineOn_linear hfdeg hBf hCf)

/-- Three pairwise skew affine lines lie on an irreducible quadratic polynomial. -/
theorem exists_irreducible_quadric_of_skew_triple [Infinite K] (A B C : Line K)
    (hAB : ¬ Coplanar A B) (hAC : ¬ Coplanar A C) (hBC : ¬ Coplanar B C) :
    ∃ q : Poly K, Irreducible q ∧ q.totalDegree = 2 ∧
      LineOn q A ∧ LineOn q B ∧ LineOn q C := by
  obtain ⟨q, hq, hdegree, hlines⟩ := exists_quadratic_on_three_lines ![A, B, C]
  have hA := hlines 0
  have hB := hlines 1
  have hC := hlines 2
  have hirr := irreducible_of_three_skew_lines hq hdegree A B C hAB hAC hBC hA hB hC
  have hpos := totalDegree_pos_of_irreducible hirr
  have hnotone : q.totalDegree ≠ 1 := fun h => hAB (coplanar_of_lineOn_linear h hA hB)
  exact ⟨q, hirr, by omega, hA, hB, hC⟩

end ExplicitRIP.GuthZahl.RuledSurfaces
end
