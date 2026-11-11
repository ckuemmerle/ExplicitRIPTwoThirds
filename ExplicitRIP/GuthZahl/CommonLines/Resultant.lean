/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Defs

/-!
# Resultant estimates for the common-line bound

Column degree estimates control the Sylvester determinant. Relative primality
over a GCD domain makes the Sylvester map injective, proving nonvanishing of
the resultant without a Bézout identity over the coefficient ring.
-/

public section

namespace ExplicitRIP.GuthZahl.CommonLines

open scoped BigOperators

theorem totalDegree_det_le {K σ ι : Type*} [CommRing K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (MvPolynomial σ K)) (d : ι → ℕ)
    (h : ∀ i j, (A i j).totalDegree ≤ d j) :
    A.det.totalDegree ≤ ∑ j, d j := by
  rw [Matrix.det_apply]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro s _
  calc
    (s.sign • ∏ i, A (s i) i).totalDegree ≤ (∏ i, A (s i) i).totalDegree := by
      exact MvPolynomial.totalDegree_smul_le (s.sign : ℤ) _
    _ ≤ ∑ i, (A (s i) i).totalDegree := MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ i, d i := Finset.sum_le_sum fun i _ => h (s i) i

theorem totalDegree_resultant_le {K σ : Type*} [CommRing K]
    (f g : Polynomial (MvPolynomial σ K)) (d e : ℕ)
    (hf : ∀ i, (f.coeff i).totalDegree ≤ d)
    (hg : ∀ i, (g.coeff i).totalDegree ≤ e) :
    (f.resultant g).totalDegree ≤ f.natDegree * e + g.natDegree * d := by
  classical
  let b : Fin (f.natDegree + g.natDegree) → ℕ := Fin.addCases (fun _ => e) (fun _ => d)
  have hb : ∀ i j, (Polynomial.sylvester f g f.natDegree g.natDegree i j).totalDegree
      ≤ b j := by
    intro i j
    induction j using Fin.addCases with
    | left j =>
      simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left, b]
      split_ifs
      · exact hg _
      · exact Nat.zero_le _
    | right j =>
      simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right, b]
      split_ifs
      · exact hf _
      · exact Nat.zero_le _
  have h := totalDegree_det_le _ b hb
  simpa [Polynomial.resultant, b, Fin.sum_univ_add] using h

theorem sylvesterMap_injective_of_isRelPrime {R : Type*} [CommRing R] [IsDomain R]
    [IsGCDMonoid R] (f g : Polynomial R) (hf : f ≠ 0) (hcop : IsRelPrime f g) :
    Function.Injective (Polynomial.sylvesterMap f g le_rfl le_rfl) := by
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  intro pq hpq
  have hzero : f * (pq.2 : Polynomial R) + g * (pq.1 : Polynomial R) = 0 :=
    congrArg Subtype.val hpq
  have hdiv : f ∣ (pq.1 : Polynomial R) := by
    apply hcop.dvd_of_dvd_mul_left
    rw [eq_neg_of_add_eq_zero_right hzero]
    exact dvd_neg.mpr (dvd_mul_right f _)
  have hp : (pq.1 : Polynomial R) = 0 := by
    by_contra hp
    have hle := Polynomial.degree_le_of_dvd hdiv hp
    have hlt := Polynomial.mem_degreeLT.mp pq.1.property
    rw [Polynomial.degree_eq_natDegree hf] at hle
    exact (not_lt_of_ge hle) hlt
  have hq : (pq.2 : Polynomial R) = 0 := by
    rw [hp, mul_zero, add_zero] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left hf
  exact Prod.ext (Subtype.ext hp) (Subtype.ext hq)

theorem resultant_ne_zero_of_isRelPrime {R : Type*} [CommRing R] [IsDomain R]
    [IsGCDMonoid R] (f g : Polynomial R) (hf : f ≠ 0) (hcop : IsRelPrime f g) :
    f.resultant g ≠ 0 := by
  classical
  intro hz
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hz
  let b₁ := Polynomial.degreeLT.basisProd R f.natDegree g.natDegree
  let b₂ := Polynomial.degreeLT.basis R (f.natDegree + g.natDegree)
  let T := Polynomial.sylvesterMap f g le_rfl le_rfl
  let x := b₁.equivFun.symm v
  have hx : T x = 0 := by
    apply b₂.equivFun.injective
    have heq := LinearMap.toMatrix_mulVec_repr b₁ b₂ T x
    have hmat : LinearMap.toMatrix b₁ b₂ T = Polynomial.sylvester f g f.natDegree g.natDegree :=
      Polynomial.toMatrix_sylvesterMap' f g le_rfl le_rfl
    rw [hmat] at heq
    change (Polynomial.sylvester f g f.natDegree g.natDegree).mulVec (b₁.equivFun x) =
      b₂.equivFun (T x) at heq
    rw [show b₁.equivFun x = v from b₁.equivFun.apply_symm_apply v, hMv] at heq
    exact heq.symm.trans (map_zero _).symm
  have hx0 : x = 0 := (sylvesterMap_injective_of_isRelPrime f g hf hcop)
    (hx.trans (map_zero T).symm)
  apply hv
  have heq : b₁.equivFun x = v := b₁.equivFun.apply_symm_apply v
  rw [hx0, map_zero] at heq
  exact heq.symm

end ExplicitRIP.GuthZahl.CommonLines
end
