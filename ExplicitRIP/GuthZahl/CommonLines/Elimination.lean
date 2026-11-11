/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.CommonLines.Resultant

/-!
# Eliminating one coordinate from two relatively prime surfaces

The resultant supplies a nonzero plane polynomial of degree at most twice the
product of the surface degrees. If both polynomials have degree zero in the
eliminated variable, the first polynomial itself supplies the eliminant.
-/

public section

namespace ExplicitRIP.GuthZahl.CommonLines

theorem totalDegree_coeff_finSuccEquiv_le {K : Type*} [CommSemiring K] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (i : ℕ) :
    ((MvPolynomial.finSuccEquiv K n f).coeff i).totalDegree ≤ f.totalDegree := by
  by_cases hi : (MvPolynomial.finSuccEquiv K n f).coeff i = 0
  · rw [hi, MvPolynomial.totalDegree_zero]
    exact Nat.zero_le _
  · exact (Nat.le_add_right _ _).trans (MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le f i hi)

theorem eval₂_finSuccEquiv {K : Type*} [CommSemiring K] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (x : Fin (n + 1) → K) :
    (MvPolynomial.finSuccEquiv K n f).eval₂ (MvPolynomial.eval (Fin.tail x)) (x 0) =
      MvPolynomial.eval x f := by
  rw [Polynomial.eval₂_eq_eval_map]
  rw [← MvPolynomial.eval_eq_eval_mv_eval', Fin.cons_self_tail]

theorem exists_common_zero_eliminant {K : Type*} [Field K]
    (f g : Poly K) (hf : f ≠ 0) (hg : g ≠ 0) (hcop : IsRelPrime f g)
    (he : 0 < g.totalDegree) :
    ∃ R : MvPolynomial (Fin 2) K, R ≠ 0 ∧
      R.totalDegree ≤ 2 * f.totalDegree * g.totalDegree ∧
      ∀ x : Point K, MvPolynomial.eval x f = 0 → MvPolynomial.eval x g = 0 →
        MvPolynomial.eval (fun i => x i.succ) R = 0 := by
  let F := MvPolynomial.finSuccEquiv K 2 f
  let G := MvPolynomial.finSuccEquiv K 2 g
  have hF : F ≠ 0 := by
    intro h
    apply hf
    apply (MvPolynomial.finSuccEquiv K 2).injective
    exact h.trans (map_zero _).symm
  have hG : G ≠ 0 := by
    intro h
    apply hg
    apply (MvPolynomial.finSuccEquiv K 2).injective
    exact h.trans (map_zero _).symm
  have hFG : IsRelPrime F G := by
    apply IsRelPrime.of_map (MvPolynomial.finSuccEquiv K 2).symm
    simpa only [F, G, AlgEquiv.symm_apply_apply] using hcop
  have hcoeffF : ∀ i, (F.coeff i).totalDegree ≤ f.totalDegree :=
    totalDegree_coeff_finSuccEquiv_le f
  have hcoeffG : ∀ i, (G.coeff i).totalDegree ≤ g.totalDegree :=
    totalDegree_coeff_finSuccEquiv_le g
  have hdegF : F.natDegree ≤ f.totalDegree := by
    dsimp only [F]
    rw [MvPolynomial.natDegree_finSuccEquiv]
    exact MvPolynomial.degreeOf_le_totalDegree f 0
  have hdegG : G.natDegree ≤ g.totalDegree := by
    dsimp only [G]
    rw [MvPolynomial.natDegree_finSuccEquiv]
    exact MvPolynomial.degreeOf_le_totalDegree g 0
  by_cases hdeg : F.natDegree = 0 ∧ G.natDegree = 0
  · have hFC : F = Polynomial.C (F.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg.1
    refine ⟨F.coeff 0, ?_, ?_, ?_⟩
    · intro h
      apply hF
      rw [hFC, h, map_zero]
    · calc
        (F.coeff 0).totalDegree ≤ f.totalDegree := hcoeffF 0
        _ ≤ f.totalDegree * g.totalDegree := Nat.le_mul_of_pos_right _ he
        _ ≤ 2 * f.totalDegree * g.totalDegree := by
          rw [show 2 * f.totalDegree * g.totalDegree =
            2 * (f.totalDegree * g.totalDegree) by ring]
          omega
    · intro x hx _
      have hval : F.eval₂ (MvPolynomial.eval (Fin.tail x)) (x 0) = 0 :=
        (eval₂_finSuccEquiv f x).trans hx
      rwa [hFC, Polynomial.eval₂_C] at hval
  · refine ⟨F.resultant G, resultant_ne_zero_of_isRelPrime F G hF hFG, ?_, ?_⟩
    · calc
        (F.resultant G).totalDegree ≤ F.natDegree * g.totalDegree +
            G.natDegree * f.totalDegree :=
          totalDegree_resultant_le F G f.totalDegree g.totalDegree hcoeffF hcoeffG
        _ ≤ f.totalDegree * g.totalDegree + g.totalDegree * f.totalDegree :=
          Nat.add_le_add (Nat.mul_le_mul_right _ hdegF) (Nat.mul_le_mul_right _ hdegG)
        _ = 2 * f.totalDegree * g.totalDegree := by ring
    · intro x hx hy
      have hxF : F.eval₂ (MvPolynomial.eval (Fin.tail x)) (x 0) = 0 :=
        (eval₂_finSuccEquiv f x).trans hx
      have hxG : G.eval₂ (MvPolynomial.eval (Fin.tail x)) (x 0) = 0 :=
        (eval₂_finSuccEquiv g x).trans hy
      obtain ⟨p, q, _, _, hpq⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant F G
        le_rfl le_rfl (not_and_or.mp hdeg)
      have heval := congrArg (Polynomial.eval₂ (MvPolynomial.eval (Fin.tail x)) (x 0)) hpq
      simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, hxF, hxG, zero_mul,
        zero_add, Polynomial.eval₂_C] at heval
      exact heval.symm

end ExplicitRIP.GuthZahl.CommonLines
end
