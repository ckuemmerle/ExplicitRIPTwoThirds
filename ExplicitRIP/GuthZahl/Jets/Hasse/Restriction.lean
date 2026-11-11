/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Jets.Hasse.Index

/-!
# Restriction coefficients and finite jets

Substitute `y = t v` in the literal translate `f(x+y)` and collect terms of a fixed total degree.
-/

public section

namespace ExplicitRIP.GuthZahl

namespace Hasse

theorem restrictLine_eq_eval₂_translatedPolynomial {K : Type*} [Field K]
    (f : Poly K) (x v : Point K) :
    restrictLine f x v =
      MvPolynomial.eval₂Hom (Polynomial.C.comp (MvPolynomial.eval x))
        (fun i => Polynomial.C (v i) * Polynomial.X) (translatedPolynomial f) := by
  have h : (MvPolynomial.eval₂Hom (Polynomial.C.comp (MvPolynomial.eval x))
      (fun i => Polynomial.C (v i) * Polynomial.X)).comp
      (MvPolynomial.eval₂Hom (MvPolynomial.C.comp (MvPolynomial.C : K →+* Poly K))
        (fun i : Fin 3 => MvPolynomial.C (MvPolynomial.X i) + MvPolynomial.X i)) =
      MvPolynomial.eval₂Hom Polynomial.C
        (fun i => Polynomial.C (x i) + Polynomial.C (v i) * Polynomial.X) := by
    apply MvPolynomial.ringHom_ext
    · intro k
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.eval_C]
    · intro i
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', map_add,
        MvPolynomial.eval₂Hom_C, MvPolynomial.eval_X]
  exact (DFunLike.congr_fun h f).symm

theorem coeff_eval₂_direction {K : Type*} [Field K]
    (H : MvPolynomial (Fin 3) (Poly K)) (x v : Point K) (j : ℕ) :
    (MvPolynomial.eval₂Hom (Polynomial.C.comp (MvPolynomial.eval x))
      (fun i => Polynomial.C (v i) * Polynomial.X) H).coeff j =
        ∑ a ∈ H.support, if (∑ i : Fin 3, a i) = j then
          MvPolynomial.eval x (H.coeff a) * ∏ i : Fin 3, v i ^ a i else 0 := by
  classical
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq', Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro a _
  have hp : (∏ i : Fin 3, (Polynomial.C (v i) * Polynomial.X) ^ a i) =
      Polynomial.C (∏ i : Fin 3, v i ^ a i) * Polynomial.X ^ (∑ i : Fin 3, a i) := by
    simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod,
      Finset.prod_pow_eq_pow_sum]
  rw [hp]
  simp only [RingHom.comp_apply, ← mul_assoc, ← map_mul, Polynomial.coeff_C_mul_X_pow,
    eq_comm]

theorem sum_direction_coeff_eq_jet {K : Type*} [Field K]
    (H : MvPolynomial (Fin 3) (Poly K)) (r : ℕ) (x v : Point K)
    (j : ℕ) (hj : j ≤ r) :
    (∑ a ∈ H.support, if (∑ i : Fin 3, a i) = j then
      MvPolynomial.eval x (H.coeff a) * ∏ i : Fin 3, v i ^ a i else 0) =
      ∑ b : JetIndex r, if (∑ i : Fin 3, (b.val i).val) = j then
        MvPolynomial.eval x (H.coeff (jetExponent b)) *
          ∏ i : Fin 3, v i ^ (b.val i).val else 0 := by
  classical
  let S := Finset.univ.image (jetExponent (r := r))
  let T (a : Fin 3 →₀ ℕ) : K := if (∑ i : Fin 3, a i) = j then
    MvPolynomial.eval x (H.coeff a) * ∏ i : Fin 3, v i ^ a i else 0
  have hzero (a : Fin 3 →₀ ℕ) (ha : a ∉ H.support) : T a = 0 := by
    have hc := MvPolynomial.notMem_support_iff.mp ha
    simp only [T, hc, map_zero, zero_mul, ite_self]
  have hout (a : Fin 3 →₀ ℕ) (ha : a ∉ S) : T a = 0 := by
    dsimp only [T]
    split_ifs with h
    · obtain ⟨b, hb⟩ := exists_jetExponent_eq a (h.le.trans hj)
      exact (ha (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, hb⟩)).elim
    · rfl
  calc
    _ = ∑ a ∈ H.support ∪ S, T a :=
      Finset.sum_subset Finset.subset_union_left (fun a _ ha => hzero a ha)
    _ = ∑ a ∈ S, T a :=
      (Finset.sum_subset Finset.subset_union_right (fun a _ ha => hout a ha)).symm
    _ = ∑ b : JetIndex r, T (jetExponent b) :=
      Finset.sum_image (fun _ _ _ _ h => jetExponent_injective r h)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      dsimp only [T]
      apply if_congr
      · exact Iff.of_eq (congrArg (fun n : ℕ => n = j)
          (Finset.sum_congr (by ext i; simp only [Finset.mem_univ])
            (fun i _ => jetExponent_apply b i)))
      · exact congrArg (fun c : K => MvPolynomial.eval x (H.coeff (jetExponent b)) * c)
          (Finset.prod_congr (by ext i; simp only [Finset.mem_univ])
            (fun i _ => congrArg (fun n : ℕ => v i ^ n) (jetExponent_apply b i)))
      · rfl

/-- Finite Taylor expansion without factorial division. -/
theorem _root_.ExplicitRIP.GuthZahl.restriction_coeff_from_jet {K : Type*} [Field K]
    (r : ℕ) (f : Poly K) (x v : Point K) (j : ℕ) (hj : j ≤ r) :
    (restrictLine f x v).coeff j = jetDirectionCoefficient (finiteJet r f x) v j := by
  rw [restrictLine_eq_eval₂_translatedPolynomial, coeff_eval₂_direction,
    sum_direction_coeff_eq_jet (translatedPolynomial f) r x v j hj]
  rfl

end Hasse

end ExplicitRIP.GuthZahl

end
