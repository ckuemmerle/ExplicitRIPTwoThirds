/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Interpolation.Dimension
public import ExplicitRIP.GuthZahl.Basic.Restriction

/-!
# Polynomial interpolation on finite sets of affine lines

A polynomial of degree at most `d` has `choose (d + 3) 3` coefficients. Each line
imposes at most `d + 1` linear conditions, so sufficiently few lines have a common
nonzero vanishing polynomial. The argument works over arbitrary fields.
-/

public section

namespace ExplicitRIP.GuthZahl

theorem polynomial_interpolation {K : Type*} [Field K]
    (Ls : Finset (Line K)) (d : ℕ)
    (hd : Ls.card * (d + 1) < Nat.choose (d + 3) 3) :
    ∃ f : Poly K, f ≠ 0 ∧ f.totalDegree ≤ d ∧ ∀ L ∈ Ls, LineOn f L := by
  classical
  choose a ha v hv hv0 using (fun L : Line K => line_exists_base_direction L)
  let V := MvPolynomial.restrictTotalDegree (Fin 3) K d
  let T : V →ₗ[K] (Ls → Fin (d + 1) → K) :=
    LinearMap.pi fun L => LinearMap.pi fun j =>
      (Polynomial.lcoeff K j).comp
        ((MvPolynomial.aeval (fun i =>
          Polynomial.C (a L.1 i) + Polynomial.C (v L.1 i) * Polynomial.X)).toLinearMap.comp
            V.subtype)
  have hdim : Module.finrank K (Ls → Fin (d + 1) → K) < Module.finrank K V := by
    change Module.finrank K (Ls → Fin (d + 1) → K) <
      Module.finrank K (MvPolynomial.restrictTotalDegree (Fin 3) K d)
    rw [Module.finrank_pi_fintype]
    simpa only [Module.finrank_fin_fun, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
      smul_eq_mul, Interpolation.finrank_restrictTotalDegree] using hd
  obtain ⟨f, hfker, hf0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot
      (LinearMap.ker_ne_bot_of_finrank_lt (f := T) hdim)
  refine ⟨f.1, ?_, (MvPolynomial.mem_restrictTotalDegree _ _ _).mp f.2, ?_⟩
  · intro h
    exact hf0 (Subtype.ext h)
  · intro L hL
    apply (lineOn_iff_restrictLine_eq_zero f.1 L (a L) (ha L) (v L) (hv L) (hv0 L)).mpr
    apply (Polynomial.ext_iff_natDegree_le
      ((restrictLine_natDegree_le f.1 (a L) (v L)).trans
        ((MvPolynomial.mem_restrictTotalDegree _ _ _).mp f.2))
      (by simp only [Polynomial.natDegree_zero, zero_le])).mpr
    intro j hj
    have hcoeff := congrFun (congrFun (LinearMap.mem_ker.mp hfker) ⟨L, hL⟩)
      ⟨j, Nat.lt_succ_of_le hj⟩
    change (restrictLine f.1 (a L) (v L)).coeff j = 0 at hcoeff
    simpa only [Polynomial.coeff_zero] using hcoeff

end ExplicitRIP.GuthZahl

end
