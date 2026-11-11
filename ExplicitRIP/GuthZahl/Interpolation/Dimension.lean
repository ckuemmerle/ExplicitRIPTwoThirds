/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Defs

/-!
# Dimension of bounded total degree polynomials in three variables

Adding a slack exponent identifies bounded exponents with degree-exact multisets
on four variables. Stars and bars then gives the dimension.
-/

@[expose] public section

namespace ExplicitRIP.GuthZahl.Interpolation

/-- Add the unused degree as a fourth exponent. -/
noncomputable def boundedExponentsEquiv (d : ℕ) :
    {m : Fin 3 →₀ ℕ // m.sum (fun _ e => e) ≤ d} ≃
      {m : Fin 4 → ℕ // ∑ i, m i = d} where
  toFun m := ⟨Fin.cons (d - m.1.sum (fun _ e => e)) m.1, by
    rw [Fin.sum_univ_succ]
    simpa only [Fin.cons_zero, Fin.cons_succ,
      ← Finsupp.sum_fintype _ (fun _ e => e) (fun _ => rfl)] using
        Nat.sub_add_cancel m.2⟩
  invFun m := ⟨Finsupp.equivFunOnFinite.symm (Fin.tail m.1), by
    have h := m.2
    rw [Fin.sum_univ_succ] at h
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    change (∑ i : Fin 3, m.1 i.succ) ≤ d
    omega⟩
  left_inv m := by
    apply Subtype.ext
    ext i
    rfl
  right_inv m := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · have h := m.2
      rw [Fin.sum_univ_succ] at h
      change d - (Finsupp.equivFunOnFinite.symm (Fin.tail m.1)).sum
        (fun _ e => e) = m.1 0
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
      change d - (∑ i : Fin 3, m.1 i.succ) = m.1 0
      omega
    · rfl

theorem card_bounded_exponents (d : ℕ) :
    Nat.card {m : Fin 3 →₀ ℕ // m.sum (fun _ e => e) ≤ d} = Nat.choose (d + 3) 3 := by
  rw [Nat.card_congr (boundedExponentsEquiv d),
    ← Nat.card_congr (Sym.equivNatSumOfFintype (Fin 4) d), Nat.card_eq_fintype_card,
    Sym.card_sym_eq_choose]
  simp only [Fintype.card_fin]
  have h : 4 + d - 1 = d + 3 := by omega
  rw [h, ← Nat.choose_symm (show d ≤ d + 3 by omega)]
  congr 1
  omega

theorem finrank_restrictTotalDegree {K : Type*} [Field K] (d : ℕ) :
    Module.finrank K (MvPolynomial.restrictTotalDegree (Fin 3) K d) =
      Nat.choose (d + 3) 3 := by
  unfold MvPolynomial.restrictTotalDegree
  rw [Module.finrank_eq_nat_card_basis
    (MvPolynomial.basisRestrictSupport K {m : Fin 3 →₀ ℕ | m.sum (fun _ e => e) ≤ d})]
  exact card_bounded_exponents d

end ExplicitRIP.GuthZahl.Interpolation

end
