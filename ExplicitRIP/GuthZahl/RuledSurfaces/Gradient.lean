/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.RuledSurfaces.Polynomial

/-!
# Nonvanishing gradients of irreducible hypersurfaces

In positive characteristic, a polynomial with all partial derivatives zero is
a power of a polynomial over an algebraically closed coefficient field. This
excludes such a polynomial from being irreducible. The characteristic-zero
case follows directly from the coefficient formula for partial derivatives.
-/

public section

namespace ExplicitRIP.GuthZahl.RuledSurfaces

variable {K : Type*} [Field K]

/-- A vanishing partial derivative kills each coefficient multiplied by its exponent. -/
theorem coeff_mul_exponent_eq_zero {f : Poly K} {i : Fin 3}
    (hi : MvPolynomial.pderiv i f = 0) (d : Fin 3 →₀ ℕ) :
    f.coeff d * (d i : K) = 0 := by
  by_cases hd : d i = 0
  · rw [hd, Nat.cast_zero, mul_zero]
  have hcoeff := congrArg (fun q : Poly K => q.coeff (d - Finsupp.single i 1)) hi
  rw [MvPolynomial.coeff_pderiv, Finsupp.sub_add_single_one_cancel hd,
    AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hcoeff
  have he : (d - Finsupp.single i 1 : Fin 3 →₀ ℕ) i + 1 = d i := by
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
    omega
  have heK : (((d - Finsupp.single i 1 : Fin 3 →₀ ℕ) i : ℕ) : K) + 1 = (d i : K) := by
    simpa only [Nat.cast_add, Nat.cast_one] using congrArg (Nat.cast : ℕ → K) he
  rw [heK] at hcoeff
  exact hcoeff

/-- In characteristic zero, a polynomial with all partial derivatives zero has degree zero. -/
theorem totalDegree_eq_zero_of_pderiv_eq_zero [CharZero K] {f : Poly K}
    (h : ∀ i : Fin 3, MvPolynomial.pderiv i f = 0) : f.totalDegree = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  change f.support.sup (fun d => d.sum (fun _ e => e)) ≤ 0
  apply Finset.sup_le
  intro d hd
  have hd0 : d = 0 := by
    ext i
    have he := coeff_mul_exponent_eq_zero (h i) d
    have hcast : (d i : K) = 0 :=
      (mul_eq_zero.mp he).resolve_left (MvPolynomial.mem_support_iff.mp hd)
    exact Nat.cast_eq_zero.mp hcast
  rw [hd0, Finsupp.sum_zero_index]

/-- In prime characteristic, vanishing partial derivatives force all supported exponents
to be divisible by the characteristic. -/
theorem exponent_dvd_of_pderiv_eq_zero (p : ℕ) [CharP K p] {f : Poly K}
    (h : ∀ i : Fin 3, MvPolynomial.pderiv i f = 0)
    {d : Fin 3 →₀ ℕ} (hd : d ∈ f.support) (i : Fin 3) : p ∣ d i := by
  apply (CharP.cast_eq_zero_iff K p (d i)).mp
  exact (mul_eq_zero.mp (coeff_mul_exponent_eq_zero (h i) d)).resolve_left
    (MvPolynomial.mem_support_iff.mp hd)

/-- Over an algebraically closed field, a polynomial with zero gradient in positive
characteristic is a power of another polynomial. -/
theorem exists_pow_eq_of_pderiv_eq_zero [IsAlgClosed K] (p : ℕ) [CharP K p]
    [Fact p.Prime] (f : Poly K) (h : ∀ i : Fin 3, MvPolynomial.pderiv i f = 0) :
    ∃ q : Poly K, q ^ p = f := by
  classical
  have hp : 0 < p := (Fact.out : p.Prime).pos
  choose roots hroots using fun d : Fin 3 →₀ ℕ =>
    IsAlgClosed.exists_pow_nat_eq (f.coeff d) hp
  let divideExponent : (Fin 3 →₀ ℕ) → (Fin 3 →₀ ℕ) :=
    fun d => d.mapRange (fun n => n / p) (Nat.zero_div p)
  refine ⟨∑ d ∈ f.support, MvPolynomial.monomial (divideExponent d) (roots d), ?_⟩
  rw [sum_pow_char]
  conv_rhs => rw [f.as_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [MvPolynomial.monomial_pow, hroots]
  have hexp : p • divideExponent d = d := by
    ext i
    simp only [divideExponent, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
    exact Nat.mul_div_cancel' (exponent_dvd_of_pderiv_eq_zero p h hd i)
  rw [hexp]

/-- An irreducible polynomial over an algebraically closed field has a nonzero
partial derivative. -/
theorem exists_pderiv_ne_zero [IsAlgClosed K] {f : Poly K} (hf : Irreducible f) :
    ∃ i : Fin 3, MvPolynomial.pderiv i f ≠ 0 := by
  by_contra h
  push Not at h
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hp | hp
  · have : Fact (ringChar K).Prime := ⟨hp⟩
    obtain ⟨q, hq⟩ := exists_pow_eq_of_pderiv_eq_zero (ringChar K) f h
    exact not_irreducible_pow hp.ne_one (hq.symm ▸ hf)
  · have : CharZero K := (CharP.ringChar_zero_iff_CharZero K).mp hp
    exact (totalDegree_pos_of_irreducible hf).ne' (totalDegree_eq_zero_of_pderiv_eq_zero h)

/-- Differentiation decreases positive total degree. -/
theorem totalDegree_pderiv_lt {f : Poly K} (hf : 0 < f.totalDegree) (i : Fin 3) :
    (MvPolynomial.pderiv i f).totalDegree < f.totalDegree := by
  classical
  change (MvPolynomial.pderiv i f).support.sup (fun d => d.sum (fun _ e => e)) < f.totalDegree
  rw [Finset.sup_lt_iff hf]
  intro d hd
  have hcoeff : f.coeff (d + Finsupp.single i 1) ≠ 0 := by
    have hnonzero := MvPolynomial.mem_support_iff.mp hd
    rw [MvPolynomial.coeff_pderiv] at hnonzero
    exact (mul_ne_zero_iff.mp hnonzero).1
  have hle := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hcoeff)
  have hsum : (d + Finsupp.single i 1).sum (fun _ e => e) = d.sum (fun _ e => e) + 1 := by
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
      Finsupp.sum_single_index (by rfl)]
  rw [hsum] at hle
  omega

/-- A nonzero partial derivative of an irreducible equation is not divisible by it. -/
theorem not_dvd_pderiv {f : Poly K} (hf : Irreducible f) {i : Fin 3}
    (hi : MvPolynomial.pderiv i f ≠ 0) : ¬ f ∣ MvPolynomial.pderiv i f := by
  intro hdiv
  exact (totalDegree_pderiv_lt (totalDegree_pos_of_irreducible hf) i).not_ge
    (MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv hi)

/-- The smooth locus of an irreducible hypersurface contains a nonempty principal open. -/
theorem exists_smooth_principalOpen [IsAlgClosed K] {f : Poly K} (hf : Irreducible f) :
    ∃ g : Poly K, ¬ f ∣ g ∧ (principalOpen f g).Nonempty ∧
      ∀ x ∈ principalOpen f g, ∃ i : Fin 3,
        MvPolynomial.eval x (MvPolynomial.pderiv i f) ≠ 0 := by
  obtain ⟨i, hi⟩ := exists_pderiv_ne_zero hf
  have hnotdvd := not_dvd_pderiv hf hi
  exact ⟨MvPolynomial.pderiv i f, hnotdvd, principalOpen_nonempty _ _ hf hnotdvd,
    fun x hx => ⟨i, hx.2⟩⟩

end ExplicitRIP.GuthZahl.RuledSurfaces
end
