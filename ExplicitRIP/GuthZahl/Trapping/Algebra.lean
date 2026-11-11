/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Trapping.Algebra.Derivation
public import ExplicitRIP.GuthZahl.Trapping.Algebra.FractionRelation

/-!
# Polynomial algebra for the Guth–Zahl trapping argument

The directional derivative differentiates only the coefficients. Fraction-field
relations lift after clearing denominators, and a polynomial recurrence remains
valid at every order after multiplying by powers of its one denominator.
-/

public section

namespace ExplicitRIP.GuthZahl

open Classical in
/-- Clear finitely many coefficients in a fraction field of K[x]/(f). The canonical quotient
fraction field supplies the hypotheses needed to lift the directional-jet recurrence. -/
theorem lift_fraction_relation {K E : Type*} [Field K] [Field E]
    (f : Poly K) (hf : Irreducible f) (ρ : Poly K →+* E)
    (hker : RingHom.ker ρ = Ideal.span ({f} : Set (Poly K)))
    (hfrac : ∀ z : E, ∃ a b : Poly K, ¬ f ∣ b ∧ z = ρ a / ρ b)
    (s : ℕ) (Hs : DirectionPoly K) (H : Fin s → DirectionPoly K)
    (hrel : MvPolynomial.map ρ Hs ∈
      Ideal.span (Set.range (fun i => MvPolynomial.map ρ (H i)))) :
    ∃ q : Poly K, ¬ f ∣ q ∧ ∃ b : DirectionPoly K,
      ∃ a : Fin s → DirectionPoly K,
        MvPolynomial.C q * Hs = MvPolynomial.C f * b + ∑ i, a i * H i := by
  classical
  have hker' : ∀ r : Poly K, ρ r = 0 ↔ f ∣ r := by
    intro r
    rw [← RingHom.mem_ker, hker, Ideal.mem_span_singleton]
  obtain ⟨q, hq, A, hAI, hA⟩ := TrappingAlgebra.clear_denominator_mem_span
    f (irreducible_iff_prime.mp hf) ρ hker' hfrac H hrel
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp hAI
  have hzero : MvPolynomial.map ρ (MvPolynomial.C q * Hs - A) = 0 := by
    rw [map_sub, map_mul, MvPolynomial.map_C, hA, sub_self]
  obtain ⟨b, hb⟩ :=
    (MvPolynomial.C_dvd_iff_map_hom_eq_zero ρ f hker' _).mpr hzero
  refine ⟨q, hq, b, a, ?_⟩
  rw [ha]
  exact sub_eq_iff_eq_add.mp hb

open Classical in
/-- Polynomial saturation avoids a derivation on a localization. One denominator q suffices; only
its exponent grows. -/
theorem saturated_direction_recurrence {K : Type*} [Field K]
    (f q : Poly K) (s : ℕ) (hs : 1 ≤ s) (a : Fin s → DirectionPoly K)
    (ha : MvPolynomial.C q * directionJet f s =
      ∑ i, a i * directionJet f i.val) :
    ∀ j : ℕ, ∃ e : ℕ, ∃ b : Fin s → DirectionPoly K,
      (MvPolynomial.C q) ^ e * directionJet f j =
        ∑ i, b i * directionJet f i.val := by
  classical
  let Q : DirectionPoly K := MvPolynomial.C q
  let F : Fin s → DirectionPoly K := fun i => directionJet f i.val
  let I : Ideal (DirectionPoly K) := Ideal.span (Set.range F)
  have hF (i : Fin s) : F i ∈ I := Ideal.subset_span (Set.mem_range_self i)
  have hQF (i : Fin s) : Q * directionDeriv (F i) ∈ I := by
    change Q * directionJet f (i.val + 1) ∈ I
    by_cases hi : i.val + 1 < s
    · exact I.mul_mem_left Q (hF ⟨i.val + 1, hi⟩)
    · have hi' : i.val + 1 = s := by omega
      change MvPolynomial.C q * directionJet f (i.val + 1) ∈ I
      rw [hi', ha]
      exact I.sum_mem fun i _ => I.mul_mem_left (a i) (hF i)
  have hDI (P : DirectionPoly K) (hP : P ∈ I) : Q * directionDeriv P ∈ I := by
    induction hP using Submodule.span_induction with
    | mem P hP =>
        obtain ⟨i, rfl⟩ := hP
        exact hQF i
    | zero =>
        rw [TrappingAlgebra.directionDeriv_zero, mul_zero]
        exact I.zero_mem
    | add P R _ _ hP hR =>
        rw [TrappingAlgebra.directionDeriv_add, mul_add]
        exact I.add_mem hP hR
    | smul c P hP hDP =>
        change Q * directionDeriv (c * P) ∈ I
        rw [directionDeriv_mul, mul_add]
        apply I.add_mem
        · simpa only [mul_assoc] using I.mul_mem_left (Q * directionDeriv c) hP
        · simpa only [mul_assoc, mul_left_comm] using I.mul_mem_left c hDP
  have hjet : ∀ j : ℕ, ∃ e : ℕ, Q ^ e * directionJet f j ∈ I := by
    intro j
    induction j with
    | zero =>
        refine ⟨0, ?_⟩
        simpa only [pow_zero, one_mul] using hF ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hs⟩
    | succ j ih =>
        obtain ⟨e, he⟩ := ih
        -- Multiplying again removes the term involving the derivative of the denominator.
        have hd := I.mul_mem_left (Q ^ e) (hDI _ he)
        have hc := I.mul_mem_left (Q * directionDeriv (Q ^ e)) he
        refine ⟨e + e + 1, ?_⟩
        convert I.sub_mem hd hc using 1
        rw [directionDeriv_mul]
        simp only [directionJet, pow_add, pow_one]
        ring
  intro j
  obtain ⟨e, he⟩ := hjet j
  obtain ⟨b, hb⟩ := Ideal.mem_span_range_iff_exists_fun.mp he
  exact ⟨e, b, hb.symm⟩

end ExplicitRIP.GuthZahl

end
