/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Trapping.Defs

/-!
# Clearing denominators in polynomial ideal relations

First lift one polynomial after multiplying by a scalar denominator. An
induction on ideal membership then clears the finitely many denominators in
an ideal relation, without any choice of a derivation on the quotient field.
-/

public section

namespace ExplicitRIP.GuthZahl.TrappingAlgebra

theorem exists_polynomial_denominator {R E σ : Type*} [CommRing R] [Field E]
    (f : R) (hf : Prime f) (ρ : R →+* E)
    (hker : ∀ r : R, ρ r = 0 ↔ f ∣ r)
    (hfrac : ∀ z : E, ∃ a b : R, ¬ f ∣ b ∧ z = ρ a / ρ b)
    (P : MvPolynomial σ E) :
    ∃ q : R, ¬ f ∣ q ∧ ∃ A : MvPolynomial σ R,
      MvPolynomial.C (ρ q) * P = MvPolynomial.map ρ A := by
  classical
  induction P using MvPolynomial.induction_on with
  | C z =>
      obtain ⟨a, b, hb, hz⟩ := hfrac z
      have hb0 : ρ b ≠ 0 := fun h => hb ((hker b).mp h)
      refine ⟨b, hb, MvPolynomial.C a, ?_⟩
      rw [MvPolynomial.map_C, ← map_mul]
      congr 1
      rw [hz, mul_comm, div_mul_cancel₀ _ hb0]
  | add P Q hP hQ =>
      obtain ⟨q, hq, A, hA⟩ := hP
      obtain ⟨r, hr, B, hB⟩ := hQ
      refine ⟨q * r, hf.not_dvd_mul hq hr,
        MvPolynomial.C r * A + MvPolynomial.C q * B, ?_⟩
      simp only [map_add, map_mul, MvPolynomial.map_C]
      rw [← hA, ← hB]
      ring
  | mul_X P i hP =>
      obtain ⟨q, hq, A, hA⟩ := hP
      refine ⟨q, hq, A * MvPolynomial.X i, ?_⟩
      rw [map_mul, MvPolynomial.map_X, ← hA, mul_assoc]

theorem clear_denominator_mem_span {R E σ ι : Type*} [CommRing R] [Field E]
    (f : R) (hf : Prime f) (ρ : R →+* E)
    (hker : ∀ r : R, ρ r = 0 ↔ f ∣ r)
    (hfrac : ∀ z : E, ∃ a b : R, ¬ f ∣ b ∧ z = ρ a / ρ b)
    (H : ι → MvPolynomial σ R) {P : MvPolynomial σ E}
    (hP : P ∈ Ideal.span (Set.range (fun i => MvPolynomial.map ρ (H i)))) :
    ∃ q : R, ¬ f ∣ q ∧ ∃ A ∈ Ideal.span (Set.range H),
      MvPolynomial.C (ρ q) * P = MvPolynomial.map ρ A := by
  classical
  induction hP using Submodule.span_induction with
  | mem P hP =>
      obtain ⟨i, rfl⟩ := hP
      refine ⟨1, hf.not_dvd_one, H i, Ideal.subset_span (Set.mem_range_self i), ?_⟩
      simp only [map_one, one_mul]
  | zero =>
      refine ⟨1, hf.not_dvd_one, 0, Ideal.zero_mem _, ?_⟩
      simp only [mul_zero, map_zero]
  | add P Q _ _ hP hQ =>
      obtain ⟨q, hq, A, hAI, hA⟩ := hP
      obtain ⟨r, hr, B, hBI, hB⟩ := hQ
      refine ⟨q * r, hf.not_dvd_mul hq hr,
        MvPolynomial.C r * A + MvPolynomial.C q * B,
        Ideal.add_mem _ (Ideal.mul_mem_left _ _ hAI) (Ideal.mul_mem_left _ _ hBI), ?_⟩
      simp only [map_add, map_mul, MvPolynomial.map_C]
      rw [← hA, ← hB]
      ring
  | smul P Q _ hQ =>
      obtain ⟨q, hq, A, hAI, hA⟩ := hQ
      obtain ⟨r, hr, B, hB⟩ := exists_polynomial_denominator f hf ρ hker hfrac P
      refine ⟨q * r, hf.not_dvd_mul hq hr, B * A,
        Ideal.mul_mem_left _ _ hAI, ?_⟩
      simp only [smul_eq_mul, map_mul]
      rw [← hA, ← hB]
      ring

end ExplicitRIP.GuthZahl.TrappingAlgebra

end
