/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Trapping.Defs
import ExplicitRIP.GuthZahl.ACC
import ExplicitRIP.GuthZahl.Basic
import ExplicitRIP.GuthZahl.Trapping.Algebra
import ExplicitRIP.GuthZahl.Trapping.Jets

/-!
# Uniform generic trapping of lines

Quantitative ACC applied to the positive-order directional jets supplies a
field-independent recurrence order. The recurrence is lifted from the fraction
field of an irreducible hypersurface before using polynomial saturation. On the
resulting principal open, coefficient tangency forces containment of the line
whenever the surface degree is strictly less than the characteristic.
-/

public section

namespace ExplicitRIP.GuthZahl

open Classical in
/-- The positive-order direction jets satisfy an ideal-membership recurrence with an order bound
independent of the field and surface degree. -/
theorem shifted_direction_recurrence :
    ∃ R : ℕ, 1 ≤ R ∧ ∀ (K : Type*) [Field K] (f : Poly K)
      (E : Type*) [Field E] (ρ : Poly K →+* E),
      ∃ s : ℕ, 1 ≤ s ∧ s ≤ R ∧
        MvPolynomial.map ρ (directionJet f s) ∈
          Ideal.span ((fun i => MvPolynomial.map ρ (directionJet f i)) '' Set.Iio s) := by
  obtain ⟨M, hM⟩ := quantitative_acc 3 (fun j => j + 1)
  refine ⟨M + 1, Nat.succ_le_succ (Nat.zero_le M), ?_⟩
  intro K _ f E _ ρ
  let fs : ℕ → MvPolynomial (Fin 3) E := fun j =>
    MvPolynomial.map ρ (directionJet f (j + 1))
  have hdegree (j : ℕ) : (fs j).totalDegree ≤ j + 1 := by
    have hmap : (fs j).totalDegree ≤ (directionJet f (j + 1)).totalDegree :=
      Finset.sup_mono (MvPolynomial.support_map_subset ρ _)
    exact hmap.trans (directionJet_totalDegree_le f (j + 1))
  obtain ⟨j, hj, hrel⟩ := hM E fs hdegree
  refine ⟨j + 1, Nat.succ_le_succ (Nat.zero_le j), Nat.succ_le_succ hj, ?_⟩
  apply Ideal.span_mono ?_ hrel
  rintro H ⟨i, hi, rfl⟩
  exact ⟨i + 1, Nat.succ_lt_succ hi, rfl⟩

open Classical in
/-- Clearing the fraction-field recurrence gives a polynomial recurrence; the multiple of the
surface equation is absorbed into the coefficient of jet zero. -/
theorem polynomial_direction_recurrence :
    ∃ R : ℕ, 1 ≤ R ∧ ∀ (K : Type*) [Field K] (f : Poly K),
      Irreducible f → ∃ s : ℕ, 1 ≤ s ∧ s ≤ R ∧
        ∃ q : Poly K, ¬ f ∣ q ∧ ∃ a : Fin s → DirectionPoly K,
          MvPolynomial.C q * directionJet f s =
            ∑ i, a i * directionJet f i.val := by
  obtain ⟨R, hR, hrec⟩ := shifted_direction_recurrence
  refine ⟨R, hR, ?_⟩
  intro K _ f hf
  let I : Ideal (Poly K) := Ideal.span {f}
  have : I.IsPrime := Ideal.isPrime_span_singleton_of_prime
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp hf)
  let A := Poly K ⧸ I
  let E := FractionRing A
  let ρ : Poly K →+* E := (algebraMap A E).comp (Ideal.Quotient.mk I)
  have hker : RingHom.ker ρ = I := by
    rw [RingHom.ker_comp_of_injective _ (IsFractionRing.injective A E), Ideal.mk_ker]
  have hfrac : ∀ z : E, ∃ a b : Poly K, ¬ f ∣ b ∧ z = ρ a / ρ b := by
    intro z
    obtain ⟨a, b, hb, hz⟩ := IsFractionRing.div_surjective A z
    obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
    refine ⟨a', b', ?_, hz.symm⟩
    intro hfb
    exact (nonZeroDivisors.ne_zero hb)
      (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hfb))
  obtain ⟨s, hs, hsR, hrel⟩ := hrec K f E ρ
  have hrel' : MvPolynomial.map ρ (directionJet f s) ∈
      Ideal.span (Set.range (fun i : Fin s => MvPolynomial.map ρ (directionJet f i.val))) := by
    apply Ideal.span_mono ?_ hrel
    rintro H ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩
  obtain ⟨q, hq, b, a, ha⟩ := lift_fraction_relation f hf ρ hker hfrac s
    (directionJet f s) (fun i => directionJet f i.val) hrel'
  let J : Ideal (DirectionPoly K) :=
    Ideal.span (Set.range (fun i : Fin s => directionJet f i.val))
  have hjet (i : Fin s) : directionJet f i.val ∈ J :=
    Ideal.subset_span (Set.mem_range_self i)
  have hzero : MvPolynomial.C f ∈ J :=
    hjet ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hs⟩
  have hmem : MvPolynomial.C q * directionJet f s ∈ J := by
    rw [ha]
    exact J.add_mem (J.mul_mem_right b hzero)
      (J.sum_mem fun i _ => J.mul_mem_left (a i) (hjet i))
  obtain ⟨a', ha'⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
  exact ⟨s, hs, hsR, q, hq, a', ha'.symm⟩

open Classical in
/-- Specialize the saturated relations where q is nonzero. -/
theorem direction_recurrence_specializes {K : Type*} [Field K]
    (f q : Poly K) (s : ℕ) (hs : 1 ≤ s) (a : Fin s → DirectionPoly K)
    (ha : MvPolynomial.C q * directionJet f s =
      ∑ i, a i * directionJet f i.val)
    (x v : Point K) (hq : MvPolynomial.eval x q ≠ 0)
    (hj : ∀ j < s, evalDirection (directionJet f j) x v = 0) :
    ∀ j, evalDirection (directionJet f j) x v = 0 := by
  let ev : DirectionPoly K →+* K :=
    (MvPolynomial.eval v).comp (MvPolynomial.map (MvPolynomial.eval x))
  have hjet (i : Fin s) : ev (directionJet f i.val) = 0 := hj i.val i.isLt
  have hevq : ev (MvPolynomial.C q) = MvPolynomial.eval x q := by
    simp only [ev, RingHom.coe_comp, Function.comp_apply, MvPolynomial.map_C,
      MvPolynomial.eval_C]
  intro j
  obtain ⟨e, b, hb⟩ := saturated_direction_recurrence f q s hs a ha j
  have he := congrArg ev hb
  rw [map_mul, map_pow, hevq, map_sum] at he
  have hsum : (∑ i, ev (b i * directionJet f i.val)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [map_mul, hjet, mul_zero]
  rw [hsum] at he
  exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero e hq)

open Classical in
/-- Invert factorials only through the actual degree, strictly below p. -/
theorem all_directionJets_trap {K : Type*} [Field K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (f : Poly K)
    (hd : f.totalDegree < p) (x v : Point K)
    (hj : ∀ j ≤ f.totalDegree, evalDirection (directionJet f j) x v = 0) :
    restrictLine f x v = 0 := by
  ext j
  rw [Polynomial.coeff_zero]
  by_cases hle : j ≤ f.totalDegree
  · have hfac : (j.factorial : K) ≠ 0 :=
      ((IsUnit.natCast_factorial_iff_of_charP p).mpr (hle.trans_lt hd)).ne_zero
    have h := hj j hle
    rw [eval_directionJet] at h
    exact (mul_eq_zero.mp h).resolve_left hfac
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt
      ((restrictLine_natDegree_le f x v).trans_lt (Nat.lt_of_not_ge hle))

open Classical in
/-- Line-only generic trapping. The order is independent of the surface degree and field. For
lines, degree < characteristic suffices; coefficient tangency also handles r ≥ p. -/
theorem uniform_generic_trapping :
    ∃ r : ℕ, 1 ≤ r ∧ ∀ (p : ℕ) [Fact p.Prime]
      (K : Type*) [Field K] [IsAlgClosed K] [CharP K p]
      (f : Poly K), Irreducible f → f.totalDegree < p →
      ∃ g : Poly K, ¬ f ∣ g ∧ (principalOpen f g).Nonempty ∧
        ∀ x ∈ principalOpen f g, ∀ v : Point K, v ≠ 0 →
          TangentToOrder f x v r → restrictLine f x v = 0 := by
  obtain ⟨R, hR, hrec⟩ := polynomial_direction_recurrence
  refine ⟨R, hR, ?_⟩
  intro p _ K _ _ _ f hf hd
  obtain ⟨s, hs, hsR, q, hq, a, ha⟩ := hrec K f hf
  refine ⟨q, hq, principalOpen_nonempty f q hf hq, ?_⟩
  intro x hx v _ ht
  have hj : ∀ j < s, evalDirection (directionJet f j) x v = 0 := by
    intro j hj
    rw [eval_directionJet, ht j (Nat.le_trans (Nat.le_of_lt hj) hsR), mul_zero]
  have hall := direction_recurrence_specializes f q s hs a ha x v hx.2 hj
  exact all_directionJets_trap p f hd x v (fun j _ => hall j)

end ExplicitRIP.GuthZahl

end
