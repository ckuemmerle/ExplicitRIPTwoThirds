/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.Data.Fintype.Order
import Mathlib.Tactic.Choose

/-!
# Reduced representatives for strict polynomial sequences

Divide by all nonzero elements of the preceding ideal using the degree-lexicographic
order. The remainder has no greater total degree, and its leading exponent is not
divisible by any leading exponent in that ideal. Applied to a strict polynomial
sequence, these remainders give a controlled bad sequence of exponent vectors.
-/

public section

namespace ExplicitRIP.GuthZahl.ACC

open MonomialOrder

/-- A nonzero reduced representative modulo an ideal, with no increase in total degree. -/
theorem exists_reduced_representative (N : ℕ) (K : Type*) [Field K]
    (I : Ideal (MvPolynomial (Fin N) K)) (f : MvPolynomial (Fin N) K) (hf : f ∉ I) :
    ∃ r : MvPolynomial (Fin N) K, r ≠ 0 ∧ r.totalDegree ≤ f.totalDegree ∧
      f - r ∈ I ∧ ∀ b ∈ I, b ≠ 0 → ¬ degLex.degree b ≤ degLex.degree r := by
  classical
  let B : Set (MvPolynomial (Fin N) K) := {b | b ∈ I ∧ b ≠ 0}
  have hB : ∀ b ∈ B, IsUnit (degLex.leadingCoeff b) := by
    intro b hb
    exact isUnit_iff_ne_zero.mpr (fun h => hb.2 (degLex.leadingCoeff_eq_zero_iff.mp h))
  obtain ⟨g, r, hfr, hdeg, hred⟩ := degLex.div_set hB f
  let q := Finsupp.linearCombination (MvPolynomial (Fin N) K) (fun b : B => b.val) g
  change f = q + r at hfr
  have hqmem : q ∈ I := by
    dsimp only [q]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    exact I.sum_mem (fun b _ => I.smul_mem (g b) b.property.1)
  have hqdeg : q.totalDegree ≤ f.totalDegree := by
    dsimp only [q]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    apply MvPolynomial.totalDegree_finsetSum_le
    intro b _
    simpa only [smul_eq_mul, mul_comm] using MvPolynomial.degLex_totalDegree_monotone (hdeg b)
  have hr0 : r ≠ 0 := by
    intro hr
    apply hf
    rw [hfr, hr, add_zero]
    exact hqmem
  have hrdeg : r.totalDegree ≤ f.totalDegree := by
    have hr : r = f - q := by rw [hfr, add_sub_cancel_left]
    rw [hr]
    exact (MvPolynomial.totalDegree_sub _ _).trans (max_le le_rfl hqdeg)
  refine ⟨r, hr0, hrdeg, ?_, ?_⟩
  · simpa only [hfr, add_sub_cancel_right] using hqmem
  · intro b hb hb0
    exact hred _ (degLex.degree_mem_support hr0) b ⟨hb, hb0⟩

/-- Degree-compatible division by the preceding ideal gives a controlled bad monomial sequence.
No degree bound on a Groebner basis is needed. -/
theorem _root_.ExplicitRIP.GuthZahl.strict_polynomial_sequence_monomials (N m : ℕ) (τ : ℕ → ℕ)
    (K : Type*) [Field K] (fs : Fin m → MvPolynomial (Fin N) K)
    (hdegree : ∀ i, (fs i).totalDegree ≤ τ i.val)
    (hstrict : ∀ i, fs i ∉ Ideal.span (fs '' Set.Iio i)) :
    ∃ a : Fin m → (Fin N → ℕ),
      (∀ i, (∑ k, a i k) ≤ τ i.val) ∧
      ∀ i j, i < j → ¬ a i ≤ a j := by
  classical
  choose r hr0 hrdeg hrmem hrred using
    (fun i => exists_reduced_representative N K
      (Ideal.span (fs '' Set.Iio i)) (fs i) (hstrict i))
  refine ⟨fun i => degLex.degree (r i), ?_, ?_⟩
  · intro i
    rw [← Finsupp.degree_eq_sum, MvPolynomial.degree_degLexDegree]
    exact (hrdeg i).trans (hdegree i)
  · intro i j hij hle
    apply hrred j (r i) ?_ (hr0 i) hle
    have hmono : Ideal.span (fs '' Set.Iio i) ≤ Ideal.span (fs '' Set.Iio j) :=
      Ideal.span_mono (Set.image_mono (Set.Iio_subset_Iio (le_of_lt hij)))
    have hfi : fs i ∈ Ideal.span (fs '' Set.Iio j) :=
      Ideal.subset_span (Set.mem_image_of_mem fs hij)
    have hdiff := (Ideal.span (fs '' Set.Iio j)).sub_mem hfi (hmono (hrmem i))
    simpa only [sub_sub_cancel] using hdiff

end ExplicitRIP.GuthZahl.ACC

end
