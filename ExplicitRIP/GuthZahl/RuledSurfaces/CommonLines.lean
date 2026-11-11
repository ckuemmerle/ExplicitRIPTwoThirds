/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.RuledSurfaces.LineIdeal

/-!
# Finiteness of common lines of two hypersurfaces

The nonquantitative intersection lemma needed by the ruled-surface argument
follows from finite minimal primes and the height bound for the ideal of a
line. It applies over any infinite field and is used in the ruled-surface
classification. The resultant argument in `GuthZahl/CommonLines` gives a quantitative
bound over algebraically closed fields for component counts and contagion; its stronger
field hypothesis would narrow the statements here.
-/

public section

namespace ExplicitRIP.GuthZahl.RuledSurfaces

variable {K : Type*} [Field K] [Infinite K]

/-- A common line defines a minimal prime of the two surface equations when
one equation is irreducible and does not divide the other. -/
theorem lineIdeal_mem_minimalPrimes {f q : Poly K} (hf : Irreducible f)
    (hq : ¬ f ∣ q) {L : Line K} (hLf : LineOn f L) (hLq : LineOn q L) :
    lineIdeal L ∈ (Ideal.span ({f, q} : Set (Poly K))).minimalPrimes := by
  have hle : Ideal.span ({f, q} : Set (Poly K)) ≤ lineIdeal L := by
    apply Ideal.span_le.mpr
    intro p hp
    rcases Set.mem_insert_iff.mp hp with rfl | hp
    · exact hLf
    · rcases Set.mem_singleton_iff.mp hp with rfl
      exact hLq
  refine ⟨⟨inferInstance, hle⟩, ?_⟩
  intro P hP hPL
  have : P.IsPrime := hP.1
  have hfP : f ∈ P := hP.2 (Ideal.subset_span (Set.mem_insert f {q}))
  have hqP : q ∈ P := hP.2 (Ideal.subset_span (Set.mem_insert_of_mem f (Set.mem_singleton q)))
  by_contra hLP
  have hlt : P < lineIdeal L := lt_of_le_not_ge hPL hLP
  have hheight : P.height < 2 :=
    (Ideal.height_strict_mono_of_isPrime_of_isPrime hlt).trans_le (height_lineIdeal_le_two L)
  have hheight0 : P.height ≠ 0 := by
    intro hh
    have hpbot := Ideal.height_eq_zero_iff_eq_bot.mp hh
    exact hf.ne_zero (Ideal.mem_bot.mp (hpbot ▸ hfP))
  have hheight1 : P.height = 1 := by
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt hheight)
    rw [← hn] at hheight hheight0 ⊢
    norm_cast at hheight hheight0 ⊢
    omega
  have hPspan := Ideal.eq_span_singleton_of_height_eq_one hheight1 hfP hf.prime
  exact hq (Ideal.mem_span_singleton.mp (hPspan ▸ hqP))

/-- Two hypersurfaces have only finitely many common lines if one has an
irreducible equation not dividing the other equation. -/
theorem finite_common_lines_of_not_dvd (f q : Poly K) (hf : Irreducible f)
    (hq : ¬ f ∣ q) : {L : Line K | LineOn f L ∧ LineOn q L}.Finite := by
  apply Set.Finite.of_finite_image (f := lineIdeal)
  · apply (Ideal.finite_minimalPrimes_of_isNoetherianRing (Poly K)
      (Ideal.span ({f, q} : Set (Poly K)))).subset
    rintro I ⟨L, ⟨hLf, hLq⟩, rfl⟩
    exact lineIdeal_mem_minimalPrimes hf hq hLf hLq
  · exact lineIdeal_injective.injOn

/-- Infinitely many common lines force divisibility by an irreducible equation. -/
theorem dvd_of_infinite_common_lines {f q : Poly K} (hf : Irreducible f)
    (h : {L : Line K | LineOn f L ∧ LineOn q L}.Infinite) : f ∣ q := by
  by_contra hdiv
  exact h (finite_common_lines_of_not_dvd f q hf hdiv)

end ExplicitRIP.GuthZahl.RuledSurfaces
end
