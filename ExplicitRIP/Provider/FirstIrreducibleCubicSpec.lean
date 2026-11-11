/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Algebra.CubicSelection

/-!
# The first monic irreducible cubic

Source: [KM, Section 4.2, footnote 3].

Finite lexicographic search produces a monic irreducible polynomial of degree three over the
prime field, with every preceding coefficient triple giving a reducible cubic. The coefficient
order uses the representatives `0, …, p - 1` as in [KM, footnote 3].
-/

public section

theorem ExplicitRIP.Provider.firstIrreducibleCubic_spec :
    ∀ (p : ℕ) [Fact p.Prime], ∃ c₂ c₁ c₀ : ZMod p,
      ExplicitRIP.firstIrreducibleCubic p =
          Polynomial.X ^ 3 + Polynomial.C c₂ * Polynomial.X ^ 2 + Polynomial.C c₁ * Polynomial.X +
            Polynomial.C c₀ ∧
        Irreducible (ExplicitRIP.firstIrreducibleCubic p) ∧
        ∀ d₂ d₁ d₀ : ZMod p,
          (d₂.val < c₂.val ∨ d₂.val = c₂.val ∧
              (d₁.val < c₁.val ∨ d₁.val = c₁.val ∧ d₀.val < c₀.val)) →
          ¬ Irreducible (Polynomial.X ^ 3 + Polynomial.C d₂ * Polynomial.X ^ 2 +
            Polynomial.C d₁ * Polynomial.X + Polynomial.C d₀) :=
by
  intro p hp
  obtain ⟨n, hn, hsel, hi, hmin⟩ := ExplicitRIP.CubicSelection.search_spec p
  refine ⟨((n / p ^ 2 : ℕ) : ZMod p), ((n / p % p : ℕ) : ZMod p),
    ((n % p : ℕ) : ZMod p), hsel, ?_, ?_⟩
  · rw [hsel]
    exact hi
  · intro d₂ d₁ d₀ hlex hred
    have henc := ExplicitRIP.CubicSelection.encode_lt_of_lex_lt p d₂ d₁ d₀
      ((n / p ^ 2 : ℕ) : ZMod p) ((n / p % p : ℕ) : ZMod p)
      ((n % p : ℕ) : ZMod p) hlex
    rw [ExplicitRIP.CubicSelection.encode_digits p n hn] at henc
    apply hmin (ExplicitRIP.CubicSelection.encode p d₂ d₁ d₀) henc
    rwa [ExplicitRIP.CubicSelection.cubic_encode]
