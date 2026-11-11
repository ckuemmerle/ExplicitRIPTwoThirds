/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib
public import ExplicitRIP.Frozen.Defs.FirstIrreducibleCubic

/-!
# Cubic enumeration over a prime field

Base-`p` coefficient encoding, existence of irreducible cubics, and correctness of the
finite search used by `firstIrreducibleCubic`.
-/

@[expose] public section

namespace ExplicitRIP.CubicSelection

open Polynomial

noncomputable section

/-- The cubic at index `n` in the enumeration defining `firstIrreducibleCubic`. -/
def cubic (p n : ℕ) : Polynomial (ZMod p) :=
  X ^ 3 + C ((n / p ^ 2 : ℕ) : ZMod p) * X ^ 2 +
    C ((n / p % p : ℕ) : ZMod p) * X + C ((n % p : ℕ) : ZMod p)

/-- Encode the three canonical residue representatives in base `p`. -/
def encode (p : ℕ) (a b c : ZMod p) : ℕ := a.val * p ^ 2 + b.val * p + c.val

/-- The base-`p` encoding has the asserted three digits and lies in the search range. -/
theorem digits (p a b c : ℕ) (_hp : 0 < p) (ha : a < p) (hb : b < p) (hc : c < p) :
    let n := a * p ^ 2 + b * p + c
    n < p ^ 3 ∧ n / p ^ 2 = a ∧ n / p % p = b ∧ n % p = c := by
  dsimp
  have htail : b * p + c < p ^ 2 := by
    have hmul := Nat.mul_le_mul_right p (Nat.succ_le_of_lt hb)
    nlinarith
  have htop := Nat.mul_le_mul_right (p ^ 2) (Nat.succ_le_of_lt ha)
  have hdiv₂ : (a * p ^ 2 + b * p + c) / p ^ 2 = a := by
    apply Nat.div_eq_of_lt_le <;> nlinarith
  have hdiv : (a * p ^ 2 + b * p + c) / p = a * p + b := by
    apply Nat.div_eq_of_lt_le <;> nlinarith
  have heq : a * p ^ 2 + b * p + c = (a * p + b) * p + c := by ring
  refine ⟨by nlinarith [pow_succ p 2], hdiv₂, ?_, ?_⟩
  · rw [hdiv, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hb]
  · rw [heq, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hc]

theorem encode_lt (p : ℕ) [Fact p.Prime] (a b c : ZMod p) : encode p a b c < p ^ 3 :=
  (digits p a.val b.val c.val (Fact.out : p.Prime).pos
    (ZMod.val_lt a) (ZMod.val_lt b) (ZMod.val_lt c)).1

theorem cubic_encode (p : ℕ) [Fact p.Prime] (a b c : ZMod p) :
    cubic p (encode p a b c) = X ^ 3 + C a * X ^ 2 + C b * X + C c := by
  obtain ⟨_, h₂, h₁, h₀⟩ := digits p a.val b.val c.val (Fact.out : p.Prime).pos
    (ZMod.val_lt a) (ZMod.val_lt b) (ZMod.val_lt c)
  simp only [cubic, encode, h₂, h₁, h₀, ZMod.natCast_zmod_val]

/-- Every monic cubic has the coefficient presentation used in the finite search. -/
theorem eq_cubic_coeff {K : Type*} [Field K] (f : Polynomial K)
    (hm : f.Monic) (hd : f.natDegree = 3) :
    f = X ^ 3 + C (f.coeff 2) * X ^ 2 + C (f.coeff 1) * X + C (f.coeff 0) := by
  conv_lhs => rw [hm.as_sum, hd]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, mul_one,
    pow_one]
  ring

/-- A degree-three finite extension supplies a monic irreducible cubic. -/
theorem exists_monic_irreducible_cubic (p : ℕ) [Fact p.Prime] :
    ∃ f : Polynomial (ZMod p), f.Monic ∧ Irreducible f ∧ f.natDegree = 3 := by
  let pb := Field.powerBasisOfFiniteOfSeparable (ZMod p) (GaloisField p 3)
  refine ⟨minpoly (ZMod p) pb.gen, minpoly.monic pb.isIntegral_gen,
    minpoly.irreducible pb.isIntegral_gen, ?_⟩
  rw [pb.natDegree_minpoly, ← pb.finrank, GaloisField.finrank p (by decide)]

theorem exists_irreducible_index (p : ℕ) [Fact p.Prime] :
    ∃ n < p ^ 3, Irreducible (cubic p n) := by
  obtain ⟨f, hm, hi, hd⟩ := exists_monic_irreducible_cubic p
  refine ⟨encode p (f.coeff 2) (f.coeff 1) (f.coeff 0), encode_lt p _ _ _, ?_⟩
  rw [cubic_encode, ← eq_cubic_coeff f hm hd]
  exact hi

/-- Recover an index from its three digits within the enumeration range. -/
theorem encode_digits (p n : ℕ) [Fact p.Prime] (hn : n < p ^ 3) :
    encode p ((n / p ^ 2 : ℕ) : ZMod p) ((n / p % p : ℕ) : ZMod p)
      ((n % p : ℕ) : ZMod p) = n := by
  have hp := (Fact.out : p.Prime).pos
  have h₂ : n / p ^ 2 < p := (Nat.div_lt_iff_lt_mul (pow_pos hp 2)).2 (by
    convert hn using 1; ring)
  rw [encode, ZMod.val_natCast_of_lt h₂,
    ZMod.val_natCast_of_lt (Nat.mod_lt _ hp),
    ZMod.val_natCast_of_lt (Nat.mod_lt _ hp)]
  have hdiv : n / p ^ 2 = n / p / p := by rw [Nat.div_div_eq_div_mul, pow_two]
  calc
    n / p ^ 2 * p ^ 2 + n / p % p * p + n % p =
        (n / p / p * p + n / p % p) * p + n % p := by rw [hdiv]; ring
    _ = n := by
      rw [Nat.mul_comm (n / p / p) p, Nat.div_add_mod, Nat.mul_comm (n / p) p,
        Nat.div_add_mod]

/-- The outer-pair lexicographic order respects the base-`p` encoding. -/
theorem encode_lt_of_toLex_lt (p : ℕ) [Fact p.Prime] (a b c d e f : ZMod p)
    (h : toLex (a.val, b.val, c.val) < toLex (d.val, e.val, f.val)) :
    encode p a b c < encode p d e f := by
  have hp := (Fact.out : p.Prime).pos
  have hb := ZMod.val_lt b
  have hc := ZMod.val_lt c
  have htail : b.val * p + c.val < p ^ 2 := by
    have hmul := Nat.mul_le_mul_right p (Nat.succ_le_of_lt hb)
    nlinarith
  rcases Prod.Lex.toLex_lt_toLex.mp h with had | ⟨had, htail'⟩
  · have hmul := Nat.mul_le_mul_right (p ^ 2) (Nat.succ_le_of_lt had)
    dsimp only [encode]
    nlinarith
  · change a.val = d.val at had
    rcases Prod.lt_iff.mp htail' with ⟨hbe, hcf⟩ | ⟨hbe, hcf⟩
    · change b.val < e.val at hbe
      change c.val ≤ f.val at hcf
      have hmul := Nat.mul_lt_mul_of_pos_right hbe hp
      dsimp only [encode]
      rw [had]
      omega
    · change b.val ≤ e.val at hbe
      change c.val < f.val at hcf
      have hmul := Nat.mul_le_mul_right p hbe
      dsimp only [encode]
      rw [had]
      omega

/-- Full lexicographic comparison of the three digits implies comparison of their encodings. -/
theorem encode_lt_of_lex_lt (p : ℕ) [Fact p.Prime] (a b c d e f : ZMod p)
    (h : a.val < d.val ∨ a.val = d.val ∧
      (b.val < e.val ∨ b.val = e.val ∧ c.val < f.val)) :
    encode p a b c < encode p d e f := by
  have hp := (Fact.out : p.Prime).pos
  have hb := ZMod.val_lt b
  have hc := ZMod.val_lt c
  have htail : b.val * p + c.val < p ^ 2 := by
    have hmul := Nat.mul_le_mul_right p (Nat.succ_le_of_lt hb)
    nlinarith
  rcases h with had | ⟨had, hbe | ⟨hbe, hcf⟩⟩
  · have hmul := Nat.mul_le_mul_right (p ^ 2) (Nat.succ_le_of_lt had)
    dsimp only [encode]
    nlinarith
  · have hmul := Nat.mul_le_mul_right p (Nat.succ_le_of_lt hbe)
    dsimp only [encode]
    rw [had]
    nlinarith
  · dsimp only [encode]
    rw [had, hbe]
    omega

/-- The search defining `firstIrreducibleCubic` returns the least index with an
irreducible cubic. -/
theorem search_spec (p : ℕ) [Fact p.Prime] :
    ∃ n < p ^ 3, firstIrreducibleCubic p = cubic p n ∧ Irreducible (cubic p n) ∧
      ∀ m < n, ¬ Irreducible (cubic p m) := by
  classical
  have hex := exists_irreducible_index p
  let n := Nat.find hex
  have hn : n < p ^ 3 := (Nat.find_spec hex).1
  have hi : Irreducible (cubic p n) := (Nat.find_spec hex).2
  have hmin : ∀ m < n, ¬ Irreducible (cubic p m) := by
    intro m hm hmi
    exact Nat.find_min hex hm ⟨hm.trans hn, hmi⟩
  have hfind : (List.range (p ^ 3)).find? (fun m => decide (Irreducible (cubic p m))) =
      some n := by
    apply List.find?_range_eq_some.mpr
    simpa only [decide_eq_true_eq, List.mem_range, Bool.not_eq_true', decide_eq_false_iff_not]
      using And.intro hi (And.intro hn hmin)
  refine ⟨n, hn, ?_, hi, hmin⟩
  change (match (List.range (p ^ 3)).find? (fun m => decide (Irreducible (cubic p m))) with
    | some m => cubic p m
    | none => X ^ 3) = cubic p n
  rw [hfind]

end

end ExplicitRIP.CubicSelection

end
