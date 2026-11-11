/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.HermitianForms.Defs.HermitianGraph

/-!
# Host parameter asymptotics

The degree and frame-parameter formulas of [KM, Section 3, (13)] imply that the adjacent and
nonadjacent magnitudes are asymptotic to `1/p` and `1/p²`, respectively, and the edge density is
asymptotic to `1/p`. These formulas hold in the Hermitian-forms model of the host graph. The
edge density is exactly `1 / (p + 1)`.
-/

public section

open scoped BigOperators

namespace ExplicitRIP.HostFrame

open Classical in
theorem edge_density_of_isSRGWith (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]
    (hSRG : (hermitianGraph p).IsSRGWith (p ^ 4) ((p - 1) * (p ^ 2 + 1)) (p - 2)
      (p * (p - 1))) :
    ((hermitianGraph p).edgeSet.ncard : ℝ) / ((p ^ 4).choose 2 : ℕ) =
      1 / ((p : ℝ) + 1) := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp1 : 1 ≤ p := le_trans (by decide) hp2
  have hp : (1 : ℝ) < p := by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hp2)
  have hsum := (hermitianGraph p).sum_degrees_eq_twice_card_edges
  simp only [hSRG.regular.degree_eq, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, hSRG.card] at hsum
  have hedges : 2 * ((hermitianGraph p).edgeSet.ncard : ℝ) =
      (p : ℝ) ^ 4 * (((p : ℝ) - 1) * ((p : ℝ) ^ 2 + 1)) := by
    have hn : (hermitianGraph p).edgeSet.ncard = (hermitianGraph p).edgeFinset.card := by
      simp only [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card']
    rw [hn]
    have hcast := congrArg (fun n : ℕ => (n : ℝ)) hsum.symm
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hp1, Nat.cast_add,
      Nat.cast_one, Nat.cast_two] using hcast
  have hcount : ((hermitianGraph p).edgeSet.ncard : ℝ) =
      (p : ℝ) ^ 4 * (((p : ℝ) - 1) * ((p : ℝ) ^ 2 + 1)) / 2 := by
    linarith only [hedges]
  rw [hcount, Nat.cast_choose_two]
  push_cast
  have hpn : (p : ℝ) ≠ 0 := by linarith
  have hq : (p : ℝ) ^ 4 - 1 ≠ 0 := by nlinarith [sq_nonneg ((p : ℝ) ^ 2 - 1)]
  have hplus : (p : ℝ) + 1 ≠ 0 := by linarith
  field_simp
  ring

theorem parameter_error_bounds (x : ℝ) (hx : 2 ≤ x) :
    |x * ((x ^ 2 - x + 1) / ((x - 1) * (x ^ 2 + 1))) - 1| ≤ 1 / x ∧
    |x ^ 2 * (1 / (x ^ 2 + 1)) - 1| ≤ 1 / x ∧
    |x * (1 / (x + 1)) - 1| ≤ 1 / x := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have hq : 0 < x ^ 2 + 1 := by positivity
  have hm : 0 < (x - 1) * (x ^ 2 + 1) := mul_pos hx1 hq
  have hmge : x ≤ (x - 1) * (x ^ 2 + 1) := by
    nlinarith [mul_nonneg (show 0 ≤ x - 2 by linarith) (sq_nonneg x)]
  have hqge : x ≤ x ^ 2 + 1 := by nlinarith [sq_nonneg (x - 1)]
  have ha : x * ((x ^ 2 - x + 1) / ((x - 1) * (x ^ 2 + 1))) - 1 =
      1 / ((x - 1) * (x ^ 2 + 1)) := by field_simp; ring
  have hb : x ^ 2 * (1 / (x ^ 2 + 1)) - 1 = -(1 / (x ^ 2 + 1)) := by
    field_simp; ring
  have hd : x * (1 / (x + 1)) - 1 = -(1 / (x + 1)) := by
    field_simp; ring
  rw [ha, hb, hd, abs_of_nonneg (le_of_lt (one_div_pos.mpr hm)), abs_neg,
    abs_of_nonneg (le_of_lt (one_div_pos.mpr hq)), abs_neg,
    abs_of_nonneg (by positivity : 0 ≤ 1 / (x + 1))]
  exact ⟨one_div_le_one_div_of_le hx0 hmge, one_div_le_one_div_of_le hx0 hqge,
    one_div_le_one_div_of_le hx0 (by linarith)⟩

end ExplicitRIP.HostFrame
