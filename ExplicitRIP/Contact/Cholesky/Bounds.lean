/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Frozen.Defs.HostGram
public import ExplicitRIP.Analysis.ConstructionBarrier.Parameters

/-!
# Scalar coefficient bounds for the quantitative RIP estimate

The two coefficients in the host Gram formula are bounded by `2/p` and `1/p²`. These estimates
give the final absorption of constants in [KM, (16)], using the parameters [KM, (13)].
-/

public section

namespace ExplicitRIP.Contact.Cholesky

/-- Both host Gram coefficients are nonnegative. -/
theorem gram_coeff_nonneg (p : ℕ) [Fact p.Prime] :
    0 ≤ Actbar.largeEntry p ∧ 0 ≤ Actbar.smallEntry p := by
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  constructor
  · apply div_nonneg
    · nlinarith only [sq_nonneg ((p : ℝ) - 1)]
    · exact mul_nonneg (by linarith only [hp]) (by positivity)
  · exact div_nonneg zero_le_one (by positivity)

/-- Uniform bounds for the two host Gram coefficients. -/
theorem gram_coeff_bounds (p : ℕ) [Fact p.Prime] :
    Actbar.largeEntry p ≤ 2 / (p : ℝ) ∧ Actbar.smallEntry p ≤ 1 / (p : ℝ) ^ 2 := by
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  have hp0 : (0 : ℝ) < p := by linarith only [hp]
  have hm : 0 < ((p : ℝ) - 1) * ((p : ℝ) ^ 2 + 1) :=
    mul_pos (by linarith only [hp]) (by positivity)
  constructor
  · unfold Actbar.largeEntry
    apply (div_le_div_iff₀ hm hp0).mpr
    have hprod : 0 ≤ (p : ℝ) ^ 2 * ((p : ℝ) - 1) :=
      mul_nonneg (sq_nonneg _) (by linarith only [hp])
    nlinarith only [hprod, hp]
  · exact one_div_le_one_div_of_le (pow_pos hp0 2) (by linarith)

/-- Absorb the two coefficients and the density constant into one absolute constant. -/
theorem combine_unsigned_bounds (p : ℕ) [Fact p.Prime] (K X Y : ℝ)
    (hK : 0 ≤ K) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    Actbar.largeEntry p * (K * X) + Actbar.smallEntry p * Y ≤
      (2 * K + 1) * (X / p + Y / (p : ℝ) ^ 2) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  calc
    Actbar.largeEntry p * (K * X) + Actbar.smallEntry p * Y ≤
        (2 / p) * (K * X) + (1 / (p : ℝ) ^ 2) * Y :=
      add_le_add (mul_le_mul_of_nonneg_right (gram_coeff_bounds p).1 (mul_nonneg hK hX))
        (mul_le_mul_of_nonneg_right (gram_coeff_bounds p).2 hY)
    _ = 2 * K * (X / p) + Y / (p : ℝ) ^ 2 := by ring
    _ ≤ (2 * K + 1) * (X / p + Y / (p : ℝ) ^ 2) := by
      have hXP : 0 ≤ X / p := div_nonneg hX hp.le
      have hYP : 0 ≤ Y / (p : ℝ) ^ 2 := div_nonneg hY (sq_nonneg _)
      nlinarith only [hXP, hYP, mul_nonneg hK hYP]

end ExplicitRIP.Contact.Cholesky
