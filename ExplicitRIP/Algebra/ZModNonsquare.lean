/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib

/-!
# `-1` is not a square modulo a prime `p ≡ 3 (mod 4)`

The fact and the instance `Fact (¬ IsSquare (-1 : ZMod p))` that Zahl's argument and the
construction in Hermitian coordinates use. -/

public section

namespace ExplicitRIP

/-- For a prime `p ≡ 3 (mod 4)`, `-1` is not a square in `ZMod p`. -/
theorem zmod_neg_one_not_isSquare (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)] :
    ¬ IsSquare (-1 : ZMod p) :=
  fun h => (ZMod.exists_sq_eq_neg_one_iff.mp h) (Fact.out : p % 4 = 3)

instance fact_not_isSquare_neg_one (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)] :
    Fact (¬ IsSquare (-1 : ZMod p)) :=
  ⟨zmod_neg_one_not_isSquare p⟩

end ExplicitRIP
