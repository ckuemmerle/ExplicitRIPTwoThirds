/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib

/-!
# Guth–Zahl line route: definitions for the sampling branch

The weight of a subset in independent Bernoulli sampling is the product of its
inclusion and exclusion probabilities.

* `bernoulliWeight`
-/

@[expose] public section

namespace ExplicitRIP.GuthZahl

open Classical in
noncomputable def bernoulliWeight {α : Type*} (q : ℝ) (S T : Finset α) : ℝ :=
  q ^ T.card * (1 - q) ^ (S.card - T.card)

end ExplicitRIP.GuthZahl

end
