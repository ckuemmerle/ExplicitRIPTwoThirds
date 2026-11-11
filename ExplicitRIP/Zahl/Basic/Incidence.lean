/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Zahl.Defs

/-!
# Exact enumeration of fixed-size samples

The number of `m`-element subsets of a finite set that contain a fixed subset.
-/

public section

namespace ExplicitRIP.Zahl

/-- Exact enumeration of fixed-size subsets containing a fixed witness. -/
theorem powersetCard_containing_count {α : Type*} [DecidableEq α]
    (S T : Finset α) (m : ℕ) (hTS : T ⊆ S) (hTm : T.card ≤ m) :
    ((S.powersetCard m).filter (fun U => T ⊆ U)).card =
      Nat.choose (S.card - T.card) (m - T.card) := by
  exact Finset.card_filter_powersetCard_subset T S m hTS hTm

end ExplicitRIP.Zahl
