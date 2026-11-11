/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Jets.Defs

/-!
# Finite jet indices

The finite jet index represents exactly the exponent vectors whose total degree is at most `r`.
-/

public section

namespace ExplicitRIP.GuthZahl

namespace Hasse

@[simp] theorem jetExponent_apply {r : ℕ} (a : JetIndex r) (i : Fin 3) :
    jetExponent a i = (a.val i).val := rfl

theorem jetExponent_injective (r : ℕ) : Function.Injective (jetExponent (r := r)) := by
  intro a b h
  apply Subtype.ext
  funext i
  apply Fin.ext
  exact congrArg (fun d : Fin 3 →₀ ℕ => d i) h

theorem exists_jetExponent_eq {r : ℕ} (a : Fin 3 →₀ ℕ)
    (ha : (∑ i : Fin 3, a i) ≤ r) : ∃ b : JetIndex r, jetExponent b = a := by
  classical
  have hi (i : Fin 3) : a i < r + 1 :=
    Nat.lt_succ_of_le
      ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans ha)
  refine ⟨⟨fun i => ⟨a i, hi i⟩, ha⟩, ?_⟩
  ext i
  rfl

end Hasse

end ExplicitRIP.GuthZahl

end
