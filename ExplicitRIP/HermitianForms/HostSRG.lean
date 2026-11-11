/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.HermitianForms.HostSRG.Degree
public import ExplicitRIP.HermitianForms.HostSRG.Common

/-!
# Strong regularity of the Hermitian forms graph

The Hermitian-forms model of `VO₄⁻(p)` has the strongly regular parameters of [KM, Section 3].
The determinant and counting proofs below use only the Hermitian-coordinate definitions
`ExplicitRIP.hermitianMatrix` and `ExplicitRIP.hermitianGraph` and Mathlib. The sphere map
transports the result to the contact graph of [KM, Section 4.1].
-/

public section

theorem ExplicitRIP.HostFrame.isSRGWith (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)] :
    (open Classical in
      (ExplicitRIP.hermitianGraph p).IsSRGWith (p ^ 4) ((p - 1) * (p ^ 2 + 1)) (p - 2)
        (p * (p - 1))) := by
  classical
  refine ⟨?_, ExplicitRIP.Hfsrg.regular p, ?_, ?_⟩
  · simp only [Fintype.card_prod, ZMod.card]
    ring
  · intro x y hxy
    rw [Fintype.card_eq_nat_card]
    exact ExplicitRIP.Hfsrg.card_common_of_adj p x y hxy
  · intro x y hne hxy
    rw [Fintype.card_eq_nat_card]
    exact ExplicitRIP.Hfsrg.card_common_of_not_adj p x y hne hxy
