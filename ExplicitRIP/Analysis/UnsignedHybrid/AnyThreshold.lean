/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Analysis.UnsignedHybrid.Gram
public import ExplicitRIP.Analysis.UnsignedHybrid.Threshold

/-!
# Unsigned Gershgorin comparison

A matrix with symmetric entry moduli satisfies the column-sum bound after taking
entrywise moduli. The threshold estimate imported here already permits every real threshold.
-/

public section

namespace ExplicitRIP.UnsignedHybrid

/-- Symmetric entry moduli give the unsigned Gershgorin estimate over either scalar field. -/
theorem opNorm_map_norm_le_oneToOneNorm {𝕜 : Type*} [RCLike 𝕜]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι 𝕜)
    (hsym : ∀ i j, ‖M i j‖ = ‖M j i‖) :
    opNorm (M.map fun z => ‖z‖) ≤ oneToOneNorm M := by
  calc
    opNorm (M.map fun z => ‖z‖) ≤
        opNorm ((M.map fun z => ‖z‖).map Complex.ofReal) :=
      opNorm_real_le_opNorm_complex _
    _ ≤ oneToOneNorm ((M.map fun z => ‖z‖).map Complex.ofReal) :=
      Gersh.opNorm_le_oneToOneNorm_of_isHermitian
        (isHermitian_map_ofReal_of_symm _ hsym)
    _ = oneToOneNorm M := oneToOneNorm_map_norm_ofReal M

end ExplicitRIP.UnsignedHybrid
