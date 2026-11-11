/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

import ExplicitRIP.Frozen.AbsoluteRayleigh
import ExplicitRIP.Frozen.CoherenceBound
import ExplicitRIP.Frozen.ConstructionBarrier
import ExplicitRIP.Frozen.ConstructionBarrierHost
import ExplicitRIP.Frozen.Defs.CholeskyMatrix
import ExplicitRIP.Frozen.Defs.Coherence
import ExplicitRIP.Frozen.Defs.ContactGraph
import ExplicitRIP.Frozen.Defs.DRNorm
import ExplicitRIP.Frozen.Defs.FieldNorm
import ExplicitRIP.Frozen.Defs.FirstIrreducibleCubic
import ExplicitRIP.Frozen.Defs.FlatConstant
import ExplicitRIP.Frozen.Defs.HostGram
import ExplicitRIP.Frozen.Defs.InducedEdgeCount
import ExplicitRIP.Frozen.Defs.IsComplementaryConicPair
import ExplicitRIP.Frozen.Defs.IsContactPencil
import ExplicitRIP.Frozen.Defs.IsTwoDistanceTightFrame
import ExplicitRIP.Frozen.Defs.LDLFactor
import ExplicitRIP.Frozen.Defs.LDLPivots
import ExplicitRIP.Frozen.Defs.LDLResidual
import ExplicitRIP.Frozen.Defs.LexEquiv
import ExplicitRIP.Frozen.Defs.LexGram
import ExplicitRIP.Frozen.Defs.OneToOneNorm
import ExplicitRIP.Frozen.Defs.OpNorm
import ExplicitRIP.Frozen.Defs.RIPConstant
import ExplicitRIP.Frozen.Defs.RhoConstant
import ExplicitRIP.Frozen.Defs.RichPencilCount
import ExplicitRIP.Frozen.Defs.SelectedVertices
import ExplicitRIP.Frozen.Defs.SphereContact
import ExplicitRIP.Frozen.Defs.UnsignedRIPConstant
import ExplicitRIP.Frozen.FieldNormSpec
import ExplicitRIP.Frozen.FinalRIP
import ExplicitRIP.Frozen.FirstIrreducibleCubicSpec
import ExplicitRIP.Frozen.FlatConstantCharacterization
import ExplicitRIP.Frozen.FlatRIPDR
import ExplicitRIP.Frozen.FramePotential
import ExplicitRIP.Frozen.GershgorinBound
import ExplicitRIP.Frozen.HereditaryDensity
import ExplicitRIP.Frozen.HostFrameParams
import ExplicitRIP.Frozen.HostParameters
import ExplicitRIP.Frozen.HybridSplitEstimate
import ExplicitRIP.Frozen.LDLFactorization
import ExplicitRIP.Frozen.LargeEntriesDR
import ExplicitRIP.Frozen.LevDRBound
import ExplicitRIP.Frozen.LineConicAvoidance
import ExplicitRIP.Frozen.MainTheorem
import ExplicitRIP.Frozen.OpNormAbs
import ExplicitRIP.Frozen.RIPConstantCharacterization
import ExplicitRIP.Frozen.RIPConstantOneTwo
import ExplicitRIP.Frozen.RIPDensityBound
import ExplicitRIP.Frozen.SrgScaling
import ExplicitRIP.Frozen.SubgraphDensityDR
import ExplicitRIP.Frozen.UnsignedBarrier
import ExplicitRIP.Frozen.UnsignedHybridEstimate
import ExplicitRIP.Frozen.WelchBound
import ExplicitRIP.Frozen.ZahlSphereContacts
import Solution

/-!
# Axiom check

Prints the axioms used by each of the 55 frozen declarations (30 theorems and 25 definitions in
`ExplicitRIP/Frozen/`) and by the 4 theorems of the statement package (`Solution.lean`). Expected
output: only `propext`, `Classical.choice` and `Quot.sound`, or no axioms at all. Run from the
repository root, after `lake build`, with

    lake env lean scripts/PrintAxioms.lean

This file is not part of the `ExplicitRIP` library.
-/

#print axioms ExplicitRIP.ripConstant_isLeast
#print axioms ExplicitRIP.ripConstant_le_coherence
#print axioms ExplicitRIP.gershgorin_bound
#print axioms ExplicitRIP.lev_dr_bound
#print axioms ExplicitRIP.flat_rip_dr
#print axioms ExplicitRIP.flatConstant_isLeast
#print axioms ExplicitRIP.ripConstant_one_two
#print axioms ExplicitRIP.hybrid_split_estimate
#print axioms ExplicitRIP.drNorm_le_drNorm_abs
#print axioms ExplicitRIP.large_entries_dr_bound
#print axioms ExplicitRIP.subgraph_density_dr_bound
#print axioms ExplicitRIP.rip_density_bound
#print axioms ExplicitRIP.frame_potential_bound
#print axioms ExplicitRIP.firstIrreducibleCubic_spec
#print axioms ExplicitRIP.ldl_factorization
#print axioms ExplicitRIP.unsigned_hybrid_estimate
#print axioms ExplicitRIP.unsigned_barrier
#print axioms ExplicitRIP.opNorm_le_opNorm_abs
#print axioms ExplicitRIP.welch_bound
#print axioms ExplicitRIP.zahl_sphere_contacts
#print axioms ExplicitRIP.fieldNorm_spec
#print axioms ExplicitRIP.host_parameters
#print axioms ExplicitRIP.host_frame_params
#print axioms ExplicitRIP.srg_scaling
#print axioms ExplicitRIP.line_conic_avoidance
#print axioms ExplicitRIP.hereditary_density
#print axioms ExplicitRIP.final_rip
#print axioms ExplicitRIP.main_theorem
#print axioms ExplicitRIP.construction_barrier
#print axioms ExplicitRIP.construction_barrier_host
#print axioms ExplicitRIP.opNorm
#print axioms ExplicitRIP.ripConstant
#print axioms ExplicitRIP.coherence
#print axioms ExplicitRIP.flatConstant
#print axioms ExplicitRIP.oneToOneNorm
#print axioms ExplicitRIP.drNorm
#print axioms ExplicitRIP.rhoConstant
#print axioms ExplicitRIP.inducedEdgeCount
#print axioms ExplicitRIP.unsignedRIPConstant
#print axioms ExplicitRIP.IsTwoDistanceTightFrame
#print axioms ExplicitRIP.hostGram
#print axioms ExplicitRIP.contactGraph
#print axioms ExplicitRIP.SphereContact
#print axioms ExplicitRIP.IsContactPencil
#print axioms ExplicitRIP.IsComplementaryConicPair
#print axioms ExplicitRIP.richPencilCount
#print axioms ExplicitRIP.selectedVertices
#print axioms ExplicitRIP.firstIrreducibleCubic
#print axioms ExplicitRIP.fieldNorm
#print axioms ExplicitRIP.choleskyMatrix
#print axioms ExplicitRIP.lexGram
#print axioms ExplicitRIP.lexEquiv
#print axioms ExplicitRIP.ldlResidual
#print axioms ExplicitRIP.ldlPivots
#print axioms ExplicitRIP.ldlFactor

-- The theorems compared by Comparator (`comparator.json`).
#print axioms KM.main_theorem
#print axioms KM.unsigned_barrier
#print axioms KM.construction_barrier
#print axioms KM.construction_barrier_host
