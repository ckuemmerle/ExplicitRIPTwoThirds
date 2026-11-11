# Paper ↔ Lean map

This table lists, for every statement and definition of [KM] that the formalization covers, the Lean declaration that
states it. Each declaration is in its own file under `ExplicitRIP/Frozen/` (definitions under
`ExplicitRIP/Frozen/Defs/`). Every theorem below is proved, and the proofs use only the axioms `propext`,
`Classical.choice` and `Quot.sound` (run `scripts/PrintAxioms.lean` to check).

- [KM] C. Kümmerle and D. G. Mixon, *Explicit restricted isometries with k = m^{2/3-o(1)}*,
  [arXiv:2611.14475](https://arxiv.org/abs/2611.14475).
- [Z] J. Zahl, *Sphere tangencies, line incidences, and Lie's line-sphere correspondence*, Math. Proc. Cambridge
  Philos. Soc. 172 (2022), no. 2, 401–421, [arXiv:2002.11677](https://arxiv.org/abs/2002.11677).


## Numbered results

| [KM] | Lean declaration | File |
|---|---|---|
| Theorem 1 | `ExplicitRIP.main_theorem` | [MainTheorem.lean](ExplicitRIP/Frozen/MainTheorem.lean) |
| Lemma 2 | `ExplicitRIP.flat_rip_dr` | [FlatRIPDR.lean](ExplicitRIP/Frozen/FlatRIPDR.lean) |
| Lemma 3 | `ExplicitRIP.subgraph_density_dr_bound` | [SubgraphDensityDR.lean](ExplicitRIP/Frozen/SubgraphDensityDR.lean) |
| Theorem 4 | `ExplicitRIP.unsigned_barrier` | [UnsignedBarrier.lean](ExplicitRIP/Frozen/UnsignedBarrier.lean) |
| Lemma 5 | `ExplicitRIP.srg_scaling` | [SrgScaling.lean](ExplicitRIP/Frozen/SrgScaling.lean) |
| Theorem 6 (the case of [Z, Theorem 1.8] used in [KM]) | `ExplicitRIP.zahl_sphere_contacts` | [ZahlSphereContacts.lean](ExplicitRIP/Frozen/ZahlSphereContacts.lean) |
| Lemma 7 | `ExplicitRIP.line_conic_avoidance` | [LineConicAvoidance.lean](ExplicitRIP/Frozen/LineConicAvoidance.lean) |
| Proposition 8 | `ExplicitRIP.hereditary_density` | [HereditaryDensity.lean](ExplicitRIP/Frozen/HereditaryDensity.lean) |
| Proposition 10 | `ExplicitRIP.construction_barrier` | [ConstructionBarrier.lean](ExplicitRIP/Frozen/ConstructionBarrier.lean) |
| Proposition 10 for the matrices of Theorem 1 ([KM, abstract and Section 5]) | `ExplicitRIP.construction_barrier_host` | [ConstructionBarrierHost.lean](ExplicitRIP/Frozen/ConstructionBarrierHost.lean) |

Problem 9 of [KM] is an open problem and is not formalized.

## Further statements used by the numbered results

Unnumbered statements of the text, in order of appearance.

| Statement | Place in [KM] | Lean declaration | File |
|---|---|---|---|
| The two definitions of `δ_k` agree | Section 1, definition of δ_k | `ExplicitRIP.ripConstant_isLeast` | [RIPConstantCharacterization.lean](ExplicitRIP/Frozen/RIPConstantCharacterization.lean) |
| The coherence bound `δ_k ≤ (k - 1)μ` | (2) | `ExplicitRIP.ripConstant_le_coherence` | [CoherenceBound.lean](ExplicitRIP/Frozen/CoherenceBound.lean) |
| The Welch bound | (3) | `ExplicitRIP.welch_bound` | [WelchBound.lean](ExplicitRIP/Frozen/WelchBound.lean) |
| The flat-RIP constant is the smallest admissible θ | (4) and Lemma 2 | `ExplicitRIP.flatConstant_isLeast` | [FlatConstantCharacterization.lean](ExplicitRIP/Frozen/FlatConstantCharacterization.lean) |
| The Gershgorin estimate as a matrix-norm bound | Section 2.1 | `ExplicitRIP.gershgorin_bound` | [GershgorinBound.lean](ExplicitRIP/Frozen/GershgorinBound.lean) |
| The spectral norm is controlled by the discrete Rayleigh norm (Lev) | (5) | `ExplicitRIP.lev_dr_bound` | [LevDRBound.lean](ExplicitRIP/Frozen/LevDRBound.lean) |
| `δ_1 = 0` and `δ_2 = μ` for unit vectors | Section 2.2 | `ExplicitRIP.ripConstant_one_two` | [RIPConstantOneTwo.lean](ExplicitRIP/Frozen/RIPConstantOneTwo.lean) |
| The split of a Gram submatrix into large and small entries | (6) | `ExplicitRIP.hybrid_split_estimate` | [HybridSplitEstimate.lean](ExplicitRIP/Frozen/HybridSplitEstimate.lean) |
| Large Gram entries and the discrete Rayleigh norm | (6)–(8) | `ExplicitRIP.large_entries_dr_bound` | [LargeEntriesDR.lean](ExplicitRIP/Frozen/LargeEntriesDR.lean) |
| The unsigned hybrid estimate | (6)–(8) and Section 2.3 | `ExplicitRIP.unsigned_hybrid_estimate` | [UnsignedHybridEstimate.lean](ExplicitRIP/Frozen/UnsignedHybridEstimate.lean) |
| Entrywise absolute values and the discrete Rayleigh norm | (7) | `ExplicitRIP.drNorm_le_drNorm_abs` | [AbsoluteRayleigh.lean](ExplicitRIP/Frozen/AbsoluteRayleigh.lean) |
| Restricted isometry from hereditary density | (9) | `ExplicitRIP.rip_density_bound` | [RIPDensityBound.lean](ExplicitRIP/Frozen/RIPDensityBound.lean) |
| Entrywise absolute values do not decrease the spectral norm | Section 2.3 | `ExplicitRIP.opNorm_le_opNorm_abs` | [OpNormAbs.lean](ExplicitRIP/Frozen/OpNormAbs.lean) |
| The frame potential bound | (11), in the proof of Theorem 4 | `ExplicitRIP.frame_potential_bound` | [FramePotential.lean](ExplicitRIP/Frozen/FramePotential.lean) |
| The host frame and its parameters | Section 3, (13); proof of Theorem 1, footnote 4 | `ExplicitRIP.host_frame_params` | [HostFrameParams.lean](ExplicitRIP/Frozen/HostFrameParams.lean) |
| The parameters of the strongly regular graph `VO₄⁻(p)` | Section 3 | `ExplicitRIP.host_parameters` | [HostParameters.lean](ExplicitRIP/Frozen/HostParameters.lean) |
| The first monic irreducible cubic: specification | Section 4.2, footnote 3 | `ExplicitRIP.firstIrreducibleCubic_spec` | [FirstIrreducibleCubicSpec.lean](ExplicitRIP/Frozen/FirstIrreducibleCubicSpec.lean) |
| The field norm on lines: the coefficient of `s³` in `N(c + s v)` is `N(v)` | Section 4.2 and footnote 3 | `ExplicitRIP.fieldNorm_spec` | [FieldNormSpec.lean](ExplicitRIP/Frozen/FieldNormSpec.lean) |
| The bound (16) on `δ_k(Φ_T)` | (16), in the proof of Theorem 1; footnotes 4 and 5 | `ExplicitRIP.final_rip` | [FinalRIP.lean](ExplicitRIP/Frozen/FinalRIP.lean) |
| Exact `LDLᵀ` elimination factors a positive semidefinite matrix | proof of Theorem 1, footnote 4 | `ExplicitRIP.ldl_factorization` | [LDLFactorization.lean](ExplicitRIP/Frozen/LDLFactorization.lean) |

## Definitions

| Definition | Place in [KM] | Lean declaration | File |
|---|---|---|---|
| The spectral norm `‖M‖_op` | Sections 1 and 2.1 | `ExplicitRIP.opNorm` | [OpNorm.lean](ExplicitRIP/Frozen/Defs/OpNorm.lean) |
| The restricted isometry constant `δ_k` | Section 1 | `ExplicitRIP.ripConstant` | [RIPConstant.lean](ExplicitRIP/Frozen/Defs/RIPConstant.lean) |
| The coherence `μ` | Section 1 | `ExplicitRIP.coherence` | [Coherence.lean](ExplicitRIP/Frozen/Defs/Coherence.lean) |
| The flat-RIP constant `θ_k(Φ)` | (4) and Lemma 2 | `ExplicitRIP.flatConstant` | [FlatConstant.lean](ExplicitRIP/Frozen/Defs/FlatConstant.lean) |
| The induced `1`-norm `‖M‖_{1→1}` | Section 2.1 | `ExplicitRIP.oneToOneNorm` | [OneToOneNorm.lean](ExplicitRIP/Frozen/Defs/OneToOneNorm.lean) |
| The discrete Rayleigh norm `‖M‖_DR` | Section 2.1 | `ExplicitRIP.drNorm` | [DRNorm.lean](ExplicitRIP/Frozen/Defs/DRNorm.lean) |
| The constant `ρ_k(Φ)` | Lemma 2 | `ExplicitRIP.rhoConstant` | [RhoConstant.lean](ExplicitRIP/Frozen/Defs/RhoConstant.lean) |
| The induced edge count `e(U)` | Lemma 3 | `ExplicitRIP.inducedEdgeCount` | [InducedEdgeCount.lean](ExplicitRIP/Frozen/Defs/InducedEdgeCount.lean) |
| The unsigned constant `Δ_k` | Section 2.3 | `ExplicitRIP.unsignedRIPConstant` | [UnsignedRIPConstant.lean](ExplicitRIP/Frozen/Defs/UnsignedRIPConstant.lean) |
| Two-distance tight frames | Section 3; Proposition 10 | `ExplicitRIP.IsTwoDistanceTightFrame` | [IsTwoDistanceTightFrame.lean](ExplicitRIP/Frozen/Defs/IsTwoDistanceTightFrame.lean) |
| The Gram matrix `G` of the proof of Theorem 1 | Section 3, (13); proof of Theorem 1 | `ExplicitRIP.hostGram` | [HostGram.lean](ExplicitRIP/Frozen/Defs/HostGram.lean) |
| The elliptic affine polar graph `VO₄⁻(p)` | Sections 3 and 4.1 | `ExplicitRIP.contactGraph` | [ContactGraph.lean](ExplicitRIP/Frozen/Defs/ContactGraph.lean) |
| Contact of oriented spheres | Section 4.1, footnote 1; [Z, (1.1)] | `ExplicitRIP.SphereContact` | [SphereContact.lean](ExplicitRIP/Frozen/Defs/SphereContact.lean) |
| Pencils of contacting spheres | Section 4.1; [Z, Definition 1.2] | `ExplicitRIP.IsContactPencil` | [IsContactPencil.lean](ExplicitRIP/Frozen/Defs/IsContactPencil.lean) |
| Pairs of complementary conic sections | Section 4.1; [Z, Definition 1.6] | `ExplicitRIP.IsComplementaryConicPair` | [IsComplementaryConicPair.lean](ExplicitRIP/Frozen/Defs/IsComplementaryConicPair.lean) |
| The number of `h`-rich pencils | Theorem 6(a) | `ExplicitRIP.richPencilCount` | [RichPencilCount.lean](ExplicitRIP/Frozen/Defs/RichPencilCount.lean) |
| The selected vertex set `V'_T` | (15) | `ExplicitRIP.selectedVertices` | [SelectedVertices.lean](ExplicitRIP/Frozen/Defs/SelectedVertices.lean) |
| The first monic irreducible cubic in lexicographic order | footnote 3 | `ExplicitRIP.firstIrreducibleCubic` | [FirstIrreducibleCubic.lean](ExplicitRIP/Frozen/Defs/FirstIrreducibleCubic.lean) |
| The field norm `N : 𝔽_p³ → 𝔽_p` | Section 4.2, footnote 3 | `ExplicitRIP.fieldNorm` | [FieldNorm.lean](ExplicitRIP/Frozen/Defs/FieldNorm.lean) |
| The explicit realization `Φ_T` of the proof of Theorem 1 | proof of Theorem 1, footnotes 4 and 5 | `ExplicitRIP.choleskyMatrix` | [CholeskyMatrix.lean](ExplicitRIP/Frozen/Defs/CholeskyMatrix.lean) |
| The rational Gram matrix in lexicographic vertex order | footnote 4 | `ExplicitRIP.lexGram` | [LexGram.lean](ExplicitRIP/Frozen/Defs/LexGram.lean) |
| The lexicographic order on `𝔽_p⁴` | footnote 4 | `ExplicitRIP.lexEquiv` | [LexEquiv.lean](ExplicitRIP/Frozen/Defs/LexEquiv.lean) |
| Exact `LDLᵀ` elimination: residual matrices | footnote 4 | `ExplicitRIP.ldlResidual` | [LDLResidual.lean](ExplicitRIP/Frozen/Defs/LDLResidual.lean) |
| Exact `LDLᵀ` elimination: the nonzero pivots | footnote 4 | `ExplicitRIP.ldlPivots` | [LDLPivots.lean](ExplicitRIP/Frozen/Defs/LDLPivots.lean) |
| Exact `LDLᵀ` elimination: the real factor `B` | footnote 4 | `ExplicitRIP.ldlFactor` | [LDLFactor.lean](ExplicitRIP/Frozen/Defs/LDLFactor.lean) |
