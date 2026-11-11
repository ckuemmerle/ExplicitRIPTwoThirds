# Explicit restricted isometries with k = m^{2/3−o(1)}: a Lean formalization

This repository contains a complete Lean 4 / Mathlib formalization of the paper

> C. Kümmerle and D. G. Mixon, *Explicit restricted isometries with k = m^{2/3−o(1)}*,
> [arXiv:2611.14475](https://arxiv.org/abs/2611.14475),

cited below as [KM].

The restricted isometry constant δ_k of a matrix measures how well it preserves the lengths of vectors with at most k
nonzero entries; explicit matrices with small δ_k are sought as deterministic measurement matrices for compressed
sensing. [KM] constructs explicit real m × n matrices with m → ∞, m/n → 0 and δ_k → 0 for k = m^{2/3−o(1)}, beyond the
square-root barrier of coherence arguments, by an argument that uses only the entrywise absolute values of the Gram
matrix. It also shows that 2/3 is a barrier both for such arguments (Theorem 4) and for the construction itself
(Proposition 10).

## What is formalized

Every numbered theorem, lemma and proposition of [KM] is proved in Lean: Theorems 1, 4 and 6, Lemmas 2, 3, 5 and 7,
and Propositions 8 and 10. So are the unnumbered statements of the text that these results use, among them the Welch
bound and the Gershgorin estimate in matrix-norm form, and the statement that the matrices of Theorem 1 do not break
the 2/3 barrier. In total these are 30 theorems about 25 definitions; [PAPER_MAP.md](PAPER_MAP.md) gives, for each,
its place in [KM] and its Lean declaration. The proofs use only Lean's standard axioms `propext`, `Classical.choice`
and `Quot.sound`, and contain no `sorry`.

- **Statements.** Every statement is a Lean declaration in its own file under `ExplicitRIP/Frozen/` (definitions under
  `ExplicitRIP/Frozen/Defs/`). These *frozen statements* were written from the paper, checked against it by an
  independent agent and approved; the proofs had to establish exactly these statements. Their docstrings cite [KM]
  and explain how they read the text.
- **Theorem 1** is proved for the matrices of the paper: a real factor of the Gram matrix `G = I − μA + νĀ` of the
  strongly regular graph `VO₄⁻(p)`, restricted to the columns indexed by `V'_T = {(c, N(c) + t)}`, where `N` is the
  norm of `𝔽_{p³}/𝔽_p`. As in [KM, footnotes 3 and 4], the factor is the Cholesky factor of `G` in lexicographic vertex
  order with the zero rows of zero pivots deleted (computed by exact `LDLᵀ` elimination over ℚ), and `𝔽_p³` is
  identified with `𝔽_{p³}` through the power basis of the lexicographically first monic irreducible cubic. The limits
  run through the primes `p ≡ 3 (mod 4)`, with the parameters of the proof of Theorem 1.
- **Theorem 6** is the case of Zahl's sphere-tangency theorem [Z, Theorem 1.8] that [KM] uses: sphere families in
  `𝔽_p⁴` with `p ≡ 3 (mod 4)` and at most `p²` spheres. It is proved here from Mathlib alone, together with the line
  case, in positive characteristic, of the structure theorem of Guth and Zahl [GZ, Theorem 3.8] on which Zahl's proof
  rests. As [KM, footnote 2] notes, formalizing these proofs required a number of local corrections to the published
  arguments; none of them affects the statement of Theorem 6.
- **Readings.** Where the text of [KM] needs an interpretation, the Lean statement fixes one and its docstring says
  so. For example, "for all sufficiently large m" in Proposition 10 is read as eventually along the sequence,
  uniformly in `1 ≤ k ≤ n`, and Lemma 5 keeps the standing assumption of [KM, Section 3] that the graph and its
  complement are connected.
- **Not formalized:** the meaning of *explicit* in [KM] (entries computable in time polynomial in the dimensions and
  the precision): the matrices are given by concrete definitions, but no running-time bound is proved. Also not
  formalized are the background results quoted in the introduction other than the Welch bound, heuristic remarks,
  and the open Problem 9.

## Checking it yourself

You need [elan](https://github.com/leanprover/elan), which installs the Lean version pinned in `lean-toolchain`, and
Python 3 for the optional checks.

```sh
lake exe cache get                      # download the compiled Mathlib v4.35.0 (several GB)
lake build                              # build the formalization (about 20 minutes on a laptop)
lake env lean scripts/PrintAxioms.lean  # axioms of the 55 frozen declarations and the 4 compared theorems
python3 scripts/check_lean_modules.py   # module-system conventions and the Comparator configuration
```

The build reports no warnings except the four deliberate `declaration uses 'sorry'` warnings of `Challenge.lean` (see
below). The axiom check prints only `propext`, `Classical.choice` and `Quot.sound`.

## Statement package

The repository follows the layout of the [Palomar registry](https://palomar-registry.org) of Lean-verified results.

| File | Role |
|---|---|
| `Challenge.lean` | The statements to audit, importing only Mathlib: the four compared theorems with `sorry` proofs and the definitions they use, written out in full, in the namespace `KM`. |
| `Solution.lean` | The same definitions verbatim, and each theorem proved by the frozen statement that states it. |
| `comparator.json` | The compared theorems `KM.main_theorem` (Theorem 1), `KM.unsigned_barrier` (Theorem 4), `KM.construction_barrier` (Proposition 10) and `KM.construction_barrier_host` (Proposition 10 for the matrices of Theorem 1), and the permitted axioms `propext`, `Quot.sound` and `Classical.choice`. |
| `formalization.yaml` | Sources, scope, fidelity notes, automation and review, in the `formalization.yaml` v0.4 format. |

The definitions and theorems of `Challenge.lean` are copied from the frozen statements, with the namespace
`ExplicitRIP` renamed to `KM`, because `Solution.lean` imports the development, whose declarations keep their names.
[Comparator](https://github.com/leanprover/comparator) checks that the Challenge and the Solution state the same
theorems about the same definitions and that the proofs use only the permitted axioms. Lean 4.35 ships it as
`lake comparator`. On Linux, where it runs the checks in a [bubblewrap](https://github.com/containers/bubblewrap)
sandbox (install `bwrap`, with user namespaces enabled), run

```sh
lake comparator --config comparator.json
```

macOS has no `bwrap`. There, after `lake build`, run `scripts/comparator_macos.sh`: it exports the modules
`Challenge` and `Solution` from the build with the toolchain's `leanexport`, using the same export targets as
`lake comparator`, and compares the two exports with `lake comparator --inadvisably-no-sandbox`. The comparison
passes, with both the NanoDa and the Lean kernel replaying the exported Solution.

## How the code is organized

| Path | Content |
|---|---|
| `ExplicitRIP/Frozen/` | The 30 theorem statements, one per file. Each proof is the single line `by exact ExplicitRIP.Provider.<name>`. |
| `ExplicitRIP/Frozen/Defs/` | The 25 definitions that the statements use, one per file. |
| `ExplicitRIP/Provider/` | One module per frozen theorem, assembling its proof from the library below, and one shared helper module. |
| `ExplicitRIP/Analysis/` | Sections 2, 3 and 5 of [KM]: norms, the restricted isometry constant, the hybrid and unsigned estimates, the scaling of strongly regular graphs (`SrgScaling/`), the barrier for two-distance tight frames (`TwoDistanceBarrier/`) and the asymptotics of Theorem 1. |
| `ExplicitRIP/Contact/` | Sections 3 and 4 in the coordinates `(x, y, z, r)` of [KM]: the host frame, the selection `V'_T`, the density bound of Proposition 8 and the Cholesky realization. |
| `ExplicitRIP/HermitianForms/` | An isomorphic model of the host graph on Hermitian forms, in which part of the construction is proved before `Contact/` transports it to the coordinates of [KM]. |
| `ExplicitRIP/Zahl/` | Zahl's argument for Theorem 6: Lie's line–sphere correspondence, pencils and incidence counting. |
| `ExplicitRIP/GuthZahl/` | The line case of the Guth–Zahl structure theorem in positive characteristic. |
| `ExplicitRIP/Relative/` | Conditional steps whose premise is the Guth–Zahl structure theorem or Zahl's theorem in a stated form, together with unconditional helper lemmas for them. Each conditional module names the proved theorem that discharges its premise. |
| `ExplicitRIP/Algebra/`, `LinearAlgebra/`, `Combinatorics/` | Supporting algebra: finite fields, the avoidance lemmas, exact `LDLᵀ` elimination and counting. |
| `Challenge.lean`, `Solution.lean` | The statement package (above). |
| `scripts/` | The axiom check `PrintAxioms.lean`, the module checker `check_lean_modules.py` and `comparator_macos.sh`. |

## How the formalization was made

The formalization was produced by AI agents directed by the authors of [KM]. An orchestrating agent (Claude Opus 5.5 in Claude Code) wrote the Lean statements from the paper and had each of them
audited against the paper by an independent agent. The proofs were written by Codex CLI agents running GPT-6.1 Sol and GPT-6 Astra and by Claude subagents, and every proof of a frozen statement was audited independently
before it was accepted. The statement package was finally
checked with Comparator.

## Toolchain

Lean `v4.35.0` with Mathlib `v4.35.0`, pinned in `lean-toolchain` and `lake-manifest.json`. Every Lean file uses the
module system. Mathlib is the only direct dependency.

## Citing

Please cite the paper:

```bibtex
@misc{KuemmerleMixon2026,
  author        = {Christian K{\"u}mmerle and Dustin G. Mixon},
  title         = {Explicit restricted isometries with $k=m^{2/3-o(1)}$},
  year          = {2026},
  eprint        = {2611.14475},
  archivePrefix = {arXiv},
}
```

## License

The Lean code is released under the Apache License 2.0; see [LICENSE](LICENSE).

## References

- [KM] C. Kümmerle and D. G. Mixon, *Explicit restricted isometries with k = m^{2/3−o(1)}*,
  [arXiv:2611.14475](https://arxiv.org/abs/2611.14475).
- [Z] J. Zahl, *Sphere tangencies, line incidences, and Lie's line-sphere correspondence*, Math. Proc. Cambridge
  Philos. Soc. 172 (2022), no. 2, 401–421, [arXiv:2002.11677](https://arxiv.org/abs/2002.11677).
- [GZ] L. Guth and J. Zahl, *Algebraic curves, rich points, and doubly-ruled surfaces*, Amer. J. Math. 140 (2018),
  no. 5, 1187–1229, [arXiv:1503.02173](https://arxiv.org/abs/1503.02173).
