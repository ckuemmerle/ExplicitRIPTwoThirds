/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib

/-!
# Explicit restricted isometries with `k = m^{2/3 - o(1)}`: the compared statements

This module states the principal results of [KM] in the namespace `KM`. It imports only Mathlib;
every definition is written out in full and every theorem ends in `sorry`. `Solution.lean` proves
each theorem by the frozen statement of the development (`ExplicitRIP/Frozen/`) that states it.

## The compared results

* `KM.main_theorem` (Theorem 1): an explicit family of real `m × n` matrices with unit-norm columns
  such that `m → ∞`, `m/n → 0`, `δ_k → 0` and `k = m^{2/3 - o(1)}`.
* `KM.unsigned_barrier` (Theorem 4): if `m → ∞`, `m/n → 0` and the unsigned constants `Δ_k → 0`,
  then `k = o(m^{2/3})`: bounds through `Δ_k`, which ignore the signs of the Gram entries, cannot
  pass the `2/3` barrier.
* `KM.construction_barrier` (Proposition 10): subframes of two-distance tight frames with coherence
  `μ ≳ m^{-1/3}` do not pass it either, even with phase cancellation.
* `KM.construction_barrier_host`: the matrices of Theorem 1 do not break the `2/3` barrier.

## The construction

For a prime `p ≡ 3 (mod 4)`, let `A` be the adjacency matrix of the graph `VO₄⁻(p)` on `𝔽_p⁴`
(`contactGraph`) and `G = I - μA + νĀ` (`hostGram`), with `m = (p - 1)(p² + 1)`,
`μ = (p² - p + 1)/m` and `ν = 1/(p² + 1)`. Then `G` is the Gram matrix of a real unit-norm
two-distance tight frame in dimension `m`. For `T ⊆ 𝔽_p`, the matrix `Φ_T` keeps the columns of that
frame indexed by `V'_T = {(c, N(c) + t) : c ∈ 𝔽_p³, t ∈ T}`, where `N` is the norm of `𝔽_{p³}/𝔽_p`.
As in [KM, footnotes 3 and 4], the frame is the Cholesky factor of `G` in lexicographic vertex order
with the zero rows of zero pivots deleted (computed by exact `LDLᵀ` elimination), and `𝔽_p³` is
identified with `𝔽_{p³}` through the power basis of the lexicographically first monic irreducible
cubic. For a fixed `V'_T`, the choice of real factor does not affect `δ_k`, which depends only on
`G[V'_T]`; the identification determines `V'_T`. "Explicit" means these concrete definitions; no
running-time bound is formalized. Limits along primes `p ≡ 3 (mod 4)` use `ε`-`P` quantifiers.

## References

* [KM] C. Kümmerle and D. G. Mixon, *Explicit restricted isometries with `k = m^{2/3 - o(1)}`*,
  arXiv:2611.14475.
-/

@[expose] public section

open scoped Matrix

/-! ## Definitions -/

/-- The spectral norm `‖M‖ = ‖M‖_{2→2}` of a matrix `M ∈ 𝕜^{m × n}` (`𝕜 = ℝ` or `ℂ`): the operator
norm of `x ↦ M x` between the Euclidean spaces `𝕜ⁿ` and `𝕜ᵐ`. -/
noncomputable def KM.opNorm {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m]
    [Fintype n] [DecidableEq n] (M : Matrix m n 𝕜) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)‖

/-- The restricted isometry constant `δ_k(Φ) = max_{|S| ≤ k} ‖Φ_Sᴴ Φ_S - I‖`, where `Φ_S` is the
submatrix of the columns of `Φ` indexed by `S`. Equivalently, `δ_k` is the least `δ ≥ 0` such that
`(1 - δ)‖x‖² ≤ ‖Φ x‖² ≤ (1 + δ)‖x‖²` for every `x` with at most `k` nonzero entries (proved in the
development as `ExplicitRIP.ripConstant_isLeast`). -/
noncomputable def KM.ripConstant {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m]
    [Fintype n] [DecidableEq n] (Φ : Matrix m n 𝕜) (k : ℕ) : ℝ :=
  ⨆ S : {S : Finset n // S.card ≤ k},
    KM.opNorm ((Φ.submatrix id (Subtype.val : S.1 → n))ᴴ *
      Φ.submatrix id (Subtype.val : S.1 → n) - 1)

/-- The unsigned constant `Δ_k(Φ) = max_{|S| ≤ k} ‖H[S]‖`, where `H = |Φᴴ Φ - I|` is the entrywise
absolute value of `Φᴴ Φ - I` and `H[S]` its principal submatrix indexed by `S`. Always `δ_k ≤ Δ_k`;
a bound on `Δ_k` is a bound on `δ_k` that ignores the signs (phases) of the Gram entries. -/
noncomputable def KM.unsignedRIPConstant {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m]
    [Fintype n] [DecidableEq n] (Φ : Matrix m n 𝕜) (k : ℕ) : ℝ :=
  ⨆ S : {S : Finset n // S.card ≤ k},
    KM.opNorm (((Φᴴ * Φ - 1).map fun z => ‖z‖).submatrix
      (Subtype.val : S.1 → n) (Subtype.val : S.1 → n))

/-- The coherence `μ(Φ) = max_{i ≠ j} |⟨φ_i, φ_j⟩|` of the columns `φ_j` of `Φ`, where
`⟨φ_i, φ_j⟩ = (Φᴴ Φ)_{ij}`; it is `0` when `Φ` has at most one column. -/
noncomputable def KM.coherence {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m]
    [Fintype n] (Φ : Matrix m n 𝕜) : ℝ :=
  ⨆ ij : {ij : n × n // ij.1 ≠ ij.2}, ‖(Φᴴ * Φ) ij.1.1 ij.1.2‖

/-- `F ∈ ℝ^{m × N}` is a two-distance tight frame, as defined in [KM, Section 3]: there are
`a, b, c ∈ ℝ` with `a ≠ b` such that the diagonal entries of `Fᵀ F` equal `1`, its off-diagonal
entries lie in `{a, b}`, and `F Fᵀ = c I`. So the columns have unit norm, form a tight frame, and
the inner products of distinct columns take at most two values. -/
def KM.IsTwoDistanceTightFrame {m N : Type*} [Fintype m] [Fintype N] [DecidableEq m]
    (F : Matrix m N ℝ) : Prop :=
  ∃ a b c : ℝ, a ≠ b ∧ (∀ j, (Fᵀ * F) j j = 1) ∧
    (∀ i j, i ≠ j → (Fᵀ * F) i j = a ∨ (Fᵀ * F) i j = b) ∧
    F * Fᵀ = c • (1 : Matrix m m ℝ)

/-- For a prime `p ≡ 3 (mod 4)`, the elliptic affine polar graph `VO₄⁻(p)`: the vertices are the
points `(x, y, z, r) ∈ 𝔽_p⁴`, and distinct `u, v` are adjacent when `Q(u - v) = 0`, where
`Q(x, y, z, r) = x² + y² + z² - r²`. It is strongly regular with parameters
`(p⁴, (p - 1)(p² + 1), p - 2, p(p - 1))` (`ExplicitRIP.host_parameters`). -/
def KM.contactGraph (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)] :
    SimpleGraph (ZMod p × ZMod p × ZMod p × ZMod p) :=
  SimpleGraph.fromRel fun u v =>
    (u - v).1 ^ 2 + (u - v).2.1 ^ 2 + (u - v).2.2.1 ^ 2 - (u - v).2.2.2 ^ 2 = 0

/-- The matrix `G = I - μA + νĀ = I - μA + ν(J - I - A)` over a field `K` of characteristic zero
(`ℚ` for the exact factorization, `ℝ` for the frame), where `A` is the adjacency matrix of
`VO₄⁻(p)`, `m = (p - 1)(p² + 1)`, `μ = (p² - p + 1)/m` and `ν = 1/(p² + 1)` (`a` and `b` in the
code). Over `ℝ`, `G` is `p⁴/m` times the orthogonal projection onto an `m`-dimensional eigenspace of
`A`, so it is the Gram matrix of a unit-norm tight frame in dimension `m`
(`ExplicitRIP.host_frame_params`); its off-diagonal entries are `-μ` and `ν`, so the frame is
two-distance with coherence `μ`. -/
noncomputable def KM.hostGram (K : Type*) [Field K] [CharZero K] (p : ℕ) [Fact p.Prime]
    [Fact (p % 4 = 3)] :
    Matrix (ZMod p × ZMod p × ZMod p × ZMod p) (ZMod p × ZMod p × ZMod p × ZMod p) K :=
  open Classical in
  let m : K := ((p : K) - 1) * ((p : K) ^ 2 + 1)
  let a : K := ((p : K) ^ 2 - p + 1) / m
  let b : K := 1 / ((p : K) ^ 2 + 1)
  let A := (KM.contactGraph p).adjMatrix K
  1 - a • A + b • (Matrix.of (fun _ _ => (1 : K)) - 1 - A)

/-- The lexicographically first monic irreducible cubic over `𝔽_p`: among the cubics
`X³ + c₂ X² + c₁ X + c₀` with `(c₂, c₁, c₀) ∈ {0, …, p - 1}³`, ordered by `c₂ p² + c₁ p + c₀`, the
first one that is irreducible over `ZMod p`. The fallback `X³` is never reached (proved in the
development as `ExplicitRIP.firstIrreducibleCubic_spec`). -/
noncomputable def KM.firstIrreducibleCubic (p : ℕ) [Fact p.Prime] : Polynomial (ZMod p) :=
  open Classical in
  let cubic : ℕ → Polynomial (ZMod p) := fun n =>
    Polynomial.X ^ 3 + Polynomial.C ((n / p ^ 2 : ℕ) : ZMod p) * Polynomial.X ^ 2 +
      Polynomial.C ((n / p % p : ℕ) : ZMod p) * Polynomial.X + Polynomial.C ((n % p : ℕ) : ZMod p)
  match (List.range (p ^ 3)).find? (fun n => decide (Irreducible (cubic n))) with
  | some n => cubic n
  | none => Polynomial.X ^ 3

/-- The norm `N : 𝔽_p³ → 𝔽_p` of the field extension `𝔽_{p³}/𝔽_p`. Here `𝔽_{p³} = 𝔽_p[θ]` is the
field obtained by adjoining a root `θ` of `firstIrreducibleCubic p`, identified with `𝔽_p³` through
the basis `1, θ, θ²`, and `N(w₀, w₁, w₂) = N_{𝔽_{p³}/𝔽_p}(w₀ + w₁ θ + w₂ θ²)`. This is the
identification of `𝔽_p³` with `𝔽_{p³}` that [KM, footnote 3] fixes. -/
noncomputable def KM.fieldNorm (p : ℕ) [Fact p.Prime] (w : ZMod p × ZMod p × ZMod p) :
    ZMod p :=
  Algebra.norm (ZMod p)
    (AdjoinRoot.of (KM.firstIrreducibleCubic p) w.1 +
      AdjoinRoot.of (KM.firstIrreducibleCubic p) w.2.1 *
        AdjoinRoot.root (KM.firstIrreducibleCubic p) +
      AdjoinRoot.of (KM.firstIrreducibleCubic p) w.2.2 *
        AdjoinRoot.root (KM.firstIrreducibleCubic p) ^ 2)

/-- The vertex set `V'_T = {(c, N(c) + t) : c ∈ 𝔽_p³, t ∈ T}` for `T ⊆ 𝔽_p`, in the coordinates
`(x, y, z, r)` with `c = (x, y, z)`: the `|T|` translates of the graph of the field norm `N`. -/
noncomputable def KM.selectedVertices (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]
    (T : Finset (ZMod p)) : Finset (ZMod p × ZMod p × ZMod p × ZMod p) :=
  (Finset.univ ×ˢ T).image fun ct : (ZMod p × ZMod p × ZMod p) × ZMod p =>
    (ct.1.1, ct.1.2.1, ct.1.2.2, KM.fieldNorm p ct.1 + ct.2)

/-- The lexicographic enumeration `(ZMod p)⁴ → Fin (p⁴)`, `(x, y, z, r) ↦ x p³ + y p² + z p + r`
with the representatives `0, …, p - 1`, for any nonzero `p`; for prime `p` these are the coordinates
of `𝔽_p⁴`. -/
def KM.lexEquiv (p : ℕ) [NeZero p] :
    (ZMod p × ZMod p × ZMod p × ZMod p) ≃ Fin (p * (p * (p * p))) :=
  let e : ZMod p ≃ Fin p := (ZMod.finEquiv p).symm.toEquiv
  (e.prodCongr (e.prodCongr (e.prodCongr e))).trans <|
    ((Equiv.refl (Fin p)).prodCongr ((Equiv.refl (Fin p)).prodCongr finProdFinEquiv)).trans <|
      ((Equiv.refl (Fin p)).prodCongr finProdFinEquiv).trans finProdFinEquiv

/-- The rational matrix `G = hostGram ℚ p` with its rows and columns in lexicographic vertex order.
-/
noncomputable def KM.lexGram (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)] :
    Matrix (Fin (p * (p * (p * p)))) (Fin (p * (p * (p * p)))) ℚ :=
  (KM.hostGram ℚ p).submatrix (KM.lexEquiv p).symm (KM.lexEquiv p).symm

/-- Exact symmetric (`LDLᵀ`) Gaussian elimination over `ℚ`, as a total recursion: `ldlResidual G k`
is the residual matrix after the indices `0, …, k - 1` have been processed. At index `k` with pivot
`d = R(k, k)`, the residual `R` is kept if `d = 0` and replaced by `R - d⁻¹ R(·, k) R(k, ·)`
otherwise. Once `k ≥ v` the residual is unchanged. -/
def KM.ldlResidual {v : ℕ} (G : Matrix (Fin v) (Fin v) ℚ) :
    ℕ → Matrix (Fin v) (Fin v) ℚ
  | 0 => G
  | k + 1 =>
    if h : k < v then
      if KM.ldlResidual G k ⟨k, h⟩ ⟨k, h⟩ = 0 then KM.ldlResidual G k
      else KM.ldlResidual G k -
        (KM.ldlResidual G k ⟨k, h⟩ ⟨k, h⟩)⁻¹ •
          Matrix.of fun i j => KM.ldlResidual G k i ⟨k, h⟩ *
            KM.ldlResidual G k ⟨k, h⟩ j
    else KM.ldlResidual G k

/-- The indices `k`, in increasing order, whose pivot `(ldlResidual G k)(k, k)` is nonzero. For
positive semidefinite `G` these pivots are positive and their number is `rank G` (proved in the
development as `ExplicitRIP.ldl_factorization`). -/
def KM.ldlPivots {v : ℕ} (G : Matrix (Fin v) (Fin v) ℚ) : List (Fin v) :=
  (List.finRange v).filter fun k => KM.ldlResidual G k k k ≠ 0

/-- The real matrix built from the retained pivots: the row for the `r`-th nonzero pivot `k` is
`x ↦ R_k(k, x) / √d_k`, where `R_k = ldlResidual G k` and `d_k = R_k(k, k)`. If `G` is positive
semidefinite, every retained pivot is positive and this is a Cholesky factor with the zero pivots
omitted: `Bᵀ B = G` (proved in the development as `ExplicitRIP.ldl_factorization`). For other `G` it
is only a total formula (`Real.sqrt` of a negative number and division by zero are `0`). -/
noncomputable def KM.ldlFactor {v : ℕ} (G : Matrix (Fin v) (Fin v) ℚ) :
    Matrix (Fin (KM.ldlPivots G).length) (Fin v) ℝ :=
  fun r x =>
    (((KM.ldlResidual G ((KM.ldlPivots G).get r) ((KM.ldlPivots G).get r)
        x : ℚ) : ℝ)) /
      Real.sqrt (((KM.ldlResidual G ((KM.ldlPivots G).get r)
        ((KM.ldlPivots G).get r) ((KM.ldlPivots G).get r) : ℚ) : ℝ))

/-- The explicit matrix `Φ_T` of Theorem 1: the factor `ldlFactor` of `G` in lexicographic vertex
order, a Cholesky factor since `G` is positive semidefinite, with one row per nonzero pivot
(`m = (p - 1)(p² + 1)` rows), restricted to the columns indexed by `V'_T = selectedVertices p T`.
Its Gram matrix is `G[V'_T]` (proved in the development as `ExplicitRIP.final_rip`), so its columns
form a subframe of a two-distance tight frame. The lexicographic vertex order and the deletion of
the zero rows of zero pivots are the choices of [KM, footnote 4]. -/
noncomputable def KM.choleskyMatrix (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]
    (T : Finset (ZMod p)) :
    Matrix (Fin (KM.ldlPivots (KM.lexGram p)).length)
      (KM.selectedVertices p T) ℝ :=
  fun r x => KM.ldlFactor (KM.lexGram p) r (KM.lexEquiv p x.1)

/-! ## The compared theorems -/

/-- **Theorem 1.** For primes `p ≡ 3 (mod 4)` take `L = ⌊log p⌋`, `T = {0, …, L - 1} ⊆ 𝔽_p` and
`k = ⌊p² / (log p)⁶⌋`. There are infinitely many such primes, and for all large enough ones the
matrix `Φ_T = choleskyMatrix p T`, with `m` rows (one per nonzero pivot) and `n = |V'_T|` columns,
has unit-norm columns and `k ≤ m^{2/3}`. Along these primes `m, n → ∞`, `m / n → 0`, `δ_k(Φ_T) → 0`
and `log k / log m → 2/3`, so eventually `k = m^{2/3 - ε_p}` with `0 ≤ ε_p → 0`. Each limit is an
`ε`-`P` statement. -/
theorem KM.main_theorem :
    {p : ℕ | p.Prime ∧ p % 4 = 3}.Infinite ∧
      ∀ ε : ℝ, 0 < ε → ∃ P : ℕ, ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)], P ≤ p →
        let L := ⌊Real.log p⌋₊
        let T : Finset (ZMod p) := (Finset.range L).image fun t : ℕ => (t : ZMod p)
        let k := ⌊(p : ℝ) ^ 2 / Real.log p ^ 6⌋₊
        let m := (KM.ldlPivots (KM.lexGram p)).length
        let n := (KM.selectedVertices p T).card
        (∀ x, ∑ r, KM.choleskyMatrix p T r x ^ 2 = 1) ∧
          1 / ε ≤ (n : ℝ) ∧ 1 / ε ≤ (m : ℝ) ∧ (m : ℝ) / n ≤ ε ∧
          KM.ripConstant (KM.choleskyMatrix p T) k ≤ ε ∧
          (k : ℝ) ≤ (m : ℝ) ^ (2 / 3 : ℝ) ∧ |Real.log k / Real.log m - 2 / 3| ≤ ε := by
  sorry

/-- **Theorem 4** (the `2/3` barrier for arguments without phase cancellation). If `Φ ∈ ℂ^{m × n}`
has unit-norm columns and `2 ≤ k ≤ m ≤ n`, then
`Δ_k² ≥ (n - m)(k - 1)^{3/2} / (m (n - 1 + (k - 1)^{3/2}))`. Consequently, for every sequence
eventually satisfying these hypotheses, `m → ∞`, `m/n → 0` and `Δ_k → 0` imply `k = o(m^{2/3})`. -/
theorem KM.unsigned_barrier :
    (∀ (m n : ℕ) (Φ : Matrix (Fin m) (Fin n) ℂ), (∀ j, ∑ i, ‖Φ i j‖ ^ 2 = 1) →
      ∀ k : ℕ, 2 ≤ k → k ≤ m → m ≤ n →
        ((n : ℝ) - m) * ((k : ℝ) - 1) ^ (3 / 2 : ℝ) /
            ((m : ℝ) * ((n : ℝ) - 1 + ((k : ℝ) - 1) ^ (3 / 2 : ℝ))) ≤
          KM.unsignedRIPConstant Φ k ^ 2) ∧
      ∀ (m n k : ℕ → ℕ) (Φ : ∀ j, Matrix (Fin (m j)) (Fin (n j)) ℂ),
        (∀ᶠ j in Filter.atTop,
          (∀ c, ∑ i, ‖Φ j i c‖ ^ 2 = 1) ∧ 2 ≤ k j ∧ k j ≤ m j ∧ m j ≤ n j) →
        Filter.Tendsto (fun j => (m j : ℝ)) Filter.atTop Filter.atTop →
        Filter.Tendsto (fun j => (m j : ℝ) / n j) Filter.atTop (nhds 0) →
        Filter.Tendsto (fun j => KM.unsignedRIPConstant (Φ j) (k j)) Filter.atTop
          (nhds 0) →
        (fun j => (k j : ℝ)) =o[Filter.atTop] (fun j => (m j : ℝ) ^ (2 / 3 : ℝ)) := by
  sorry

/-- **Proposition 10.** Let `F_j ∈ ℝ^{m_j × N_j}` be two-distance tight frames with coherence `μ_j`,
and let `Φ_j` be the subframe of the columns indexed by `S_j`, where `S_j` is eventually nonempty
and `n_j = |S_j|`. If `m_j → ∞` and `m_j / n_j → 0`, then for all sufficiently large `j`,
`δ_k(Φ_j) ≥ min {μ_j √(k - 1), 1}` for every `1 ≤ k ≤ n_j`. In particular, if `μ_j ≥ C m_j^{-1/3}`
eventually for some `C > 0`, then `δ_{k_j}(Φ_j) → 0` with `1 ≤ k_j ≤ n_j` eventually requires
`k_j = o(m_j^{2/3})`, even with phase cancellation. -/
theorem KM.construction_barrier :
    ∀ (m N : ℕ → ℕ) (F : ∀ j, Matrix (Fin (m j)) (Fin (N j)) ℝ) (S : ∀ j, Finset (Fin (N j))),
      (∀ j, KM.IsTwoDistanceTightFrame (F j)) →
      (∀ᶠ j in Filter.atTop, (S j).Nonempty) →
      Filter.Tendsto (fun j => (m j : ℝ)) Filter.atTop Filter.atTop →
      Filter.Tendsto (fun j => (m j : ℝ) / (S j).card) Filter.atTop (nhds 0) →
      (∀ᶠ j in Filter.atTop, ∀ k : ℕ, 1 ≤ k → k ≤ (S j).card →
          min (KM.coherence (F j) * Real.sqrt ((k : ℝ) - 1)) 1 ≤
            KM.ripConstant ((F j).submatrix id (Subtype.val : S j → Fin (N j))) k) ∧
        ((∃ C : ℝ, 0 < C ∧ ∀ᶠ j in Filter.atTop,
            C * (m j : ℝ) ^ (-(1 / 3 : ℝ)) ≤ KM.coherence (F j)) →
          ∀ k : ℕ → ℕ, (∀ᶠ j in Filter.atTop, 1 ≤ k j ∧ k j ≤ (S j).card) →
            Filter.Tendsto (fun j => KM.ripConstant
                ((F j).submatrix id (Subtype.val : S j → Fin (N j))) (k j)) Filter.atTop (nhds 0) →
            (fun j => (k j : ℝ)) =o[Filter.atTop] (fun j => (m j : ℝ) ^ (2 / 3 : ℝ))) := by
  sorry

/-- **The matrices of Theorem 1 do not break the `2/3` barrier** ([KM, abstract and Section 5]:
Proposition 10 applied to the host frames, whose coherence is `μ ∼ m^{-1/3}`). Let `p_j ≡ 3 (mod 4)`
be primes, `Γ_j ⊆ 𝔽_{p_j}⁴` vertex sets and `Φ_j` real matrices with `m_j = (p_j - 1)(p_j² + 1)`
rows and Gram matrix `Φ_jᵀ Φ_j = G[Γ_j]`, that is, subframes of real factorizations of the host Gram
matrix; this includes the matrices `Φ_T` of Theorem 1, up to relabeling their rows. If
`m_j / |Γ_j| → 0`, `1 ≤ k_j ≤ |Γ_j|` eventually and `δ_{k_j}(Φ_j) → 0`, then
`k_j = o(m_j^{2/3})`. -/
theorem KM.construction_barrier_host :
    ∀ (p : ℕ → ℕ) [∀ j, Fact (p j).Prime] [∀ j, Fact (p j % 4 = 3)]
      (Γ : ∀ j, Finset (ZMod (p j) × ZMod (p j) × ZMod (p j) × ZMod (p j)))
      (Φ : ∀ j, Matrix (Fin ((p j - 1) * (p j ^ 2 + 1))) (Γ j) ℝ) (k : ℕ → ℕ),
      (∀ j, (Φ j)ᵀ * Φ j = (KM.hostGram ℝ (p j)).submatrix Subtype.val Subtype.val) →
      (∀ᶠ j in Filter.atTop, 1 ≤ k j ∧ k j ≤ (Γ j).card) →
      Filter.Tendsto (fun j => (((p j - 1) * (p j ^ 2 + 1) : ℕ) : ℝ) / (Γ j).card) Filter.atTop
        (nhds 0) →
      Filter.Tendsto (fun j => KM.ripConstant (Φ j) (k j)) Filter.atTop (nhds 0) →
      (fun j => (k j : ℝ)) =o[Filter.atTop]
        (fun j => (((p j - 1) * (p j ^ 2 + 1) : ℕ) : ℝ) ^ (2 / 3 : ℝ)) := by
  sorry
