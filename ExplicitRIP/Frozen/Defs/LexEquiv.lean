/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import Mathlib

/-!
# The lexicographic enumeration of the vertices

Source: [KM, proof of Theorem 1, footnote 4].
-/

@[expose] public section

open scoped Matrix

/-- For any nonzero `p`, the lexicographic enumeration `(ZMod p)⁴ → Fin (p⁴)` with the
representatives `0, …, p - 1` (via `ZMod.finEquiv`): `(x, y, z, r) ↦ x p³ + y p² + z p + r`. For
prime `p` this enumerates the vertices `(x, y, z, r)` of `𝔽_p⁴` in the order of [KM, footnote 4]. -/
def ExplicitRIP.lexEquiv (p : ℕ) [NeZero p] :
    (ZMod p × ZMod p × ZMod p × ZMod p) ≃ Fin (p * (p * (p * p))) :=
  let e : ZMod p ≃ Fin p := (ZMod.finEquiv p).symm.toEquiv
  (e.prodCongr (e.prodCongr (e.prodCongr e))).trans <|
    ((Equiv.refl (Fin p)).prodCongr ((Equiv.refl (Fin p)).prodCongr finProdFinEquiv)).trans <|
      ((Equiv.refl (Fin p)).prodCongr finProdFinEquiv).trans finProdFinEquiv
