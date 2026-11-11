/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.GuthZahl.Defs

/-!
# Guth–Zahl line route: definitions for the contagion branch

Boolean patterns record which polynomial tests vanish identically on a line or
on an irreducible surface. They connect pointwise tests with algebraic containment.

* `lineGenericPattern`
* `surfaceGenericPattern`
-/

@[expose] public section

namespace ExplicitRIP.GuthZahl

open Classical in
noncomputable def lineGenericPattern {K : Type*} [Field K] {J : ℕ}
    (qs : Fin J → Poly K) (L : Line K) : Fin J → Bool :=
  fun j => decide (LineOn (qs j) L)

open Classical in
noncomputable def surfaceGenericPattern {K : Type*} [Field K] {J : ℕ}
    (f : Poly K) (qs : Fin J → Poly K) : Fin J → Bool :=
  fun j => decide (f ∣ qs j)

end ExplicitRIP.GuthZahl

end
