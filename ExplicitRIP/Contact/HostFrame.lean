/-
Copyright (c) 2026 Christian Kümmerle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Kümmerle
-/
module

public import ExplicitRIP.Contact.HostFrame.Spectrum

/-!
# The contact-coordinate host frame

The strong regularity, least eigenvalue, Gram projection, rank and tight frame for the graph
`VO₄⁻(p)` of [KM, Section 3], with frame parameters [KM, (13)].
-/

public section

namespace ExplicitRIP.Contact.HostFrame

theorem asymptotics :
    ∀ ε : ℝ, 0 < ε → ∃ P : ℕ, ∀ (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)], P ≤ p →
      |(p : ℝ) * (((p : ℝ) ^ 2 - p + 1) / (((p : ℝ) - 1) * ((p : ℝ) ^ 2 + 1))) - 1| ≤ ε ∧
      |(p : ℝ) ^ 2 * (1 / ((p : ℝ) ^ 2 + 1)) - 1| ≤ ε := by
  intro ε hε
  obtain ⟨P, hP⟩ := ExplicitRIP.Hermitian.hermitian_graph_frame.2 ε hε
  refine ⟨P, fun p _ _ hp => ?_⟩
  exact ⟨(hP p hp).1, (hP p hp).2.1⟩

end ExplicitRIP.Contact.HostFrame
