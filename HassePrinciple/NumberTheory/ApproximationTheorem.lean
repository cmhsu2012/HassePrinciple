/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.NumberTheory.PrimeCounting

/-! # Approximation theorem. -/

@[expose] public section


noncomputable section

namespace Rat


/-- TODO -/
local instance fact_prime_nth_prime (n : ℕ) : Fact (Nat.Prime (Nat.nth Nat.Prime n)) :=
  fact_iff.mpr (Nat.prime_nth_prime n)

open Padic

/-- TODO -/
theorem approximation' {S : Finset ℕ} {ε : ℝ} (hε : ε > 0)
    (y : ℝ × (Π n : S, ℚ_[Nat.nth Nat.Prime n])) :
    ∃ x : ℚ, ‖y.1 - x‖ + Finset.sum (Finset.attach S) (fun n ↦ ‖y.2 n - x‖) < ε := by
  sorry

/-- TODO -/
abbrev finiteEmbedding (S : Finset ℕ) (x : ℚ) : ℝ × (Π n : S, ℚ_[Nat.nth Nat.Prime n]) :=
  ⟨algebraMap ℚ ℝ x, fun n ↦ (algebraMap ℚ ℚ_[Nat.nth Nat.Prime n]) x⟩

theorem approximation (S : Finset ℕ) :
    Dense (Set.range (finiteEmbedding S)) := by
  sorry

end Rat
