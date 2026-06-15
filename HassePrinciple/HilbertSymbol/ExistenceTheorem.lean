/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

public import HassePrinciple.HilbertSymbol.Basic
public import HassePrinciple.NumberTheory.ApproximationTheorem

/-!
# Existence theorem
-/
@[expose] public section

namespace hilbertSym

/-- Given a finite set of rational numbers {a_i}_{i ∈ I} and functions from I to {±1} for each
place of ℚ, there exists a rational number x such that the Hilbert symbol of x and a_i at each place
is given by the respective function -/
theorem exists_rat_with_prescribed_hilbert_symbols_at_finitely_many_places
    {I : Type*} [Finite I] (a : I → ℚˣ) (efin : I × ℕ → ℤ) (einf : I → ℤ)
    (hefinpm1 : ∀ i : I, ∀ n : ℕ, efin (i, n) = 1 ∨ efin (i, n) = -1)
    (heinfpm1 : ∀ i : I, einf i = 1 ∨ einf i = -1) :
      (∃ x : ℚˣ, ∀ i : I, (∀ n : ℕ, efin (i, n) = atP x (a i) (Nat.nth Nat.Prime n)) ∧
        einf i = atInfty x (a i)) ↔
        ∀ i : I, (∀ᶠ (n : ℕ) in Filter.cofinite, efin (i, n) = 1) ∧
          (einf i * ∏ᶠ (n : ℕ), efin (i, n) = 1) ∧
          ((∀ n : ℕ, ∃ xn : ℚ_[Nat.nth Nat.Prime n], efin (i, n) = hilbertSym xn (a i)) ∧
            ∃ xr : ℝ, einf i = hilbertSym xr (a i)) := by
  constructor
  · intro ⟨x, hx⟩ i
    specialize hx i
    constructor
    · suffices {x_1 | ¬atP (↑x) (↑(a i)) (Nat.nth Nat.Prime x_1) = 1} = {x | ¬efin (i, x) = 1} by
        simp only [Filter.eventually_cofinite]
        rw [← this]
        exact almost_all_one x (a i)
      ext n
      simp only [Set.mem_setOf_eq, ← hx.1]
    · constructor
      · rw [← prod_eq_one x (a i), ← hx.2]
        simp only [mul_eq_mul_left_iff]
        left
        congr
        simp only [hx]
      · constructor
        · intro n
          use x
          rw [hx.1 n]
        · use x
          rw [hx.2]
  · sorry

end hilbertSym
