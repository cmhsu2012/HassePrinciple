/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/

module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.NumberTheory.Padics.Hensel
public import Mathlib.Algebra.Polynomial.Basic

/-! # Auxiliary result about padic numbers. -/

@[expose] public section

/-- An indexed family `f : σ → M` of elements is called primitive if at least one of the
  elements in the image is a unit. -/
def Function.IsPrimitive {M σ : Type*} [Monoid M] (f : σ → M) : Prop :=
   ∃ (s : σ), IsUnit (f s)

namespace Padic

variable {p : ℕ} [Fact (Nat.Prime p)] (x : ℚ_[p]ˣ)

/-- Given a nonzero padic number `x`, the norm of `x` times `p` raised to the negative of its
valuation equals one. -/
lemma norm_mul_pow_neg_valuation_eq_one : ‖(x : ℚ_[p]) * p ^ (- valuation x.val)‖ = 1 := by
  simp[norm_eq_zpow_neg_valuation]
  field_simp
  rw [div_self_eq_one₀]
  apply zpow_ne_zero
  norm_cast
  exact NeZero.out

/-- Given a nonzero padic number `x`, the unit part of `x` is defined as the element `u` in `ℤ_[p]ˣ`
such that `u = x(p^{-v(x)})` -/
noncomputable def unitPart : ℤ_[p]ˣ :=
  PadicInt.mkUnits (norm_mul_pow_neg_valuation_eq_one x)

/-- The p-adic valuation of a p-adic unit in `Z_[p]` is 0 -/
lemma unit_val_zero (a : ℤ_[p]ˣ) : (a : ℤ_[p]).valuation = 0 := by
  have h₂ : (a : ℤ_[p]) ≠ 0 := by
    exact Units.ne_zero a
  have h₁ : ‖(a : ℤ_[p])‖ = 1 := by
    exact PadicInt.norm_units a
  rw[PadicInt.norm_eq_zpow_neg_valuation h₂] at h₁
  rw[zpow_eq_one_iff_right₀] at h₁
  · exact Eq.symm ((fun {a b} ↦ Int.negSucc_add_one_eq_neg_ofNat_iff.mp) (id (Eq.symm h₁)))
  · exact Nat.cast_nonneg' p
  by_contra
  rw[Nat.cast_eq_one] at this
  have h₃ : p ≠ 1 := Nat.Prime.ne_one Fact.out
  contradiction

/-- The map that sends a padic integer to its unit part in ℤ_[p]ˣ is the natural inclusion. -/
lemma map_unitPart (a : ℤ_[p]ˣ) :
    unitPart (Units.map (algebraMap ℤ_[p] ℚ_[p]) a) = a := by
  unfold unitPart
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe, PadicInt.algebraMap_apply, PadicInt.valuation_coe,
  PadicInt.val_mkUnits]
  have h₁ : ‖(a : ℤ_[p])‖ = 1 := by
    exact PadicInt.norm_units a
  have h₂ : (a : ℤ_[p]) ≠ 0 := by
    exact Units.ne_zero a
  have h₃ : (a : ℤ_[p]).valuation = 0 := unit_val_zero a
  simp[h₃]

/-- For an odd prime `p` different from 2, the element `p` in ℤ_[2]ˣ is defined. -/
noncomputable abbrev p2 (hp : p ≠ 2) : ℤ_[2]ˣ :=
  PadicInt.mkUnits (Padic.norm_natCast_eq_one_iff.mpr
    ((Nat.coprime_primes Nat.prime_two Fact.out).mpr hp.symm))

/-- If `p` is a prime, `x, y, z in ℚ_[p]` satisfy `z ^ 2 - p * x ^ 2 - v * y ^ 2`, with `v` nonzero,
and not all of `x, y, z` are zero, then there exists a nontrivial solution to the same equation with
`z', y',` and `x'` in `ℤ_[p]`, and at least one is a unit -/
lemma lift_solutions_to_int {v : ℚ_[p]ˣ} {x y z : ℚ_[p]}
    (hnontriv : (x,y,z) ≠ (0,0,0)) (hsol : z ^ 2 - p * x ^ 2 - v * y ^ 2 = 0) :
    ∃ z' y' x' : ℤ_[p],
      (z' : ℚ_[p]) ^ 2 - p * (x' : ℚ_[p]) ^ 2 - v * (y' : ℚ_[p]) ^ 2 = 0
      ∧ (IsUnit z' ∨ IsUnit y' ∨ IsUnit x') := by
  wlog h_x_max : (‖y‖ ≤ ‖x‖ ∧ ‖z‖ ≤ ‖x‖)
  · sorry
  · have h_x_ne_zero : x ≠ 0 := by -- prove that in this case, x ≠ 0
      have h_norm_x_ne_zero : 0 < ‖x‖ := by
        by_cases (z ≠ 0)
        · have hz : 0 < ‖z‖ := by
            expose_names
            exact norm_pos_iff.mpr h
          apply lt_of_lt_of_le hz h_x_max.2
        · by_cases (y ≠ 0)
          · have hy : 0 < ‖y‖ := by
              expose_names
              exact norm_pos_iff.mpr h_1
            apply lt_of_lt_of_le hy h_x_max.1
          · have hx : x ≠ 0 := by
              by_contra
              have htriv : (x,y,z) = (0,0,0) := by
                simp only [Prod.mk.injEq]
                constructor
                · exact this
                · constructor
                  · expose_names
                    simp only [ne_eq, not_not] at h_1
                    exact h_1
                  · expose_names
                    simp only [ne_eq, not_not] at h
                    exact h
              contradiction -- completes the proof that x ≠ 0 (in this case!)
            exact norm_pos_iff.mpr hx -- completes the proof that 0 < ‖x‖
      exact norm_pos_iff.mp h_norm_x_ne_zero -- completes the proof that x ≠ 0
    let x' := x * p ^ (-x.valuation)
    let y' := y * p ^ (-x.valuation)
    let z' := z * p ^(-x.valuation)
    have hx'unit : ‖x'‖ = 1 := by
      unfold x'
      have := norm_mul_pow_neg_valuation_eq_one (Units.mk0 x h_x_ne_zero)
      simp only [Units.val_mk0, zpow_neg, norm_mul,
      norm_inv, norm_p_zpow, inv_inv] at this
      simp only [zpow_neg, norm_mul, norm_inv, norm_p_zpow, inv_inv]
      exact this
    have hx' : ‖x'‖ ≤ 1 := by
      exact Std.le_of_eq hx'unit
    have hy' : ‖y'‖ ≤ 1 := by
      unfold y'
      simp only [zpow_neg, norm_mul, norm_inv, norm_p_zpow, inv_inv]
      have hxinvval : ↑p ^ x.valuation = ‖x‖⁻¹ := by
        have := norm_mul_pow_neg_valuation_eq_one (Units.mk0 x h_x_ne_zero)
        simp only [Units.val_mk0, zpow_neg, norm_mul,
        norm_inv, norm_p_zpow, inv_inv] at this
        rw[mul_eq_one_iff_inv_eq₀] at this
        · exact Real.ext_cauchy (congrArg Real.cauchy (id (Eq.symm this)))
        · simp only [ne_eq, norm_eq_zero]
          exact h_x_ne_zero
      rw[hxinvval]
      rw[mul_inv_le_iff₀]
      · simp only [one_mul]
        exact h_x_max.1
      · simp only [norm_pos_iff, ne_eq]
        exact h_x_ne_zero
    have hz' : ‖z'‖ ≤ 1 := by
      unfold z'
      simp only [zpow_neg, norm_mul, norm_inv, norm_p_zpow, inv_inv]
      have hxinvval : ↑p ^ x.valuation = ‖x‖⁻¹ := by
        have := norm_mul_pow_neg_valuation_eq_one (Units.mk0 x h_x_ne_zero)
        simp only [Units.val_mk0, zpow_neg, norm_mul,
        norm_inv, norm_p_zpow, inv_inv] at this
        rw[mul_eq_one_iff_inv_eq₀] at this
        · exact Real.ext_cauchy (congrArg Real.cauchy (id (Eq.symm this)))
        · simp only [ne_eq, norm_eq_zero]
          exact h_x_ne_zero
      rw[hxinvval]
      rw[mul_inv_le_iff₀]
      · simp only [one_mul]
        exact h_x_max.2
      · simp only [norm_pos_iff, ne_eq]
        exact h_x_ne_zero
    have hnewsol : ((z' : ℚ_[p])^2 - p * (x' : ℚ_[p])^2
      - v * (y' : ℚ_[p])^2 = 0) := by
      unfold x' y' z'
      grind
    let z'' : ℤ_[p] := ⟨z',hz'⟩
    let y'' : ℤ_[p] := ⟨y',hy'⟩
    let x'' : ℤ_[p] := ⟨x',hx'⟩
    use z'', y'', x''
    constructor
    · exact hnewsol
    · right
      right
      exact PadicInt.isUnit_iff.mpr hx'unit

--better name?
/-- If `p` is a prime, `x, y, z in ℚ_[p]` satisfy `z ^ 2 - p * x ^ 2 - v * y ^ 2`, with `v` nonzero,
and not all of `x, y, z` are zero, then there exists a nontrivial solution to the same equation with
`z', y'` units in `ℤ_[p]ˣ` and `x'` in `ℤ_[p]`. -/
lemma exists_nontrivial_zero {v : (ℚ_[p])ˣ} {x y z : ℚ_[p]}
    (hnontriv : (x, y, z) ≠ (0, 0, 0)) (hsol : z ^ 2 - p * x ^ 2 - v * y ^ 2 = 0) :
    ∃ z' y' : ℤ_[p]ˣ, ∃ x' : ℤ_[p],
      (z' : ℚ_[p]) ^ 2 - p * (x' : ℚ_[p]) ^ 2 - v * (y' : ℚ_[p]) ^ 2 = 0 := by
  sorry

lemma common_root_tfae {σ ι : Type*} {f : ι → MvPolynomial σ ℤ_[p]}
    (hf : ∀ i, (f i).IsHomogeneous (f i).totalDegree) :
    List.TFAE [∃ (z : σ → ℚ_[p]), (∃ s, z s ≠ 0)  ∧ (∀ i : ι, (f i).aeval z = 0),
      ∃ (z : σ → ℤ_[p]), z.IsPrimitive ∧ ∀ i : ι, (f i).aeval z = 0,
      ∀ {n : ℕ} (hn : 1 ≤ n),  ∃ (z : σ → ZMod (p ^ n)), z.IsPrimitive ∧
        ∀ i : ι, ((f i).map (PadicInt.toZModPow n)).aeval z = 0] := by
  sorry

end Padic



/-! # Applications and Multivariable Hensel's Lemma. -/

@[expose] public section


namespace Polynomial

/-- An element in ℤ_p (p odd) is a square if its reduction modulo p is a square. -/
lemma squares_in_Zp {p : ℕ} [Fact (Nat.Prime p)] (hodd : p ≠ 2) (m : ℤ_[p]) (n : ℕ)
    (hmod : m.zmodRepr ≡ n ^ 2 [MOD p]) : ∃ x : ℤ_[p], m = x ^ 2 := by
  let F : ℤ_[p][X] := X ^ 2 - C m
  sorry

/-- An element in ℤ_2 is a square if its reduction modulo 8 is a square. -/
lemma squares_in_Z2 (m : ℤ_[2]) (n : ℕ)
    (hmod : m.zmodRepr ≡ n ^ 2 [MOD 8]) : ∃ x : ℤ_[2], m = x^2 := by sorry

end Polynomial


namespace PadicInt

/-! ## Multivariable Hensel's Lemma -/


/-- Serre's generalization of Hensel's lemma to a multivariable polynomial over ℤ_[p]. If a
polynomial f in m variables has a solution a modulo p^n, and a is a zero modulo p^k of one of its
partial derivatives, with 0 < 2k < n, then there exists a solution in ℤ_[p], which is congruent to
a modulo p^{n-k}. -/
theorem multivariable_hensel {p : ℕ} [Fact (Nat.Prime p)] {m : ℕ}
    {f : MvPolynomial (Fin m) ℤ_[p]} {a : Fin m → ℤ_[p]}
    {n k : ℤ} (hk : 0 < 2 * k ∧ 2 * k < n) {j : Fin m}
    (hF : n ≤ valuation (MvPolynomial.aeval a f))
    (hJ : valuation (MvPolynomial.aeval a (MvPolynomial.pderiv j f)) = k) :
      ∃ (z : Fin m → ℤ_[p]), (MvPolynomial.aeval z f = 0) ∧
        ∀ i, n - k ≤ valuation (z i - a i) := by
  sorry

/-- Same theorem, in terms of norms. TODO: Keep one. -/
theorem multivariable_hensel' {p : ℕ} [Fact (Nat.Prime p)] {m : ℕ}
    {f : MvPolynomial (Fin m) ℤ_[p]} {a : Fin m → ℤ_[p]}
    {n k : ℤ} (hk : 0 < 2 * k ∧ 2 * k < n) {j : Fin m}
    (hF : ‖(MvPolynomial.aeval a) f‖ ≤ p ^ (-n))
    (hJ : ‖(MvPolynomial.aeval a) (MvPolynomial.pderiv j f)‖ = p ^ (-k)) :
      ∃ (z : Fin m → ℤ_[p]), (MvPolynomial.aeval z f = 0) ∧ ∀ i, ‖z i - a i‖ < p ^ (-n + k) := by
  sorry

end PadicInt
