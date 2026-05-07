module

public import HassePrinciple.QuadraticForm.HilbertSymbol
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.LinearAlgebra.QuadraticForm.Radical

public import Mathlib.Data.Fin.Basic

@[expose] public section

namespace Module.Basis

-- TODO: move to a different file

def IsContiguous {ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (b b' : Basis ι R M) : Prop :=
  ∃ (i j : ι), b i = b' j

variable {k : Type*} [Field k] [Invertible (2 : k)]
  {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  {Q : QuadraticForm k V}

structure Chain (Q : QuadraticForm k V) (b b' : Basis (Fin (finrank k V)) k V) : Type _ where
  m : ℕ
  basis : Fin (m + 1) → Basis (Fin (finrank k V)) k V
  basis_ortho (i : Fin (m + 1)) : Q.associated.IsOrthoᵢ (basis i)
  basis_zero : basis 0 = b
  basis_m_sub_one : basis ⟨m, lt_add_one m⟩ = b'
  basis_isContiguous {i : ℕ} (hi : i < m) : (basis ⟨i, by omega⟩).IsContiguous (basis ⟨i, by omega⟩)


-- Used in the proof of case (iii) of Theorem 2.
private lemma exists_const (hdim : 3 ≤ finrank k V) (hQ : Q.Nondegenerate)
    {b b' : Basis (Fin (finrank k V)) k V} (hb : Q.associated.IsOrthoᵢ b)
    (hb' : Q.associated.IsOrthoᵢ b') :
    ∃ (x : k), Q (b' ⟨1, by omega⟩ + x • b' ⟨2, by omega⟩) ≠ 0 ∧
    ((Q.restrict (Submodule.span k {b ⟨1, by omega⟩,
      b' ⟨1, by omega⟩ + x • b' ⟨2, by omega⟩}))).Nondegenerate := by
  sorry

-- Theorem 2 in Section IV.1. Depends on Proposition 2, which is probably in Mathlib.
def chain_of_nondegenerate (hdim : 3 ≤ finrank k V) (hQ : Q.Nondegenerate)
    {b b' : Basis (Fin (finrank k V)) k V} (hb : Q.associated.IsOrthoᵢ b)
    (hb' : Q.associated.IsOrthoᵢ b') :
    Chain Q b b' := sorry

/-   {B : LinearMap.BilinForm k V}

structure Chain (B : LinearMap.BilinForm k V) (b b' : Basis (Fin (finrank k V)) k V) : Type u where
  m : ℕ
  basis : Fin (m + 1) → Basis (Fin (finrank k V)) k V
  basis_ortho (i : Fin (m + 1)) : B.IsOrthoᵢ (basis i)
  basis_zero : basis 0 = b
  basis_m_sub_one : basis ⟨m, lt_add_one m⟩ = b'
  basis_isContiguous {i : ℕ} (hi : i < m) : (basis ⟨i, by omega⟩).IsContiguous (basis ⟨i, by omega⟩)


-- Used in the proof of case (iii) of Theorem 2.
private lemma foo (hB : B.IsSymm) (hB' : B.Nondegenerate)
    (hB3 : 3 ≤ finrank k V) {b b' : Basis (Fin (finrank k V)) k V} (hb : B.IsOrthoᵢ b)
    (hb' : B.IsOrthoᵢ b') :
    ∃ (x : k), B (b ⟨1, by sorry⟩ + x • b ⟨2, by sorry⟩) ≠ 0 := sorry

-- Theorem 2 in Section IV.1. Depends on Proposition 2, which is probably in Mathlib.
def chain_of_nondegenerate (hB : B.IsSymm) (hB' : B.Nondegenerate)
    (hB3 : 3 ≤ finrank k V) {b b' : Basis ι k V} (hb : B.IsOrthoᵢ b) (hb' : B.IsOrthoᵢ b') :
    Chain B b b' := sorry -/

end Module.Basis

namespace QuadraticForm

variable {k : Type*} [Field k] [Invertible (2 : k)] --[CharZero k]

-- Let `V` be a `k`-vector space.
variable {V : Type*} [AddCommGroup V] [Module k V]

-- Let `Q` be a quadratic form on `V`.
variable (Q : QuadraticForm k V)

noncomputable def HasseMinkoskiInvariantAux {n : ℕ} (w : Fin n → kˣ) : ℤˣ :=
  ∏ p : Fin n × Fin n with p.1 < p.2, HilbertSymbol (w p.1) (w p.2)

lemma HasseMinkoskiInvariant_aux.eq_of_equivalent {n : ℕ} {w w' : Fin n → kˣ}
    (h : (QuadraticMap.weightedSumSquares k w).Equivalent (QuadraticMap.weightedSumSquares k w')) :
    HasseMinkoskiInvariantAux w = HasseMinkoskiInvariantAux w' := by
  sorry

variable [FiniteDimensional k V]

example {Q : QuadraticForm k V} (h : Q.Nondegenerate) :
    LinearMap.SeparatingLeft (QuadraticMap.associated Q) := by
  simp only [← QuadraticMap.nondegenerate_associated_iff] at h
  exact h.1

noncomputable def HasseMinkoskiInvariant {Q : QuadraticForm k V}
    (hQ : LinearMap.SeparatingLeft (QuadraticMap.associated Q)) : ℤˣ :=
  HasseMinkoskiInvariantAux (equivalent_weightedSumSquares_units_of_nondegenerate' Q hQ).choose

namespace HasseMinkoskiInvariant

variable {Q Q' : QuadraticForm k V} (hQ : LinearMap.SeparatingLeft Q.associated)

lemma _root_.LinearMap.separatingLeft_of_equivalent {R M M' N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup M'] [Module R M] [Module R M'] [AddCommGroup N] [Module R N]
    [Invertible (2 : R)] {Q : QuadraticMap R M N} {Q' : QuadraticMap R M' N} (h : Q.Equivalent Q')
    (hQ : LinearMap.SeparatingLeft Q.associated) :
    LinearMap.SeparatingLeft Q'.associated := by
  sorry

lemma eq_of_equivalent_weightedSumSquares {n : ℕ} {w : Fin n → kˣ}
    (h : Q.Equivalent (QuadraticMap.weightedSumSquares k w)) :
    HasseMinkoskiInvariant hQ =
      HasseMinkoskiInvariant (LinearMap.separatingLeft_of_equivalent h hQ) := by
  sorry

lemma eq_of_equivalent (h : Q.Equivalent Q') :
    HasseMinkoskiInvariant hQ =
      HasseMinkoskiInvariant (LinearMap.separatingLeft_of_equivalent h hQ) := by
  sorry

lemma eq_one_or_neg_one :
    HasseMinkoskiInvariant hQ = 1 ∨ HasseMinkoskiInvariant hQ = 1 := sorry

end HasseMinkoskiInvariant

end QuadraticForm

#lint
