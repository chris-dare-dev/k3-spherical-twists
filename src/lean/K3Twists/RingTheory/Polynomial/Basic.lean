/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Multiplying a subspace of polynomials by `X`

Binary forms of degree `n` in `s, t` correspond to polynomials of degree at most `n` in
`X = t/s`: multiplication by `s` becomes the inclusion and multiplication by `t` becomes
multiplication by `X`. Under this correspondence the statement that a nonzero subspace `J` of
binary forms of one degree has `dim(sJ + tJ) ≥ dim J + 1` becomes `dim(J + XJ) ≥ dim J + 1`,
which `finrank_lt_finrank_sup_map_mulLeft_X` proves for every nonzero finite-dimensional
subspace `J` of `K[X]`: multiplication by `X` raises the largest degree in `J`
(`not_map_mulLeft_X_le`).

This is the linear algebra in the stability of the section-evaluation objects at a wall of
pairing two. There `Q_d` is the extension of `B ⊗ K[s, t]_{d-1}` by `A ⊗ K[s, t]_d` with class
`α ⊗ s + γ ⊗ t`, for a basis `α, γ` of `Ext¹(B, A)`. A subobject of `Q_d` that meets the copies
of `A` in `I` and maps onto `J` in the copies of `B` has `sJ + tJ ⊆ I`, so `dim I ≥ dim J + 1`,
and its fraction of `B` is at most `j/(2j + 1)` for `j = dim J`.
-/

namespace Polynomial

variable {K : Type*} [Field K]

/-- A finite-dimensional subspace of `K[X]` has bounded degree. -/
theorem exists_le_degreeLE (J : Submodule K K[X]) [Module.Finite K J] :
    ∃ N : ℕ, J ≤ degreeLE K N := by
  obtain ⟨S, hS⟩ := (Module.Finite.iff_fg.mp inferInstance : J.FG)
  refine ⟨S.sup natDegree, ?_⟩
  rw [← hS, Submodule.span_le]
  intro f hf
  exact mem_degreeLE.mpr (degree_le_natDegree.trans (by exact_mod_cast Finset.le_sup hf))

/-- **Multiplication by `X` leaves no nonzero finite-dimensional subspace invariant**: it would
raise the degree of a nonzero element without bound. -/
theorem not_map_mulLeft_X_le (J : Submodule K K[X]) [Module.Finite K J] (hJ : J ≠ ⊥) :
    ¬J.map (LinearMap.mulLeft K X) ≤ J := by
  intro hX
  obtain ⟨N, hN⟩ := exists_le_degreeLE J
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  have hpow : ∀ n : ℕ, X ^ n * f ∈ J := by
    intro n
    induction n with
    | zero => simpa using hf
    | succ n ih =>
      rw [pow_succ', mul_assoc]
      exact hX (Submodule.mem_map_of_mem ih)
  have hdeg := natDegree_le_of_degree_le (mem_degreeLE.mp (hN (hpow (N + 1))))
  rw [natDegree_X_pow_mul (N + 1) hf0] at hdeg
  omega

/-- **`dim(J + XJ) ≥ dim J + 1`** for a nonzero finite-dimensional subspace `J` of `K[X]`: the
dehomogenized form of `dim(sJ + tJ) ≥ dim J + 1` for binary forms. -/
theorem finrank_lt_finrank_sup_map_mulLeft_X (J : Submodule K K[X]) [Module.Finite K J]
    (hJ : J ≠ ⊥) :
    Module.finrank K J < Module.finrank K ↥(J ⊔ J.map (LinearMap.mulLeft K X)) :=
  Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne le_sup_left fun h =>
    not_map_mulLeft_X_le J hJ (le_sup_right.trans_eq h.symm))

end Polynomial
