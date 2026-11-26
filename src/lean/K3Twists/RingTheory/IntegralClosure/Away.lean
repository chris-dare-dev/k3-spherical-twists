/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.ScaleRoots

/-!
# Integrality over `ℤ[1/N]`

For a commutative ring `A` and `N : ℕ`, `integralClosureAway N A` is the subalgebra of the
elements `x` such that `N ^ j * x` is an algebraic integer for some `j`. When `N` is invertible in
`A` these are the elements integral over `ℤ[1/N]`. This file proves that it is integrally closed
in `A`, and the arithmetic step of the S-unit theorem for spectral moduli.

## Main results

* `Polynomial.Monic.isIntegral_of_isIntegral_coeff`: a root of a monic polynomial whose
  coefficients are algebraic integers is an algebraic integer.
* `Polynomial.Monic.mem_integralClosureAway`, `mem_integralClosureAway_of_isIntegral`: a root of a
  monic polynomial with coefficients in `integralClosureAway N A` lies in it; so does an element
  integral over any subalgebra of it.
* `map_mem_integralClosureAway`: ring homomorphisms preserve it.
* `coeff_zero_dvd_pow`: let `α ≠ 0` be a root of a monic `P ∈ ℤ[X]` that is irreducible over `ℚ`.
  If `α⁻¹` is integral over `ℤ[1/N]`, then `P(0)` divides a power of `N`: the norm of `α` is a
  unit of `ℤ[1/N]`. No number field enters: `P` divides `Q.reverse.scaleRoots (N ^ j)` in `ℤ[X]`
  for a monic `Q ∈ ℤ[X]` with `Q(N ^ j α⁻¹) = 0`.
* `isIntegral_mul_of_minpoly_eq`: two elements with the same minimal polynomial over `ℚ` have
  the same integer multiples that are algebraic integers. So a statement "some conjugate of `α`
  is integral over `ℤ[1/N]`" says no less than "`α` is integral over `ℤ[1/N]`".
-/

open Polynomial

section Away

variable (N : ℕ) (A : Type*) [CommRing A]

/-- The elements `x` of `A` such that `N ^ j * x` is an algebraic integer for some `j`. When `N`
is invertible in `A`, these are the elements of `A` integral over `ℤ[1/N]`. -/
def integralClosureAway : Subalgebra ℤ A where
  carrier := {x | ∃ j : ℕ, IsIntegral ℤ ((N : A) ^ j * x)}
  mul_mem' := by
    rintro x y ⟨j, hj⟩ ⟨k, hk⟩
    refine ⟨j + k, ?_⟩
    have : (N : A) ^ (j + k) * (x * y) = ((N : A) ^ j * x) * ((N : A) ^ k * y) := by ring
    rw [this]
    exact hj.mul hk
  one_mem' := ⟨0, by simpa using isIntegral_one⟩
  add_mem' := by
    rintro x y ⟨j, hj⟩ ⟨k, hk⟩
    refine ⟨j + k, ?_⟩
    have hN : IsIntegral ℤ (N : A) := by
      simpa using isIntegral_algebraMap (R := ℤ) (A := A) (x := (N : ℤ))
    have : (N : A) ^ (j + k) * (x + y) =
        (N : A) ^ k * ((N : A) ^ j * x) + (N : A) ^ j * ((N : A) ^ k * y) := by ring
    rw [this]
    exact ((hN.pow k).mul hj).add ((hN.pow j).mul hk)
  zero_mem' := ⟨0, by simpa using isIntegral_zero⟩
  algebraMap_mem' r := ⟨0, by simpa using isIntegral_algebraMap (R := ℤ) (A := A) (x := r)⟩

variable {N A}

lemma mem_integralClosureAway {x : A} :
    x ∈ integralClosureAway N A ↔ ∃ j : ℕ, IsIntegral ℤ ((N : A) ^ j * x) :=
  Iff.rfl

lemma isIntegral_natCast_pow (j : ℕ) : IsIntegral ℤ ((N : A) ^ j) := by
  have hN : IsIntegral ℤ (N : A) := by
    simpa using isIntegral_algebraMap (R := ℤ) (A := A) (x := (N : ℤ))
  exact hN.pow j

/-- A larger power of `N` keeps an integer multiple integral. -/
lemma isIntegral_pow_mul_of_le {x : A} {j J : ℕ} (hj : IsIntegral ℤ ((N : A) ^ j * x))
    (hjJ : j ≤ J) : IsIntegral ℤ ((N : A) ^ J * x) := by
  have : (N : A) ^ J * x = (N : A) ^ (J - j) * ((N : A) ^ j * x) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hjJ]
  rw [this]
  exact (isIntegral_natCast_pow _).mul hj

/-- Integrality over `ℤ[1/n]` passes to `ℤ[1/N]` for every multiple `N` of `n`. -/
lemma integralClosureAway_le_of_dvd {n : ℕ} (h : n ∣ N) :
    integralClosureAway n A ≤ integralClosureAway N A := by
  rintro x ⟨j, hj⟩
  obtain ⟨m, rfl⟩ := h
  refine ⟨j, ?_⟩
  have : ((n * m : ℕ) : A) ^ j * x = (m : A) ^ j * ((n : A) ^ j * x) := by push_cast; ring
  rw [this]
  exact (isIntegral_natCast_pow (N := m) j).mul hj

/-- Algebraic integers lie in `integralClosureAway N A`. -/
lemma mem_integralClosureAway_of_isIntegral_int {x : A} (hx : IsIntegral ℤ x) :
    x ∈ integralClosureAway N A :=
  ⟨0, by simpa using hx⟩

/-- Ring homomorphisms preserve integrality over `ℤ[1/N]`. -/
lemma map_mem_integralClosureAway {B : Type*} [CommRing B] (f : A →+* B) {x : A}
    (hx : x ∈ integralClosureAway N A) : f x ∈ integralClosureAway N B := by
  obtain ⟨j, hj⟩ := hx
  refine ⟨j, ?_⟩
  have := hj.map f.toIntAlgHom
  simpa using this

/-- **Integral coefficients.** A root of a monic polynomial whose coefficients are algebraic
integers is an algebraic integer. -/
theorem Polynomial.Monic.isIntegral_of_isIntegral_coeff {p : A[X]} (hp : p.Monic)
    (hc : ∀ i, IsIntegral ℤ (p.coeff i)) {x : A} (hx : p.eval x = 0) : IsIntegral ℤ x := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact ⟨X, monic_X, Subsingleton.elim _ _⟩
  have hlift : p ∈ Polynomial.lifts (algebraMap (integralClosure ℤ A) A) := by
    rw [lifts_iff_coeff_lifts]
    exact fun n => ⟨⟨p.coeff n, hc n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hlift hp
  have hT : IsIntegral (integralClosure ℤ A) x := ⟨q, hqm, by rw [← eval_map, hq, hx]⟩
  exact isIntegral_trans x hT

/-- **`integralClosureAway N A` is integrally closed in `A`.** A root of a monic polynomial with
coefficients in `integralClosureAway N A` lies in it: if `N ^ J` clears every coefficient, then
`N ^ J x` is a root of `p.scaleRoots (N ^ J)`, whose coefficients are algebraic integers. -/
theorem Polynomial.Monic.mem_integralClosureAway {p : A[X]} (hp : p.Monic)
    (hc : ∀ i, p.coeff i ∈ integralClosureAway N A) {x : A} (hx : p.eval x = 0) :
    x ∈ integralClosureAway N A := by
  choose j hj using hc
  set d := p.natDegree
  set J := ∑ i ∈ Finset.range d, j i
  refine ⟨J, ?_⟩
  have hs : (p.scaleRoots ((N : A) ^ J)).eval ((N : A) ^ J * x) = 0 := by
    have := scaleRoots_eval₂_eq_zero (RingHom.id A) (s := (N : A) ^ J) (r := x)
      (by simpa [eval₂_id] using hx)
    simpa [eval₂_id] using this
  refine ((monic_scaleRoots_iff _).2 hp).isIntegral_of_isIntegral_coeff (fun i => ?_) hs
  rw [coeff_scaleRoots]
  rcases lt_trichotomy i d with hi | rfl | hi
  · have hji : j i ≤ J :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hi)
    have h1 : IsIntegral ℤ ((N : A) ^ J * p.coeff i) := isIntegral_pow_mul_of_le (hj i) hji
    obtain ⟨k, hk⟩ : ∃ k, d - i = k + 1 := ⟨d - i - 1, by omega⟩
    have : p.coeff i * ((N : A) ^ J) ^ (d - i) =
        ((N : A) ^ J * p.coeff i) * ((N : A) ^ J) ^ k := by
      rw [hk, pow_succ]
      ring
    rw [this]
    exact h1.mul ((isIntegral_natCast_pow J).pow _)
  · rw [Nat.sub_self, pow_zero, mul_one, hp.coeff_natDegree]
    exact isIntegral_one
  · rw [coeff_eq_zero_of_natDegree_lt hi, zero_mul]
    exact isIntegral_zero

/-- An element integral over a subalgebra of `integralClosureAway N A` lies in
`integralClosureAway N A`. -/
theorem mem_integralClosureAway_of_isIntegral {R : Subalgebra ℤ A}
    (hR : R ≤ integralClosureAway N A) {x : A} (hx : IsIntegral R x) :
    x ∈ integralClosureAway N A := by
  obtain ⟨p, hpm, hpx⟩ := hx
  refine (hpm.map (algebraMap R A)).mem_integralClosureAway (fun i => ?_) (by rwa [eval_map])
  rw [coeff_map]
  exact hR (p.coeff i).2

end Away

section Norm

variable {K : Type*} [Field K] [CharZero K]

/-- **The arithmetic core of the S-unit theorem.** Let `α ≠ 0` be a root of a monic `P ∈ ℤ[X]`
irreducible over `ℚ`, and let `N ^ j α⁻¹` be an algebraic integer, `N ≠ 0`. Then `P(0)` divides a
power of `N`; up to sign `P(0)` is the norm of `α`, so the norm is a unit of `ℤ[1/N]`.

If `Q ∈ ℤ[X]` is monic with `Q(N ^ j α⁻¹) = 0`, then `α` is a root of
`H = Q.reverse.scaleRoots (N ^ j)`, so `P ∣ H` in `ℤ[X]` (`P` is the minimal polynomial of `α`
over `ℚ`, and Gauss's lemma for the monic `P`), and `H(0) = N ^ (j deg Q)`. -/
theorem coeff_zero_dvd_pow {P : ℤ[X]} (hPm : P.Monic)
    (hPirr : Irreducible (P.map (Int.castRingHom ℚ))) {α : K} (hα0 : α ≠ 0)
    (hα : aeval α P = 0) {N : ℕ} (hN : N ≠ 0) (hinv : α⁻¹ ∈ integralClosureAway N K) :
    ∃ k, P.coeff 0 ∣ (N : ℤ) ^ k := by
  obtain ⟨j, Q, hQm, hQ⟩ := hinv
  set β : K := (N : K) ^ j * α⁻¹ with hβdef
  have hNc : (N : K) ≠ 0 := by exact_mod_cast hN
  have hβ0 : β ≠ 0 := mul_ne_zero (pow_ne_zero _ hNc) (inv_ne_zero hα0)
  letI : Invertible β := invertibleOfNonzero hβ0
  have h1 : aeval (⅟β) Q.reverse = 0 := by
    rw [aeval_def, eval₂_reverse_eq_zero_iff]
    exact hQ
  set H : ℤ[X] := Q.reverse.scaleRoots ((N : ℤ) ^ j) with hH
  have h2 : aeval α H = 0 := by
    have h3 := scaleRoots_aeval_eq_zero (r := (N : ℤ) ^ j) h1
    have h4 : algebraMap ℤ K ((N : ℤ) ^ j) * ⅟β = α := by
      rw [invOf_eq_inv, hβdef, mul_inv, inv_inv, map_pow, ← mul_assoc]
      simp only [algebraMap_int_eq, eq_intCast, Int.cast_natCast]
      rw [mul_inv_cancel₀ (pow_ne_zero _ hNc), one_mul]
    rwa [h4] at h3
  have hmin : P.map (Int.castRingHom ℚ) = minpoly ℚ α :=
    minpoly.eq_of_irreducible_of_monic hPirr
      (by rw [← algebraMap_int_eq, aeval_map_algebraMap]; exact hα) (hPm.map _)
  have hdvd : P.map (Int.castRingHom ℚ) ∣ H.map (Int.castRingHom ℚ) := by
    rw [hmin]
    apply minpoly.dvd
    rw [← algebraMap_int_eq, aeval_map_algebraMap]
    exact h2
  rw [map_dvd_map _ (fun a b h => by simpa using h) hPm] at hdvd
  obtain ⟨S, hS⟩ := hdvd
  refine ⟨j * Q.reverse.natDegree, ?_⟩
  have hc : H.coeff 0 = (N : ℤ) ^ (j * Q.reverse.natDegree) := by
    rw [hH, coeff_scaleRoots, coeff_zero_reverse, hQm.leadingCoeff, one_mul, Nat.sub_zero,
      pow_mul]
  rw [← hc, hS, mul_coeff_zero]
  exact dvd_mul_right _ _

/-- **One conjugate is as good as any.** If `α` and `β` have the same minimal polynomial over
`ℚ` and `k β` is an algebraic integer for an integer `k`, then so is `k α`. -/
theorem isIntegral_mul_of_minpoly_eq {α β : K} (h : minpoly ℚ α = minpoly ℚ β) (k : ℤ)
    (hβ : IsIntegral ℤ ((k : K) * β)) : IsIntegral ℤ ((k : K) * α) := by
  obtain ⟨p, hpm, hp⟩ := hβ
  refine ⟨p, hpm, ?_⟩
  rw [← aeval_def] at hp ⊢
  set q : ℚ[X] := (p.map (Int.castRingHom ℚ)).comp (C (k : ℚ) * X) with hq
  have hcomp : ∀ y : K, aeval y q = aeval ((k : K) * y) p := by
    intro y
    rw [hq, aeval_comp, ← algebraMap_int_eq, aeval_map_algebraMap]
    simp
  have hqβ : aeval β q = 0 := by rw [hcomp]; exact hp
  have hqα : aeval α q = 0 := by
    rw [← minpoly.dvd_iff, h, minpoly.dvd_iff]
    exact hqβ
  rwa [hcomp] at hqα

end Norm
