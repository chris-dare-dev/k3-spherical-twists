/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.RingTheory.IntegralClosure.Away
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Specialization of a finitely generated subring of a field of characteristic zero

`exists_specialization`: for a finitely generated subring `R` of a field `K` of characteristic
zero there is `N > 0` such that every element of `K` that is algebraic over `ℚ` and integral over
`R` is integral over `ℤ[1/N]`: some `N ^ j * α` is an algebraic integer. One `N` serves every `α`.

## Proof

Let `A = ℚ[R] ⊆ K` and let `𝔪` be a maximal ideal of `A`. By Zariski's lemma (Mathlib's
`finite_of_finite_type_of_isJacobsonRing`) the field `A/𝔪` is finite over `ℚ`, so one `N` clears
the denominators of the images of the finitely many generators of `R`. For `α` algebraic over `ℚ`
and integral over `R`, the ring `A[α]` is integral over `A`, so a maximal ideal `Q` of `A[α]` lies
over `𝔪` (lying over, `Ideal.exists_ideal_over_maximal_of_isIntegral`). In the field `A[α]/Q` the
image of `R` is integral over `ℤ[1/N]`, hence so is the image of `α`. Finally `ℚ[α]` is a field,
so a polynomial in `N ^ j α` that vanishes in `A[α]/Q` vanishes in `K`, and the integrality comes
back to `α`.

The classical argument through a transcendence basis `t` of `Frac R` (an `f ∈ ℤ[t]` with the
generators integral over `ℤ[t, 1/f]`, then a specialization of `t` at an integer point with
`f ≠ 0`) is not used.

`exists_specialization_of_isAlgebraic` treats generators algebraic over `ℚ`. There `N` is a
common denominator of the generators and no Zariski lemma is needed, and the conclusion holds for
every `α` integral over `R`.

## Main results

* `adjoin_le_integralClosureAway`: generators algebraic over `ℚ` have a common `N`.
* `exists_specialization_of_isAlgebraic`: the case of algebraic generators.
* `exists_specialization`: the general case.
-/

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- An element of a field algebraic over `ℚ` is integral over `ℤ[1/n]` for some `n > 0`. -/
lemma exists_pos_mem_integralClosureAway {L : Type*} [Field L] [Algebra ℚ L] {x : L}
    (hx : IsAlgebraic ℚ x) : ∃ n : ℕ, 0 < n ∧ x ∈ integralClosureAway n L := by
  have hxℤ : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ L).2 hx
  obtain ⟨y, hy0, hy⟩ := hxℤ.exists_integral_multiple
  rw [zsmul_eq_mul] at hy
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg y
  · exact ⟨m, by omega, 1, by simpa using hy⟩
  · exact ⟨m, by omega, 1, by simpa using hy.neg⟩

/-- **Generators algebraic over `ℚ`.** For a finite set `s` of elements of `K` algebraic over `ℚ`
there is `N > 0` with `ℤ[s]` inside `integralClosureAway N K`: a common denominator. -/
theorem adjoin_le_integralClosureAway (s : Finset K) (hs : ∀ x ∈ s, IsAlgebraic ℚ x) :
    ∃ N : ℕ, 0 < N ∧ Algebra.adjoin ℤ (s : Set K) ≤ integralClosureAway N K := by
  classical
  have h : ∀ x ∈ s, ∃ n : ℕ, 0 < n ∧ x ∈ integralClosureAway n K :=
    fun x hx => exists_pos_mem_integralClosureAway (hs x hx)
  choose! n hn0 hn using h
  exact ⟨∏ x ∈ s, n x, Finset.prod_pos hn0, Algebra.adjoin_le fun x hx =>
    integralClosureAway_le_of_dvd (Finset.dvd_prod_of_mem n hx) (hn x hx)⟩

/-- **Specialization, algebraic generators.** If `R = ℤ[s]` for a finite set `s` of elements of
`K` algebraic over `ℚ`, there is `N > 0` such that every element of `K` integral over `R` is
integral over `ℤ[1/N]`. -/
theorem exists_specialization_of_isAlgebraic (s : Finset K) (hs : ∀ x ∈ s, IsAlgebraic ℚ x) :
    ∃ N : ℕ, 0 < N ∧ ∀ α : K, IsIntegral (Algebra.adjoin ℤ (s : Set K)) α →
      α ∈ integralClosureAway N K := by
  obtain ⟨N, hN, hle⟩ := adjoin_le_integralClosureAway s hs
  exact ⟨N, hN, fun α hα => mem_integralClosureAway_of_isIntegral hle hα⟩

/-- An element of `K` integral over a subring `R` is integral over any subalgebra `A ⊇ R` over
`ℚ`. -/
lemma isIntegral_of_le_of_isIntegral {R : Subalgebra ℤ K} {A : Subalgebra ℚ K}
    (hRA : ∀ x ∈ R, x ∈ A) {α : K} (hα : IsIntegral R α) : IsIntegral A α := by
  obtain ⟨p, hpm, hp⟩ := hα
  let incl : R →+* A :=
    { toFun := fun r => ⟨r, hRA r r.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  refine ⟨p.map incl, hpm.map incl, ?_⟩
  rw [eval₂_map]
  exact hp

/-- **Specialization.** For a finitely generated subring `R` of a field `K` of characteristic
zero there is `N > 0` such that every `α ∈ K` algebraic over `ℚ` and integral over `R` is integral
over `ℤ[1/N]`: some `N ^ j * α` is an algebraic integer. -/
theorem exists_specialization (R : Subalgebra ℤ K) (hR : R.FG) :
    ∃ N : ℕ, 0 < N ∧ ∀ α : K, IsAlgebraic ℚ α → IsIntegral R α →
      α ∈ integralClosureAway N K := by
  classical
  obtain ⟨s, rfl⟩ := hR
  set R := Algebra.adjoin ℤ (s : Set K) with hR
  -- `A = ℚ[s]`, a finitely generated `ℚ`-algebra, and a maximal ideal `𝔪` of it.
  set A : Subalgebra ℚ K := Algebra.adjoin ℚ (s : Set K) with hA
  haveI : Algebra.FiniteType ℚ A :=
    (Subalgebra.fg_iff_finiteType A).1 (Subalgebra.fg_adjoin_finset s)
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal A
  letI : Field (A ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  haveI : Module.Finite ℚ (A ⧸ 𝔪) := finite_of_finite_type_of_isJacobsonRing ℚ (A ⧸ 𝔪)
  haveI : Algebra.IsAlgebraic ℚ (A ⧸ 𝔪) := Algebra.IsAlgebraic.of_finite ℚ (A ⧸ 𝔪)
  have hsA : ∀ x ∈ s, x ∈ A := fun x hx => Algebra.subset_adjoin hx
  have hRA : ∀ x ∈ R, x ∈ A := by
    intro x hx
    have : R ≤ A.restrictScalars ℤ := Algebra.adjoin_le fun y hy => Algebra.subset_adjoin hy
    exact this hx
  -- one denominator for the images of the generators in the number field `A/𝔪`
  have hgen : ∀ x (hx : x ∈ s), ∃ n : ℕ, 0 < n ∧
      Ideal.Quotient.mk 𝔪 ⟨x, hsA x hx⟩ ∈ integralClosureAway n (A ⧸ 𝔪) :=
    fun x hx => exists_pos_mem_integralClosureAway (Algebra.IsAlgebraic.isAlgebraic _)
  choose! n hn0 hn using hgen
  set N : ℕ := ∏ x ∈ s, n x with hNdef
  have hgenN : ∀ x (hx : x ∈ s),
      Ideal.Quotient.mk 𝔪 ⟨x, hsA x hx⟩ ∈ integralClosureAway N (A ⧸ 𝔪) := fun x hx =>
    integralClosureAway_le_of_dvd (Finset.dvd_prod_of_mem n hx) (hn x hx)
  refine ⟨N, Finset.prod_pos hn0, fun α hαalg hαint => ?_⟩
  -- `S = A[α]`, integral over `A`, and a maximal ideal `Q` of `S` over `𝔪`.
  have hαA : IsIntegral A α := isIntegral_of_le_of_isIntegral hRA hαint
  set S : Subalgebra A K := Algebra.adjoin A {α} with hS
  haveI : Algebra.IsIntegral A S :=
    Algebra.IsIntegral.adjoin (fun x hx => by rw [Set.mem_singleton_iff.1 hx]; exact hαA)
  have hinj : Function.Injective (algebraMap A S) := by
    intro a b h
    exact Subtype.ext (by simpa using congrArg Subtype.val h)
  obtain ⟨Q, hQ, hQ𝔪⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := S) 𝔪
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le)
  letI : Field (S ⧸ Q) := Ideal.Quotient.field Q
  set π : S →+* S ⧸ Q := Ideal.Quotient.mk Q with hπ
  have hAS : ∀ x ∈ A, x ∈ S := fun x hx => by
    simpa using (algebraMap A S ⟨x, hx⟩).2
  have hRS : ∀ x ∈ R, x ∈ S := fun x hx => hAS x (hRA x hx)
  let incl : R →+* S :=
    { toFun := fun r => ⟨r, hRS r r.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  set ψ : R →+* S ⧸ Q := π.comp incl with hψ
  -- the map `A/𝔪 → S/Q`
  set φ : A ⧸ 𝔪 →+* S ⧸ Q :=
    Ideal.quotientMap Q (algebraMap A S) (by rw [← hQ𝔪]) with hφ
  -- the image of `R` in `S/Q` is integral over `ℤ[1/N]`
  set T : Subalgebra ℤ (S ⧸ Q) := integralClosureAway N (S ⧸ Q)
  have hRimg : ∀ r : R, ψ r ∈ T := by
    set P : Subalgebra ℤ K := (T.comap ψ.toIntAlgHom).map R.val with hP
    have hRP : R ≤ P := by
      refine Algebra.adjoin_le fun x hx => ?_
      refine ⟨⟨x, Algebra.subset_adjoin hx⟩, ?_, rfl⟩
      have hψx : ψ ⟨x, Algebra.subset_adjoin hx⟩ = φ (Ideal.Quotient.mk 𝔪 ⟨x, hsA x hx⟩) := by
        rw [hφ, Ideal.quotientMap_mk]
        rfl
      change ψ ⟨x, Algebra.subset_adjoin hx⟩ ∈ T
      rw [hψx]
      exact map_mem_integralClosureAway φ (hgenN x hx)
    intro r
    obtain ⟨r', hr', hrr'⟩ := hRP r.2
    have : r' = r := Subtype.ext hrr'
    rw [← this]
    exact hr'
  -- so is the image of `α`
  have hαS : α ∈ S := Algebra.subset_adjoin (Set.mem_singleton α)
  obtain ⟨p, hpm, hp⟩ := hαint
  have hpS : p.eval₂ incl ⟨α, hαS⟩ = 0 := by
    apply Subtype.ext
    have := Polynomial.hom_eval₂ p incl (algebraMap S K) ⟨α, hαS⟩
    simpa using this.trans hp
  have hαimg : π ⟨α, hαS⟩ ∈ T := by
    refine (hpm.map ψ).mem_integralClosureAway (fun i => ?_) ?_
    · rw [coeff_map]
      exact hRimg _
    · rw [eval_map, hψ, ← Polynomial.hom_eval₂, hpS, map_zero]
  -- back to `K`: `ℚ[N ^ j α]` is a field, so it embeds in `S/Q`
  obtain ⟨j, q, hqm, hq⟩ := hαimg
  refine ⟨j, q, hqm, ?_⟩
  set γ : K := (N : K) ^ j * α with hγ
  have hγS : γ ∈ S := Subalgebra.mul_mem S (Subalgebra.pow_mem S (Subalgebra.natCast_mem S N) j) hαS
  have hπγ : π ⟨γ, hγS⟩ = (N : S ⧸ Q) ^ j * π ⟨α, hαS⟩ := by
    have : (⟨γ, hγS⟩ : S) = (N : S) ^ j * ⟨α, hαS⟩ := by ext; simp [γ]
    rw [this, map_mul, map_pow, map_natCast]
  set βS : S := q.eval₂ (algebraMap ℤ S) ⟨γ, hγS⟩ with hβS
  have hβK : (βS : K) = q.eval₂ (algebraMap ℤ K) γ := by
    have := Polynomial.hom_eval₂ q (algebraMap ℤ S) (algebraMap S K) ⟨γ, hγS⟩
    rw [show (algebraMap S K).comp (algebraMap ℤ S) = algebraMap ℤ K from RingHom.ext_int _ _]
      at this
    exact this
  have hπβ : π βS = 0 := by
    rw [hβS, Polynomial.hom_eval₂, hπγ,
      show π.comp (algebraMap ℤ S) = algebraMap ℤ (S ⧸ Q) from RingHom.ext_int _ _]
    exact hq
  rw [← hβK]
  by_contra hβ0
  -- `β ≠ 0` is algebraic over `ℚ`, so `β⁻¹ ∈ S`, contradicting `π β = 0`.
  have hNint : IsIntegral ℚ (N : K) := by
    simpa using isIntegral_algebraMap (R := ℚ) (A := K) (x := (N : ℚ))
  have hγint : IsIntegral ℚ γ := (hNint.pow j).mul hαalg.isIntegral
  have hβalg : IsAlgebraic ℚ (βS : K) := by
    have hmem : (βS : K) ∈ Algebra.adjoin ℚ {γ} := by
      have := Polynomial.aeval_mem_adjoin_singleton ℚ γ (p := q.map (algebraMap ℤ ℚ))
      rwa [aeval_map_algebraMap, aeval_def, ← hβK] at this
    exact (adjoin_le_integralClosure hγint hmem).isAlgebraic
  have hβinv : (βS : K)⁻¹ ∈ S.restrictScalars ℚ :=
    Subalgebra.inv_mem_of_algebraic (S.restrictScalars ℚ) (x := ⟨βS, βS.2⟩) hβalg
  have h1 : βS * ⟨(βS : K)⁻¹, hβinv⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hβ0)
  have h2 := congrArg π h1
  rw [map_mul, hπβ, zero_mul, map_one] at h2
  exact zero_ne_one h2
