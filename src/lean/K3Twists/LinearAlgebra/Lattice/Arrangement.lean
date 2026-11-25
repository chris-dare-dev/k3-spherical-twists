/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.Lattice.Mukai.Support
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Strata of the root arrangement

Let `V` be a finite-dimensional real space with a symmetric nondegenerate form `B` of signature
`(2, n)`: `sigPos B = 2`. For the Mukai lattice of a K3 surface of Picard rank `ρ`, `n = ρ`. A
**positive period** is a pair `(Ω₁, Ω₂)` spanning a positive-definite plane (`IsPosPlane`); its
charge `Z(v) = B(Ω₁, v) + i B(Ω₂, v)` vanishes on `v` exactly when `v ⊥ Ω₁, Ω₂`. These are the
points of Bridgeland's period domain `P⁺` (arXiv:math/0307164, §8), root hyperplanes kept.

## The stratum trichotomy

* `exists_posPlane_orthogonal_iff_negDef`: **the charge of some positive period vanishes on a
  subspace `U` iff `U` is negative definite.** One direction is the signature-`(2, n)` lemma
  `Mukai.negDef_orthogonal_of_posPlane`; for the other, a positive plane projects along `U` onto a
  positive plane of `U^⊥`, the square only growing since `B ≤ 0` on `U`. So finitely many roots
  have a common zero in `P⁺` iff their span is negative definite; their root system is then the
  kernel root system of `LinearAlgebra/RootSystem/Spherical.lean`, finite and simply laced, of
  rank at most `n` (`finrank_le_of_negDef`).
* `negDef_span_pair_iff`, **two roots**: for linearly independent roots `δ₁`, `δ₂` with
  `a = B(δ₁, δ₂)`, their span is negative definite iff `|a| < 2`, so they meet in `P⁺` iff
  `|a| < 2` (`exists_posPlane_orthogonal_pair_iff`); for integral `a`, iff `|a| ≤ 1`, the types
  `A₁ × A₁` and `A₂`.
* At `a = ±2` the vector `u = δ₁ ± δ₂` is isotropic and orthogonal to both roots
  (`isotropic_add_of_eq_two`): the span is semidefinite and degenerate. For `|a| > 2` it is
  indefinite: `B(u, u) = 2|a| - 4 > 0` (`pos_add_of_two_lt`).

This is the stated form on `P⁺`; on the component `P₀⁺` with the root hyperplanes removed the
question is vacuous. That the orthogonal complement is Lorentzian for `|a| > 2` is not
formalized here.
-/

open Module

namespace Mukai

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- `(Ω₁, Ω₂)` spans a positive-definite plane: `B(aΩ₁ + bΩ₂, aΩ₁ + bΩ₂) > 0` unless
`a = b = 0`. -/
def IsPosPlane (B : LinearMap.BilinForm ℝ V) (Ω₁ Ω₂ : V) : Prop :=
  ∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) → 0 < B (a • Ω₁ + b • Ω₂) (a • Ω₁ + b • Ω₂)

/-- **The charge of a positive period vanishes on `U` iff `U` is negative definite**, in signature
`(2, n)`. -/
theorem exists_posPlane_orthogonal_iff_negDef (B : LinearMap.BilinForm ℝ V)
    (hB : ∀ x y, B x y = B y x) (hnd : ∀ w, (∀ y, B w y = 0) → w = 0)
    (hsig : sigPos B.toQuadraticMap = 2) (U : Submodule ℝ V) :
    (∃ Ω₁ Ω₂, IsPosPlane B Ω₁ Ω₂ ∧ ∀ u ∈ U, B Ω₁ u = 0 ∧ B Ω₂ u = 0) ↔
      ∀ u ∈ U, u ≠ 0 → B u u < 0 := by
  constructor
  · rintro ⟨Ω₁, Ω₂, hΩ, horth⟩ u hu hu0
    exact negDef_orthogonal_of_posPlane B hB hnd hsig.le hΩ (horth u hu).1 (horth u hu).2 hu0
  · intro hU
    -- a positive plane of `V`
    obtain ⟨P, hPdim, hPpos⟩ := exists_finrank_eq_sigPos_and_posDef B.toQuadraticMap
    rw [hsig] at hPdim
    let e := finBasisOfFinrankEq ℝ P hPdim
    -- `V = U ⊕ U^⊥`
    have hrefl : B.IsRefl := fun x y h => by rw [hB]; exact h
    have hnd' : (B.restrict U).Nondegenerate := by
      refine ⟨fun x hx => ?_, fun y hy => ?_⟩
      · by_contra hx0
        have := hU x x.2 fun h => hx0 (Subtype.ext h)
        have h0 := hx x
        simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply] at h0
        linarith
      · by_contra hy0
        have := hU y y.2 fun h => hy0 (Subtype.ext h)
        have h0 := hy y
        simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply] at h0
        linarith
    have hc := LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hrefl hnd'
    have hdec : ∀ v : V, ∃ u ∈ U, ∃ w ∈ B.orthogonal U, u + w = v := fun v =>
      Submodule.mem_sup.mp (hc.sup_eq_top ▸ Submodule.mem_top)
    choose u hu w hw huw using hdec
    refine ⟨w (e 0), w (e 1), fun a b hab => ?_, fun x hx => ⟨?_, ?_⟩⟩
    · -- the projection of a positive vector of `P` along `U`
      set p : V := a • (e 0 : V) + b • (e 1 : V)
      set u' := a • u (e 0) + b • u (e 1)
      set w' := a • w (e 0) + b • w (e 1)
      have hu' : u' ∈ U := U.add_mem (U.smul_mem _ (hu _)) (U.smul_mem _ (hu _))
      have hw' : w' ∈ B.orthogonal U :=
        (B.orthogonal U).add_mem ((B.orthogonal U).smul_mem _ (hw _))
          ((B.orthogonal U).smul_mem _ (hw _))
      have hp : p = u' + w' := by
        have h0 := huw (e 0)
        have h1 := huw (e 1)
        calc p = a • (u (e 0) + w (e 0)) + b • (u (e 1) + w (e 1)) := by rw [h0, h1]
          _ = u' + w' := by simp only [u', w']; module
      have hcross : B u' w' = 0 := hw' u' hu'
      have hcross' : B w' u' = 0 := by rw [hB]; exact hcross
      have hpp : 0 < B p p := by
        have hp0 : (a • e 0 + b • e 1 : P) ≠ 0 := by
          intro h0
          have hli := e.linearIndependent
          have h2 : LinearIndependent ℝ ![e 0, e 1] := by
            convert hli using 1
            funext i
            fin_cases i <;> rfl
          have := LinearIndependent.pair_iff.mp h2 a b h0
          rcases hab with ha | hb
          · exact ha this.1
          · exact hb this.2
        have := hPpos _ hp0
        simpa [p] using this
      have huu : B u' u' ≤ 0 := by
        by_cases h0 : u' = 0
        · simp [h0]
        · exact (hU u' hu' h0).le
      have : B p p = B u' u' + B w' w' := by
        rw [hp]
        simp only [map_add, LinearMap.add_apply, hcross, hcross']
        ring
      change 0 < B w' w'
      linarith
    · rw [hB]; exact hw (e 0) x hx
    · rw [hB]; exact hw (e 1) x hx

/-- **The rank of a stratum.** A negative-definite subspace has dimension at most
`dim V - sigPos B`; in signature `(2, ρ)` the root system of a stratum has rank at most `ρ`. -/
theorem finrank_le_of_negDef (B : LinearMap.BilinForm ℝ V) (U : Submodule ℝ V)
    (hU : ∀ u ∈ U, u ≠ 0 → B u u < 0) :
    finrank ℝ U ≤ finrank ℝ V - sigPos B.toQuadraticMap := by
  have := QuadraticForm.sigPos_add_finrank_le_of_nonpos (Q := B.toQuadraticMap) (V := U)
    fun x hx => by
      by_cases h0 : x = 0
      · simp [h0]
      · exact (hU x hx h0).le
  omega

/-! ### Two roots -/

omit [FiniteDimensional ℝ V] in
/-- **Two roots: negative definiteness.** For linearly independent roots `δ₁`, `δ₂`
(`B(δᵢ, δᵢ) = -2`) with `a = B(δ₁, δ₂)`, the span is negative definite iff `a² < 4`. -/
theorem negDef_span_pair_iff (B : LinearMap.BilinForm ℝ V) (hB : ∀ x y, B x y = B y x)
    {δ₁ δ₂ : V} (h₁ : B δ₁ δ₁ = -2) (h₂ : B δ₂ δ₂ = -2) (hli : LinearIndependent ℝ ![δ₁, δ₂]) :
    (∀ u ∈ Submodule.span ℝ {δ₁, δ₂}, u ≠ 0 → B u u < 0) ↔ B δ₁ δ₂ ^ 2 < 4 := by
  set a := B δ₁ δ₂
  have hval : ∀ s t : ℝ, B (s • δ₁ + t • δ₂) (s • δ₁ + t • δ₂) = -2 * s ^ 2 + 2 * a * s * t
      - 2 * t ^ 2 := fun s t => by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h₁, h₂,
      hB δ₂ δ₁]
    ring
  constructor
  · intro h
    by_contra ha
    push Not at ha
    have hne : (a / 2) • δ₁ + (1 : ℝ) • δ₂ ≠ 0 := by
      intro h0
      have := LinearIndependent.pair_iff.mp hli _ _ h0
      exact one_ne_zero this.2
    have := h _ (Submodule.mem_span_pair.mpr ⟨_, _, rfl⟩) hne
    rw [hval] at this
    nlinarith
  · intro ha u hu hu0
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hu
    rw [hval]
    have hst : s ≠ 0 ∨ t ≠ 0 := by
      by_contra h
      push Not at h
      apply hu0
      simp [h.1, h.2]
    have key : -2 * s ^ 2 + 2 * a * s * t - 2 * t ^ 2 =
        -2 * (s - a * t / 2) ^ 2 - (4 - a ^ 2) / 2 * t ^ 2 := by ring
    rw [key]
    rcases hst with hs | ht
    · by_cases ht : t = 0
      · rw [ht]
        have : 0 < s ^ 2 := by positivity
        nlinarith
      · have : 0 < t ^ 2 := by positivity
        nlinarith [sq_nonneg (s - a * t / 2)]
    · have : 0 < t ^ 2 := by positivity
      nlinarith [sq_nonneg (s - a * t / 2)]

/-- **Two roots meet in `P⁺` iff they pair to less than `2` in absolute value**, in signature
`(2, n)`; for integral pairings, iff `|B(δ₁, δ₂)| ≤ 1`. -/
theorem exists_posPlane_orthogonal_pair_iff (B : LinearMap.BilinForm ℝ V)
    (hB : ∀ x y, B x y = B y x) (hnd : ∀ w, (∀ y, B w y = 0) → w = 0)
    (hsig : sigPos B.toQuadraticMap = 2) {δ₁ δ₂ : V} (h₁ : B δ₁ δ₁ = -2) (h₂ : B δ₂ δ₂ = -2)
    (hli : LinearIndependent ℝ ![δ₁, δ₂]) :
    (∃ Ω₁ Ω₂, IsPosPlane B Ω₁ Ω₂ ∧ B Ω₁ δ₁ = 0 ∧ B Ω₂ δ₁ = 0 ∧ B Ω₁ δ₂ = 0 ∧ B Ω₂ δ₂ = 0) ↔
      B δ₁ δ₂ ^ 2 < 4 := by
  rw [← negDef_span_pair_iff B hB h₁ h₂ hli,
    ← exists_posPlane_orthogonal_iff_negDef B hB hnd hsig]
  constructor
  · rintro ⟨Ω₁, Ω₂, hΩ, h11, h21, h12, h22⟩
    refine ⟨Ω₁, Ω₂, hΩ, fun u hu => ?_⟩
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hu
    simp [h11, h21, h12, h22]
  · rintro ⟨Ω₁, Ω₂, hΩ, horth⟩
    have m₁ : δ₁ ∈ Submodule.span ℝ {δ₁, δ₂} := Submodule.subset_span (by simp)
    have m₂ : δ₂ ∈ Submodule.span ℝ {δ₁, δ₂} := Submodule.subset_span (by simp)
    exact ⟨Ω₁, Ω₂, hΩ, (horth _ m₁).1, (horth _ m₁).2, (horth _ m₂).1, (horth _ m₂).2⟩

omit [FiniteDimensional ℝ V] in
/-- **Pairing two: an isotropic radical.** For roots with `B(δ₁, δ₂) = 2`, `u = δ₁ + δ₂` is
isotropic and orthogonal to both roots; for `B(δ₁, δ₂) = -2` apply it to `δ₁, -δ₂`. -/
theorem isotropic_add_of_eq_two (B : LinearMap.BilinForm ℝ V) (hB : ∀ x y, B x y = B y x)
    {δ₁ δ₂ : V} (h₁ : B δ₁ δ₁ = -2) (h₂ : B δ₂ δ₂ = -2) (ha : B δ₁ δ₂ = 2) :
    B (δ₁ + δ₂) (δ₁ + δ₂) = 0 ∧ B (δ₁ + δ₂) δ₁ = 0 ∧ B (δ₁ + δ₂) δ₂ = 0 := by
  simp only [map_add, LinearMap.add_apply, h₁, h₂, ha, hB δ₂ δ₁]
  norm_num

omit [FiniteDimensional ℝ V] in
/-- **Pairing above two: an indefinite span.** For roots with `B(δ₁, δ₂) > 2`,
`B(δ₁ + δ₂, δ₁ + δ₂) = 2B(δ₁, δ₂) - 4 > 0`. -/
theorem pos_add_of_two_lt (B : LinearMap.BilinForm ℝ V) (hB : ∀ x y, B x y = B y x)
    {δ₁ δ₂ : V} (h₁ : B δ₁ δ₁ = -2) (h₂ : B δ₂ δ₂ = -2) (ha : 2 < B δ₁ δ₂) :
    0 < B (δ₁ + δ₂) (δ₁ + δ₂) := by
  simp only [map_add, LinearMap.add_apply, h₁, h₂, hB δ₂ δ₁]
  linarith

end Mukai
