/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Mass.Directional
import K3Twists.LinearAlgebra.Lattice.Mukai.PeriodRecovery

/-!
# Interior profiles are determined by their class infima

Let the classes of a triangulated category lie in a real Mukai lattice `MukaiLattice ℝ N` of a
quadratic space `(N, q)`, and let the charges be real-linear. For a stability condition `σ` whose
root classes have semistable spherical representatives (Kikuta–Koseki–Ouchi, arXiv:2504.12253,
Lemma 3.4), the class infimum of the mass is `|Z_σ|` on roots (their Corollary 3.5,
`PreStabilityCondition.WithClassMap.classInf_massProfile`). With a basis of roots with pairwise
nonzero pairings, such as the doubled line-bundle classes `v(𝒪)`, `v(𝒪(2e_i))`, `v(𝒪(-2e_{i₀}))`
(`Mukai.doubledLineBundles`, the repaired form of their Lemma 3.8), these moduli determine the
period form `|Z|²` by polarization, hence `Z` up to an orthogonal map of `ℂ` and scale (the proof of
their Proposition 3.10). This file states the consequences for profiles:

* `exists_linearIsometryEquiv_of_mass_eq_mul`: if two stability conditions have proportional masses
  on the spherical objects, `m_σ = c m_τ`, their charges differ by `c` times a real-linear isometry
  of `ℂ` (a rotation, or a rotation followed by conjugation);
* `not_classInf_eq_mul_norm_of_real`: a profile whose class infima are `|ℓ(γ)|` for one real linear
  form `ℓ` has no proportional interior profile: `|ℓ| = c |Z|` on the roots would make `ℓ` a
  surjection onto `ℂ`. The rank functional at the cusp (`|rk γ|`) and the directional profiles
  (`|Re(e^{-iθ} Z(γ))|`) have such class infima, so their projective classes are not interior.

Only interior profiles are concerned: at boundary points the square of the class infimum need not
be a quadratic form, and no boundary extension of the recovery is claimed.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Set Submodule

universe u v u'

namespace CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
section General

variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

/-- If two prestability conditions have proportional masses on `𝒮`, then on every class with
semistable representatives in `𝒮` for both, their charges have proportional moduli. -/
theorem norm_charge_eq_mul_of_mass_eq_mul (σ τ : WithClassMap C v) {𝒮 : Set C} {c : ℝ}
    (hc : 0 ≤ c) (hm : ∀ S ∈ 𝒮, σ.mass S = c * τ.mass S) {γ : Λ}
    (hσ : ∃ S ∈ 𝒮, classOf C v S = γ ∧ ∃ φ, σ.slicing.P φ S)
    (hτ : ∃ S ∈ 𝒮, classOf C v S = γ ∧ ∃ φ, τ.slicing.P φ S) :
    ‖σ.Z γ‖ = c * ‖τ.Z γ‖ := by
  rw [← σ.classInf_massProfile hσ, ← τ.classInf_massProfile hτ]
  have hprof : ∀ S ∈ 𝒮, σ.massProfile S = (Real.toNNReal c • τ.massProfile) S := fun S hS ↦ by
    apply NNReal.coe_injective
    rw [Profile.nnreal_smul_apply, NNReal.coe_mul, Real.coe_toNNReal _ hc, coe_massProfile_apply,
      coe_massProfile_apply, hm S hS]
  rw [Profile.classInf_congr hprof, Profile.classInf_smul, NNReal.coe_mul,
    Real.coe_toNNReal _ hc]

end General

variable {N : Type u'} [AddCommGroup N] [Module ℝ N] {v : K₀ C →+ MukaiLattice ℝ N}

/-- **Proportional masses have equivalent charges** (Kikuta–Koseki–Ouchi, arXiv:2504.12253,
Proposition 3.10). Let the classes lie in the real Mukai lattice of `(N, q)`, with `q` integral on
the lattice spanned by a family `e` spanning `N` and `q(e_{i₀}) ≠ 0`, and let the charges of `σ`
and `τ` be the real-linear maps `Zσ`, `Zτ`, with `Zτ` surjective. If every root in the lattice
spanned by the doubled line-bundle classes has semistable representatives in `𝒮` for both, and
`m_σ = c m_τ` on `𝒮` with `c > 0`, then `Zσ = c A Zτ` for a real-linear isometry `A` of `ℂ`. -/
theorem exists_linearIsometryEquiv_of_mass_eq_mul {ι : Type*} (q : QuadraticMap ℝ N ℝ)
    {e : ι → N} (he : span ℝ (range e) = ⊤) (hint : ∀ u ∈ span ℤ (range e), ∃ n : ℤ, q u = n)
    {i₀ : ι} (h₀ : q (e i₀) ≠ 0) (σ τ : WithClassMap C v) {Zσ Zτ : MukaiLattice ℝ N →ₗ[ℝ] ℂ}
    (hσZ : ∀ x, σ.Z x = Zσ x) (hτZ : ∀ x, τ.Z x = Zτ x) (hZ : Function.Surjective Zτ)
    {𝒮 : Set C} {R : Set (MukaiLattice ℝ N)} (hσ : σ.HasSemistableRepresentatives 𝒮 R)
    (hτ : τ.HasSemistableRepresentatives 𝒮 R)
    (hR : ∀ x ∈ span ℤ (range (Mukai.doubledLineBundles q e i₀)),
      Mukai.IsSpherical q.polarBilin x → x ∈ R)
    {c : ℝ} (hc : 0 < c) (hm : ∀ S ∈ 𝒮, σ.mass S = c * τ.mass S) :
    ∃ A : ℂ ≃ₗᵢ[ℝ] ℂ, ∀ x, Zσ x = c • A (Zτ x) :=
  Mukai.exists_linearIsometryEquiv_of_norm_eq_doubledLineBundles q he hint h₀ hZ hc
    fun x hx hsph ↦ by
      rw [← hσZ, ← hτZ]
      exact σ.norm_charge_eq_mul_of_mass_eq_mul τ hc.le hm (hσ x (hR x hx hsph))
        (hτ x (hR x hx hsph))

/-- **Class infima of rank one are not interior.** Let `ℓ : MukaiLattice ℝ N →ₗ[ℝ] ℝ` be a real
linear form and `Zτ` a surjective real-linear charge. Then `|ℓ(x)| = c ‖Zτ x‖`, with `c > 0`, cannot
hold on every root of the lattice spanned by the doubled line-bundle classes: by period recovery it
would make `ℓ`, as a map to `ℂ`, equal to `c A Zτ`, a surjection onto `ℂ`. -/
theorem not_classInf_eq_mul_norm_of_real {ι : Type*} (q : QuadraticMap ℝ N ℝ) {e : ι → N}
    (he : span ℝ (range e) = ⊤) (hint : ∀ u ∈ span ℤ (range e), ∃ n : ℤ, q u = n) {i₀ : ι}
    (h₀ : q (e i₀) ≠ 0) (ℓ : MukaiLattice ℝ N →ₗ[ℝ] ℝ) {Zτ : MukaiLattice ℝ N →ₗ[ℝ] ℂ}
    (hZ : Function.Surjective Zτ) {c : ℝ} (hc : 0 < c) :
    ¬ ∀ x ∈ span ℤ (range (Mukai.doubledLineBundles q e i₀)),
      Mukai.IsSpherical q.polarBilin x → |ℓ x| = c * ‖Zτ x‖ := by
  intro h
  obtain ⟨A, hA⟩ := Mukai.exists_linearIsometryEquiv_of_norm_eq_doubledLineBundles q he hint h₀
    (Z' := Complex.ofRealCLM.toLinearMap ∘ₗ ℓ) hZ hc fun x hx hsph ↦ by
      simpa [Complex.norm_real] using h x hx hsph
  -- `I = c A (Zτ x)` for some `x`, but the left side of `hA` is real
  obtain ⟨x, hx⟩ := hZ ((c⁻¹ : ℝ) • A.symm Complex.I)
  have := hA x
  rw [hx, map_smul, LinearIsometryEquiv.apply_symm_apply, smul_smul, mul_inv_cancel₀ hc.ne',
    one_smul] at this
  have him := congrArg Complex.im this
  simp at him

end CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap
