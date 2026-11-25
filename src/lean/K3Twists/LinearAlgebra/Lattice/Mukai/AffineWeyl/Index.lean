/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.Lattice.Mukai.AffineWeyl
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# The translation lattice of a fibre and its index bounds

For a connected exceptional fibre `F` with curves `Cᵢ` in a lattice `N`, line bundles act on the
affine simple roots through their degrees `L ↦ (L·Cᵢ)ᵢ ∈ ℤ^l` (`FundamentalCycle.degree`;
`⊗𝒪(L) αᵢ = αᵢ - (Cᵢ·L)δ`). Three lattices of translations:

* `Q^∨ = A ℤ^l`, the degrees of the classes supported on the fibre, where `A = -Gram(Cᵢ)` is the
  Cartan matrix of the fibre (`FundamentalCycle.cartan`, `FundamentalCycle.corootLattice`,
  `degree_combination`);
* `Λ_H`, the degrees of the classes orthogonal to a class `H` with `H·Cᵢ = 0`
  (`FundamentalCycle.polarizedDegreeLattice`), and `Λ`, the degrees of all of `N`
  (`FundamentalCycle.degreeLattice`).

**`A ℤ^l ⊆ Λ_H ⊆ Λ ⊆ ℤ^l`** (`corootLattice_le_polarizedDegreeLattice`,
`polarizedDegreeLattice_le_degreeLattice`), and `[ℤ^l : A ℤ^l] = |det A|`
(`index_corootLattice`), with `det A ≠ 0` from negative definiteness (`det_cartan_ne_zero`). So
both indices `[ℤ^l : Λ]`, `[ℤ^l : Λ_H]` and the relative index `[Λ : A ℤ^l]` divide `|det A|`
(`index_degreeLattice_dvd`, `index_polarizedDegreeLattice_dvd`, `relIndex_corootLattice_dvd`).
For the simply laced types the determinant is `n + 1` for `Aₙ` (`CartanMatrix.A_det`), `4` for `Dₙ`
(`CartanMatrix.D_det`), and `3`, `2`, `1` for `E₆`, `E₇`, `E₈` (`CartanMatrix.E₆_det` and its
siblings in Mathlib). That `|det A|` is the order of `P^∨/Q^∨` is not used here, and several
fibres at once, where the bound is the product of the determinants, are not treated.
-/

open Matrix

namespace Mukai.FundamentalCycle

variable {N : Type*} [AddCommGroup N] {b : N →ₗ[ℤ] N →ₗ[ℤ] ℤ} {ι : Type*} [Fintype ι]
variable (F : FundamentalCycle b ι)

/-- **The degree map** `L ↦ (L·Cᵢ)ᵢ`. -/
def degree : N →ₗ[ℤ] ι → ℤ :=
  LinearMap.pi fun i => b.flip (F.curve i)

@[simp] theorem degree_apply (L : N) (i : ι) : F.degree L i = b L (F.curve i) := rfl

/-- **The Cartan matrix of the fibre**, `A = -Gram(Cᵢ)`, a finite-type Cartan matrix. -/
def cartan : Matrix ι ι ℤ :=
  LinearMap.BilinForm.wallMatrix b F.curve

@[simp] theorem cartan_apply (i j : ι) : F.cartan i j = -b (F.curve i) (F.curve j) := rfl

/-- `Λ`: the degrees of all classes. -/
def degreeLattice : Submodule ℤ (ι → ℤ) :=
  LinearMap.range F.degree

/-- `Λ_H`: the degrees of the classes orthogonal to `H`. -/
def polarizedDegreeLattice (H : N) : Submodule ℤ (ι → ℤ) :=
  (LinearMap.ker (b.flip H)).map F.degree

theorem polarizedDegreeLattice_le_degreeLattice (H : N) :
    F.polarizedDegreeLattice H ≤ F.degreeLattice :=
  LinearMap.map_le_range

/-- The degree of a class supported on the fibre: `deg(Σ dⱼ Cⱼ) = -A d`. -/
theorem degree_combination (hb : ∀ x y, b x y = b y x) (d : ι → ℤ) :
    F.degree (∑ j, d j • F.curve j) = -(F.cartan *ᵥ d) := by
  ext i
  simp only [degree_apply, map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, Pi.neg_apply, mulVec, dotProduct, cartan_apply, neg_mul, Finset.sum_neg_distrib,
    neg_neg]
  exact Finset.sum_congr rfl fun j _ => by rw [hb]; ring

/-- `A` is injective: `A d = 0` gives `(Σ dᵢ Cᵢ)² = -dᵀAd = 0`, so `d = 0`. -/
theorem cartan_mulVec_injective : Function.Injective (F.cartan *ᵥ ·) := by
  intro d d' h
  have h0 : F.cartan *ᵥ (d - d') = 0 := by
    simp only at h
    rw [mulVec_sub, h, sub_self]
  have hq : b (∑ i, (d - d') i • F.curve i) (∑ i, (d - d') i • F.curve i) = 0 := by
    rw [LinearMap.BilinForm.apply_sum_smul_self]
    change -((d - d') ⬝ᵥ F.cartan *ᵥ (d - d')) = 0
    rw [h0, dotProduct_zero, neg_zero]
  exact sub_eq_zero.mp (F.eq_zero_of_self_combination hq)

variable [DecidableEq ι]

/-- `Q^∨ = A ℤ^l`. -/
def corootLattice : Submodule ℤ (ι → ℤ) :=
  LinearMap.range (Matrix.toLin' F.cartan)

theorem corootLattice_le_polarizedDegreeLattice (hb : ∀ x y, b x y = b y x) {H : N}
    (hH : ∀ i, b (F.curve i) H = 0) : F.corootLattice ≤ F.polarizedDegreeLattice H := by
  rintro _ ⟨d, rfl⟩
  refine ⟨∑ j, (-d) j • F.curve j, ?_, ?_⟩
  · simp [map_sum, hH]
  · rw [degree_combination F hb, Matrix.toLin'_apply, mulVec_neg, neg_neg]

theorem corootLattice_le_degreeLattice (hb : ∀ x y, b x y = b y x) :
    F.corootLattice ≤ F.degreeLattice := by
  rintro _ ⟨d, rfl⟩
  exact ⟨∑ j, (-d) j • F.curve j, by
    rw [degree_combination F hb, Matrix.toLin'_apply, mulVec_neg, neg_neg]⟩

theorem det_cartan_ne_zero : F.cartan.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  exact hv (F.cartan_mulVec_injective (by simpa using hAv))

/-- **`[ℤ^l : A ℤ^l] = |det A|`.** -/
theorem index_corootLattice :
    F.corootLattice.toAddSubgroup.index = F.cartan.det.natAbs := by
  have hinj : Function.Injective (Matrix.toLin' F.cartan) := F.cartan_mulVec_injective
  let e : (ι → ℤ) ≃ₗ[ℤ] F.corootLattice := LinearEquiv.ofInjective (Matrix.toLin' F.cartan) hinj
  have h := Submodule.natAbs_det_equiv F.corootLattice e
  have hcomp : F.corootLattice.subtype ∘ₗ AddMonoidHom.toIntLinearMap (e : (ι → ℤ) →+ _) =
      Matrix.toLin' F.cartan := by
    ext x : 1
    rfl
  rw [hcomp, LinearMap.det_toLin'] at h
  rw [h]
  rfl

theorem index_degreeLattice_dvd (hb : ∀ x y, b x y = b y x) :
    F.degreeLattice.toAddSubgroup.index ∣ F.cartan.det.natAbs := by
  rw [← F.index_corootLattice]
  exact AddSubgroup.index_dvd_of_le (F.corootLattice_le_degreeLattice hb)

theorem index_polarizedDegreeLattice_dvd (hb : ∀ x y, b x y = b y x) {H : N}
    (hH : ∀ i, b (F.curve i) H = 0) :
    (F.polarizedDegreeLattice H).toAddSubgroup.index ∣ F.cartan.det.natAbs := by
  rw [← F.index_corootLattice]
  exact AddSubgroup.index_dvd_of_le (F.corootLattice_le_polarizedDegreeLattice hb hH)

/-- `[Λ : A ℤ^l]` divides `|det A|`. -/
theorem relIndex_corootLattice_dvd (hb : ∀ x y, b x y = b y x) :
    F.corootLattice.toAddSubgroup.relIndex F.degreeLattice.toAddSubgroup ∣
      F.cartan.det.natAbs := by
  rw [← F.index_corootLattice]
  exact AddSubgroup.relIndex_dvd_index_of_le (F.corootLattice_le_degreeLattice hb)

/-- `[Λ_H : A ℤ^l]` divides `|det A|`. -/
theorem relIndex_corootLattice_polarized_dvd (hb : ∀ x y, b x y = b y x)
    {H : N} (hH : ∀ i, b (F.curve i) H = 0) :
    F.corootLattice.toAddSubgroup.relIndex (F.polarizedDegreeLattice H).toAddSubgroup ∣
      F.cartan.det.natAbs := by
  rw [← F.index_corootLattice]
  exact AddSubgroup.relIndex_dvd_index_of_le (F.corootLattice_le_polarizedDegreeLattice hb hH)

end Mukai.FundamentalCycle
