/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.EllipticWithSection.AffineWeyl
import K3Twists.CategoryTheory.Abelian.TorsionTheory.CartanDescent

/-!
# Cartan descent on the curve wall: the certificate `p = 1`

On the elliptic K3 surface `X` with a section `C` of `EllipticWithSection/Lattice.lean`, the
polarization `H = C + 2F` has `H·C = 0` and contracts the section; the exceptional fibre is the
single curve `C`, of type `A₁` (`sectionFibre`). Its Cartan matrix is `A = (-C²) = (2)`, and
`p = 1` is an integer certificate, `A·1 = 2` (`sectionFibre_cartan_mulVec_one`), computed on
the lattice `NS(X)`.

So Cartan descent applies to objects `Q j` (in the application `𝒪_C(j)`) with this matrix and
the potential `L(Y) = hom(Y, Q (κ + 1))`: every nonzero morphism `f : Y ⟶ Q κ` lowers it by at
least `2` (`two_le_potential_sub_sectionFibre`), and `(⊥F, F)` is a torsion pair
(`torsionTheory_sectionFibre`). The objects enter through
`CategoryTheory.Abelian.CartanDescentHypotheses`, whose fields have no geometric instance in the
library (see `CategoryTheory/Abelian/TorsionTheory/CartanDescent.lean`); only the matrix side is
checked on real objects here.
-/

universe w v u

namespace AlgebraicGeometry.K3.EllipticWithSection

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Matrix

/-- **The certificate `p = 1` on the curve wall**: the Cartan matrix of `sectionFibre` is `(2)`,
so `A·1 = 2`. -/
theorem sectionFibre_cartan_mulVec_one : sectionFibre.cartan *ᵥ (fun _ => 1) = fun _ => 2 := by
  ext u
  simp [Matrix.mulVec, dotProduct, curve]

variable {k : Type*} [Field k] {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [Linear k 𝒜]
  [HasExt.{w} 𝒜] {Q : Unit → ℤ → 𝒜} {κ : Unit → ℤ}

/-- **The drop on the curve wall.** With the Cartan matrix of `sectionFibre` and `p = 1`, a
nonzero `f : Y ⟶ Q () (κ ())` lowers `L = hom(-, Q () (κ () + 1))` by at least `2` from `Y` to
`ker f`. -/
theorem two_le_potential_sub_sectionFibre
    (H : CartanDescentHypotheses k Q κ sectionFibre.cartan) {Y : 𝒜} (f : Y ⟶ Q () (κ ()))
    (hf : f ≠ 0) :
    2 ≤ (CartanDescentHypotheses.potential k Q κ (fun _ => 1) Y : ℤ) -
      CartanDescentHypotheses.potential k Q κ (fun _ => 1) (kernel f) := by
  have h := H.mulVec_le_potential_sub (fun _ => zero_le_one) f hf
  rwa [sectionFibre_cartan_mulVec_one] at h

/-- **Cartan descent on the curve wall**, from the certificate `p = 1`. -/
theorem torsionTheory_sectionFibre (H : CartanDescentHypotheses k Q κ sectionFibre.cartan) :
    TorsionTheory (CartanDescentHypotheses.torsionFreeClass Q κ).leftOrthogonal
      (CartanDescentHypotheses.torsionFreeClass Q κ) :=
  H.torsionTheory (p := fun _ => 1) (fun _ => zero_le_one) fun _ => by
    rw [sectionFibre_cartan_mulVec_one]
    norm_num

end AlgebraicGeometry.K3.EllipticWithSection
