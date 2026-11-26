/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.EllipticWithSection.AffineWeyl
import K3Twists.LinearAlgebra.Lattice.Mukai.AffineWeyl.Coxeter
import K3Twists.LinearAlgebra.Lattice.Mukai.AffineWeyl.LengthZeroGroup

/-!
# The length-zero group and the Coxeter group of the curve wall

On the elliptic K3 surface `X` with a section `C` (`EllipticWithSection/Lattice.lean`), the curve
wall contracts `C` (`sectionFibre`, type `A₁`, `Θ = C`). The fibre class has `F·C = 1`, so every
degree is realized (`degreeLattice_sectionFibre`), and `NS(X)` is even (`intersection_even`).
The general theorems of `LinearAlgebra/Lattice/Mukai/AffineWeyl/` then give, on the real classes:

* **the length-zero permutations form a group isomorphic to `P^∨/Q^∨`**
  (`sectionFibreLengthZeroPermEquiv`), of order `2 = det A₁`
  (`card_lengthZeroPerm_range_sectionFibre`);
* **the length-zero element at the minuscule node** is `⊗𝒪(F) ∘ w` with `w ∈ W(A₁)`, and it sends
  `wallA = v(𝒪_C)` to `wallB = v(𝒪_C(-1)[1])` (`exists_lengthZero_sectionFibre`); the element
  `lengthZero = ⊗𝒪(F) ∘ ρ_{wallB}` of `EllipticWithSection/AffineWeyl.lean` is a length-zero
  element of the extended affine Weyl group (`lengthZero_mem_lengthZeroGroup`);
* **the Coxeter matrix of the two spherical simples is `Ã₁`**: `⟨wallA, wallB⟩ = 2`
  (`affineExt_sectionFibre`), so `m = ∞` (`affineCoxeterMatrix_sectionFibre`); the reflection
  representation of `W(Ã₁)` has image `W_aff` (`range_affineWeylRep_sectionFibre`), and for
  `0 < β·C < 1` a word in the two reflections is root-positive iff the charge `β·c - s` is
  negative on each of its prefix roots (`isRootPositive_sectionFibre_iff`): the sign of the class
  for the Weyl galleries of the curve wall.

That `C` is the exceptional fibre of the contraction by `H = C + 2F` and that the simple objects
of the wall are `𝒪_C` and `𝒪_C(-1)[1]` are geometry and are not formalized.
-/

namespace AlgebraicGeometry.K3.EllipticWithSection

open Mukai Mukai.FundamentalCycle

/-- `NS(X)` is even. -/
theorem intersection_even (L : NS) : Even (intersection L L) :=
  ⟨L.1 * (L.2 - L.1), by rw [intersection_self]; ring⟩

/-! ### The length-zero group -/

/-- **The length-zero permutations of the curve wall form a group isomorphic to
`P^∨/Q^∨ = ℤ/2`.** -/
noncomputable def sectionFibreLengthZeroPermEquiv :
    sectionFibre.lengthZeroPerm.range ≃* Multiplicative ((Unit → ℤ) ⧸ sectionFibre.corootLattice) :=
  sectionFibre.lengthZeroPermEquivOfDegreeLattice intersection_comm intersection_even
    degreeLattice_sectionFibre

/-- **The group of length-zero permutations of the curve wall has order `2 = det A₁`.** -/
theorem card_lengthZeroPerm_range_sectionFibre :
    Nat.card sectionFibre.lengthZeroPerm.range = 2 := by
  rw [sectionFibre.card_lengthZeroPerm_range intersection_comm intersection_even
    degreeLattice_sectionFibre, det_cartan_sectionFibre]
  rfl

/-- **The length-zero element at the minuscule node of the curve wall**: `⊗𝒪(F) ∘ w` for some
`w ∈ W(A₁)` permutes the affine simple roots and sends `wallA` to `wallB`. -/
theorem exists_lengthZero_sectionFibre :
    ∃ w ∈ sectionFibre.finiteWeyl,
      tensorLineEquiv intersection_comm fibre two_mul_zero_eq_fibre * w ∈
          sectionFibre.affineRootStabilizer ∧
        (tensorLineEquiv intersection_comm fibre two_mul_zero_eq_fibre * w) wallA = wallB := by
  obtain ⟨w, hw, hstab, himg⟩ := sectionFibre.exists_lengthZero_of_minuscule intersection_comm
    (j := ()) rfl (M := fibre) (fun i => by simp [curve, fibre]) two_mul_zero_eq_fibre
  refine ⟨w, hw, hstab, ?_⟩
  rw [← sectionFibre_affineRoot_none, himg, sectionFibre_affineRoot_some]

/-- **`⊗𝒪(F) ∘ ρ_{wallB}` is a length-zero element of the extended affine Weyl group.** -/
theorem lengthZero_mem_lengthZeroGroup : lengthZero ∈ sectionFibre.lengthZeroGroup :=
  ⟨lengthZero_mem_affineRootStabilizer, mul_mem
    (Subgroup.mem_sup_right
      (Subgroup.subset_closure ⟨fibre, 0, two_mul_zero_eq_fibre, fun _ => rfl⟩))
    (Subgroup.mem_sup_left reflectEquiv_wallB_mem_affineWeyl)⟩

/-! ### The Coxeter group of the curve wall -/

/-- **`wallA` and `wallB` pair to `2`**: the total Ext number of `𝒪_C` and `𝒪_C(-1)[1]`. -/
theorem affineExt_sectionFibre : sectionFibre.affineExt none (some ()) = 2 := by
  simp [affineExt, sectionFibre_cycle, pairing, curve]

/-- **The Coxeter matrix of the curve wall is `Ã₁`**: `m(wallA, wallB) = ∞`, encoded as `0`. -/
theorem affineCoxeterMatrix_sectionFibre :
    sectionFibre.affineCoxeterMatrix intersection_comm none (some ()) = 0 := by
  simp [affineCoxeterMatrix, CoxeterMatrix.ofExt, affineExt_sectionFibre]

/-- **The reflection representation of `W(Ã₁)` on the Mukai lattice has image `W_aff`.** -/
theorem range_affineWeylRep_sectionFibre :
    (sectionFibre.affineWeylRep intersection_comm).range = sectionFibre.affineWeyl :=
  sectionFibre.range_affineWeylRep intersection_comm

/-- **The sign of the class on the curve wall.** For `0 < β·C < 1`, a word in the reflections in
`wallA` and `wallB` is root-positive iff the charge `β·c - s` is negative on each of its prefix
roots. -/
theorem isRootPositive_sectionFibre_iff {β : NS →+ ℝ} (h0 : 0 < β curve) (h1 : β curve < 1)
    (ω : List (Option Unit)) :
    BilinearForm.IsRootPositive (mukaiForm intersection) sectionFibre.affineRoot ω ↔
      ∀ v ∈ BilinearForm.prefixRoots (mukaiForm intersection) sectionFibre.affineRoot ω,
        fibreCharge β v < 0 :=
  sectionFibre.isRootPositive_affineRoot_iff intersection_comm
    ⟨fun _ => h0, by rwa [sectionFibre_cycle]⟩ ω

end AlgebraicGeometry.K3.EllipticWithSection
