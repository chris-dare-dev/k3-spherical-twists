/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.EllipticWithSection.Lattice
import K3Twists.AlgebraicGeometry.Surface.K3.PairingTwoWall
import K3Twists.Combinatorics.Quiver.Kronecker.CartanMatrix

/-!
# The wall matrix of the curve wall and of a wall of pairing two

On the elliptic K3 surface `X` with a section `C` of `EllipticWithSection/Lattice.lean`, the
spherical simples of the wall where `C` is contracted are `A = 𝒪_C` and `B = 𝒪_C(-1)[1]`, of
classes `wallA`, `wallB`. Their wall matrix `χ(Sᵢ, Sⱼ) = -⟨v(Sᵢ), v(Sⱼ)⟩` is
`[[2, -2], [-2, 2]]`, the Cartan matrix of the `2`-Kronecker quiver (`wallMatrix_curveWall`):

* the curve wall is of **affine type** (`curveWall_posSemidef_and_not_posDef`), with null vector
  `(1, 1)`, the class `v(A) + v(B) = v(𝒪_x)` of a point;
* by the affine kernel, the isotropic classes `aA + bB` are exactly the multiples of `v(𝒪_x)`
  (`isIsotropic_wallClass_iff`), and `A + B` is an isotropic sum of spheres
  (`not_noIsotropicSphereSum_curveWall`);
* the Tits identity gives `v(aA + bB)² = -(a, b)ᵀ A (a, b) = -2 q₂(a, b)`
  (`selfPairing_wallClass_eq_neg_dotProduct`), the statement of
  `selfPairing_wallClass_eq_kroneckerForm` read off the wall matrix.

The wall of `PairingTwoWallHypotheses` has the same wall matrix: `dim Ext¹(B, A) = 2` between two
spherical simples. For a class map additive on the short exact sequences of that structure, `P`
and `U` have multiplicities `(1, 1)` (the null vector) and `M` has `(2, 1)`
(`PairingTwoWallHypotheses.cl_P`, `cl_M`, `cl_U`); with the Mukai form of two spherical classes
of pairing two, `P` and `U` are isotropic and `M` is spherical
(`PairingTwoWallHypotheses.selfPairing_cl`). At the curve wall these are the classes of
`𝒪_x`, of `𝒪_X/(I_C I_x)` and of `T_A 𝒪_x` (`curveWall_pairingTwoWall_classes`). That the
geometric objects form the extensions of `PairingTwoWallHypotheses` is cited, not formalized.
-/

namespace AlgebraicGeometry.K3

open CategoryTheory Matrix Quiver.Kronecker

namespace EllipticWithSection

open Mukai

/-- The spherical simples `A = 𝒪_C` and `B = 𝒪_C(-1)[1]` of the curve wall, as a family. -/
def curveWallSimples : Fin 2 → MukaiLattice ℤ NS := ![wallA, wallB]

/-- **The wall matrix of the curve wall** is `[[2, -2], [-2, 2]]`. -/
theorem wallMatrix_curveWall :
    LinearMap.BilinForm.wallMatrix (mukaiForm intersection) curveWallSimples =
      cartanMatrix (2 : ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [curveWallSimples, cartanMatrix, wallA, wallB]

/-- **The Tits identity on the curve wall.** `v(aA + bB)² = -(a, b)ᵀ A (a, b)` for the wall
matrix `A = [[2, -2], [-2, 2]]`; with `dotProduct_mulVec_cartanMatrix_eq_kroneckerForm` this is
`-2 q₂(a, b)`. -/
theorem selfPairing_wallClass_eq_neg_dotProduct (a b : ℤ) :
    selfPairing intersection (wallClass a b) = -(![a, b] ⬝ᵥ cartanMatrix (2 : ℤ) *ᵥ ![a, b]) := by
  rw [← wallMatrix_curveWall, ← LinearMap.BilinForm.apply_sum_smul_self]
  simp only [Fin.sum_univ_two, curveWallSimples, cons_val_zero, cons_val_one, mukaiForm_apply]
  rfl

/-- **The curve wall is of affine type**: its wall matrix is positive semidefinite and not
positive definite. -/
theorem curveWall_posSemidef_and_not_posDef :
    (LinearMap.BilinForm.wallMatrix (mukaiForm intersection) curveWallSimples).PosSemidef ∧
      ¬(LinearMap.BilinForm.wallMatrix (mukaiForm intersection) curveWallSimples).PosDef := by
  rw [wallMatrix_curveWall]
  simpa using (posSemidef_and_not_posDef_cartanMatrix_iff 2).mpr rfl

/-- The null vector `(1, 1)` of the curve wall is the class of a point. -/
theorem sum_curveWallSimples_null :
    (LinearMap.BilinForm.wallMatrix (mukaiForm intersection) curveWallSimples) *ᵥ
      (fun _ => 1) = 0 ∧
      ∑ i, (1 : ℤ) • curveWallSimples i = point := by
  rw [wallMatrix_curveWall]
  exact ⟨cartanMatrix_two_mulVec_one, by simp [curveWallSimples, Fin.sum_univ_two,
    wallA_add_wallB]⟩

/-- **The isotropic classes of the curve wall** are the multiples of `v(𝒪_x)`: a wall class
`aA + bB` is isotropic iff it is `a·v(𝒪_x)`. Derived from the affine kernel of the wall
matrix. -/
theorem isIsotropic_wallClass_iff (a b : ℤ) :
    IsIsotropic intersection (wallClass a b) ↔ wallClass a b = a • point := by
  constructor
  · intro h
    rw [IsIsotropic, selfPairing_wallClass_eq_neg_dotProduct, neg_eq_zero] at h
    have hab := congr_fun (cartanMatrix_two_isotropic_eq_zsmul h) 1
    simp only [cons_val_one, cons_val_zero, Pi.smul_apply, smul_eq_mul, mul_one] at hab
    rw [hab, point_eq_wallClass]
    ext <;> simp
  · intro h
    rw [IsIsotropic, h, selfPairing_smul, isIsotropic_point, mul_zero]

/-- `A + B = 𝒪_x` is an isotropic sum of the two spherical simples. -/
theorem not_noIsotropicSphereSum_curveWall :
    ¬(LinearMap.BilinForm.wallMatrix (mukaiForm intersection)
      curveWallSimples).NoIsotropicSphereSum := by
  rw [wallMatrix_curveWall]
  exact not_noIsotropicSphereSum_cartanMatrix_two

/-- **The pairing-two wall at the curve wall.** `P = 𝒪_x` and `U = T_A 𝒪_x` have the class
`v(A) + v(B)` of the null vector; `M = 𝒪_X/(I_C I_x)` has the class `2v(A) + v(B)` and is
spherical. -/
theorem curveWall_pairingTwoWall_classes :
    point = wallClass 1 1 ∧ reflect intersection wallA point = wallClass 1 1 ∧
      embeddedPoint 0 = wallClass 2 1 ∧ IsIsotropic intersection (wallClass 1 1) ∧
      IsSpherical intersection (wallClass 2 1) := by
  refine ⟨point_eq_wallClass, by rw [reflect_wallA_point, point_eq_wallClass],
    by simpa using embeddedPoint_eq_wallClass 0, ?_, ?_⟩
  · rw [IsIsotropic, selfPairing_wallClass]; ring
  · rw [IsSpherical, selfPairing_wallClass]; ring

end EllipticWithSection

namespace PairingTwoWallHypotheses

variable {C : Type*} [Category C] [Abelian C] (W : PairingTwoWallHypotheses C)
  {L : Type*} [AddCommGroup L] (cl : C → L)
  (hcl : ∀ S : ShortComplex C, S.ShortExact → cl S.X₂ = cl S.X₁ + cl S.X₃)

include hcl

/-- For a class map additive on short exact sequences, `[P] = [A] + [B]`. -/
lemma cl_P : cl W.P = cl W.A + cl W.B :=
  hcl _ W.shortExact_P

/-- `[M] = 2[A] + [B]`: `M` has multiplicities `(2, 1)`. -/
lemma cl_M : cl W.M = 2 • cl W.A + cl W.B := by
  rw [hcl _ W.shortExact_M, W.cl_P cl hcl, two_nsmul]
  dsimp
  abel

/-- `[U] = [A] + [B]`. -/
lemma cl_U : cl W.U = cl W.A + cl W.B := by
  rw [hcl _ W.shortExact_U]
  dsimp
  abel

/-- **The wall matrix of a wall of pairing two.** If the classes of the simples are spherical and
pair to two for a symmetric bilinear form `B` (the Mukai form, `χ(A, B) = -2`), the wall matrix of
`([A], [B])` is `[[2, -2], [-2, 2]]`, so `P` and `U` lie on its null line and are isotropic, and
`M` is spherical. -/
theorem selfPairing_cl (B : LinearMap.BilinForm ℤ L) (hAA : B (cl W.A) (cl W.A) = -2)
    (hBB : B (cl W.B) (cl W.B) = -2) (hAB : B (cl W.A) (cl W.B) = 2)
    (hBA : B (cl W.B) (cl W.A) = 2) :
    B.wallMatrix ![cl W.A, cl W.B] = cartanMatrix (2 : ℤ) ∧ B (cl W.P) (cl W.P) = 0 ∧
      B (cl W.U) (cl W.U) = 0 ∧ B (cl W.M) (cl W.M) = -2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [cartanMatrix, hAA, hBB, hAB, hBA]
  · rw [W.cl_P cl hcl]
    simp [hAA, hBB, hAB, hBA]
  · rw [W.cl_U cl hcl]
    simp [hAA, hBB, hAB, hBA]
  · rw [W.cl_M cl hcl]
    simp [hAA, hBB, hAB, hBA]

end PairingTwoWallHypotheses

end AlgebraicGeometry.K3
