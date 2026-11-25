/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.PicardRankOne.WallArithmetic
import K3Twists.Combinatorics.Quiver.Kronecker.CartanMatrix

/-!
# The wall matrix of a Picard-rank-one wall with two spherical simples

On a K3 surface with `Pic = ℤH`, `H² = 2d`, let `S₀`, `S₁` be spherical objects, stable of one
phase at a wall, with `⟨v(S₀), v(S₁)⟩ = g`; then `g = dim Ext¹(S₀, S₁) ≥ 0`, since `Hom` and
`Ext²` between them vanish. Their wall matrix `Aᵢⱼ = χ(Sᵢ, Sⱼ) = -⟨v(Sᵢ), v(Sⱼ)⟩` is
`[[2, -g], [-g, 2]]` (`wallMatrix_eq_cartanMatrix`), and `v(xS₀ + yS₁)² = -(x, y)ᵀ A (x, y)`
(`pairing_smul_add_smul_self`). By `Quiver.Kronecker.rank_two_trichotomy`:

* the wall is of finite type iff `g ≤ 1`, of affine type iff `g = 2`, and indefinite iff `g ≥ 3`
  (`wallMatrix_trichotomy`);
* for `|g| ≥ 3` the span of the two classes has no rational isotropic vector
  (`span_roots_anisotropic_of_wallMatrix`, the statement of `span_roots_anisotropic` read off the
  wall matrix), and the two spheres have no isotropic sum (`noIsotropicSphereSum_wallMatrix`).

**An instance from the library's classes**: `v(𝒪_X) = (1, 0, 1)` and
`v(𝒪_X(-H)[1]) = -(1, -1, d + 1)` (`MukaiVector.lineBundle`) pair to `d + 2`. Indeed
`Hom(𝒪_X, 𝒪_X(-H)[1]) = H¹(𝒪_X(-H)) = 0`, `Hom(𝒪_X(-H)[1], 𝒪_X) = 0`, and
`dim Ext¹(𝒪_X(-H)[1], 𝒪_X) = h⁰(𝒪_X(H)) = d + 2` by Kodaira vanishing and Riemann–Roch. So
where these two objects are stable of one phase the wall has `g = d + 2 ≥ 3`: it is indefinite,
and no nonzero nonnegative combination of them has an isotropic class
(`structureSheaf_shift_wall`).
-/

namespace AlgebraicGeometry.K3.PicardRankOne

open Matrix Quiver.Kronecker MukaiVector

/-- The wall matrix `Aᵢⱼ = -⟨sᵢ, sⱼ⟩` of a family of Mukai vectors (the matrix of Euler
characteristics `χ(Sᵢ, Sⱼ)` of objects of those classes). -/
def wallMatrix {R : Type*} [CommRing R] {ι : Type*} (d : R) (s : ι → MukaiVector R) :
    Matrix ι ι R :=
  Matrix.of fun i j => -MukaiVector.pairing d (s i) (s j)

section CommRing

variable {R : Type*} [CommRing R]

/-- **Two roots of pairing `g`** have wall matrix `[[2, -g], [-g, 2]]`. -/
theorem wallMatrix_eq_cartanMatrix {d : R} {s₀ s₁ : MukaiVector R} (h₀ : IsRoot d s₀)
    (h₁ : IsRoot d s₁) {g : R} (h01 : MukaiVector.pairing d s₀ s₁ = g) :
    wallMatrix d ![s₀, s₁] = cartanMatrix g := by
  unfold IsRoot at h₀ h₁
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wallMatrix, cartanMatrix, h₀, h₁, h01, MukaiVector.pairing_comm d s₁ s₀]

/-- **The Tits identity for two classes.** `⟨xs₀ + ys₁, xs₀ + ys₁⟩ = -(x, y)ᵀ A (x, y)`. -/
theorem pairing_smul_add_smul_self (d : R) (s₀ s₁ : MukaiVector R) (x y : R) :
    MukaiVector.pairing d (x • s₀ + y • s₁) (x • s₀ + y • s₁) =
      -(![x, y] ⬝ᵥ wallMatrix d ![s₀, s₁] *ᵥ ![x, y]) := by
  simp only [pairing_add_left, pairing_add_right, pairing_smul_left, pairing_smul_right,
    wallMatrix, dotProduct, mulVec, Fin.sum_univ_two, of_apply, cons_val_zero, cons_val_one,
    MukaiVector.pairing_comm d s₁ s₀]
  ring

end CommRing

/-- **The trichotomy of a Picard-rank-one wall.** Two integral roots of pairing `g ∈ ℕ` span a
wall of finite type iff `g ≤ 1`, of affine type iff `g = 2`, and indefinite iff `g ≥ 3`. -/
theorem wallMatrix_trichotomy {d : ℤ} {s₀ s₁ : MukaiVector ℤ} (h₀ : IsRoot d s₀)
    (h₁ : IsRoot d s₁) {g : ℕ} (h01 : MukaiVector.pairing d s₀ s₁ = g) :
    ((wallMatrix d ![s₀, s₁]).PosDef ↔ g ≤ 1) ∧
      ((wallMatrix d ![s₀, s₁]).PosSemidef ∧ ¬(wallMatrix d ![s₀, s₁]).PosDef ↔ g = 2) ∧
      (¬(wallMatrix d ![s₀, s₁]).PosSemidef ↔ 3 ≤ g) := by
  rw [wallMatrix_eq_cartanMatrix h₀ h₁ h01]
  exact rank_two_trichotomy g

/-- `span_roots_anisotropic` from the wall matrix: two spherical classes of pairing `g`,
`|g| ≥ 3`, span no rational isotropic class, because their wall matrix is anisotropic. -/
theorem span_roots_anisotropic_of_wallMatrix {d : ℚ} {s₀ s₁ : MukaiVector ℚ}
    (h₀ : IsRoot d s₀) (h₁ : IsRoot d s₁) {g : ℤ} (hg : 3 ≤ |g|)
    (h01 : MukaiVector.pairing d s₀ s₁ = g) {x y : ℚ} (hiso : IsIsotropic d (x • s₀ + y • s₁)) :
    x = 0 ∧ y = 0 := by
  unfold IsIsotropic at hiso
  rw [pairing_smul_add_smul_self, wallMatrix_eq_cartanMatrix h₀ h₁ h01, neg_eq_zero] at hiso
  have h := cartanMatrix_anisotropic hg hiso
  exact ⟨by simpa using congr_fun h 0, by simpa using congr_fun h 1⟩

/-- Two integral roots of pairing `|g| ≥ 3` have no isotropic sum. -/
theorem noIsotropicSphereSum_wallMatrix {d : ℤ} {s₀ s₁ : MukaiVector ℤ} (h₀ : IsRoot d s₀)
    (h₁ : IsRoot d s₁) {g : ℤ} (hg : 3 ≤ |g|) (h01 : MukaiVector.pairing d s₀ s₁ = g) :
    (wallMatrix d ![s₀, s₁]).NoIsotropicSphereSum := by
  rw [wallMatrix_eq_cartanMatrix h₀ h₁ h01]
  exact noIsotropicSphereSum_cartanMatrix hg

/-- `v(𝒪_X)` and `v(𝒪_X(-H)[1]) = -v(𝒪_X(-H))` pair to `d + 2`. -/
lemma pairing_structureSheaf_shift {R : Type*} [CommRing R] (d : R) :
    MukaiVector.pairing d (lineBundle d 0) (-lineBundle d (-1)) = d + 2 := by
  rw [pairing_neg_right, pairing_lineBundle]
  ring

/-- **The wall of `𝒪_X` and `𝒪_X(-H)[1]`.** For `d ≥ 1` their wall matrix is
`[[2, -(d + 2)], [-(d + 2), 2]]`: indefinite, with no isotropic sum. -/
theorem structureSheaf_shift_wall {d : ℤ} (hd : 1 ≤ d) :
    wallMatrix d ![lineBundle d 0, -lineBundle d (-1)] = cartanMatrix (d + 2) ∧
      ¬(wallMatrix d ![lineBundle d 0, -lineBundle d (-1)]).PosSemidef ∧
      (wallMatrix d ![lineBundle d 0, -lineBundle d (-1)]).NoIsotropicSphereSum := by
  have hneg : IsRoot d (-lineBundle d (-1)) := by
    unfold IsRoot
    rw [pairing_neg_left, pairing_neg_right, neg_neg]
    exact isRoot_lineBundle d (-1)
  have hW := wallMatrix_eq_cartanMatrix (isRoot_lineBundle d 0) hneg
    (pairing_structureSheaf_shift d)
  have hg : 3 ≤ |d + 2| := by rw [abs_of_nonneg (by linarith)]; linarith
  refine ⟨hW, ?_, ?_⟩
  · rw [hW, (cartanMatrix_isSymm _).posSemidef_iff_dotProduct_mulVec_nonneg]
    intro h
    have h1 := h fun _ => 1
    rw [dotProduct_mulVec_cartanMatrix] at h1
    simp at h1
    linarith
  · rw [hW]
    exact noIsotropicSphereSum_cartanMatrix hg

end AlgebraicGeometry.K3.PicardRankOne
