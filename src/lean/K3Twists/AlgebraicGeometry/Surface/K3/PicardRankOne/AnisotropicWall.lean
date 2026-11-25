/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.PicardRankOne.WallMatrix
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.WallStep

/-!
# In Picard rank one every wall is anisotropic, and the tower theorem follows

Let `X` be a K3 surface with `Pic X = ℤH`, `H² = 2d`, and let a named wall (`WallStep`) have its
class map in the Mukai lattice `MukaiVector ℤ` with the Mukai pairing. This file proves that every
phase of such a wall has no isotropic sum of stable sphere classes, from two cited facts and the
lattice:

* **at most two sphere types**: in Picard rank one a phase of a wall has at most two stable
  spherical objects up to isomorphism (Bayer–Bridgeland, arXiv:1310.8266, Lemma 3.3 and
  Proposition 3.4);
* **Riemann–Roch**: the class of a stable rigid object is a root, `v² = -2` (Mukai; Huybrechts,
  *Fourier–Mukai transforms in algebraic geometry*, Ch. 10).

Then (`RankOneWall.anisotropic`): one sphere has no isotropic sum (`Matrix.noIsotropic_one`); two
spheres of pairing `g` have one only at `g = 2` (`Matrix.isotropicSphereSum_two_iff`, which
contains `Matrix.noIsotropic_two`); and `g = 2` does not occur between two stable spheres of one
phase in Picard rank one, because two roots of pairing `2` are opposite
(`MukaiVector.eq_neg_of_pairing_eq_two`, a lattice computation: `s + t` would be isotropic and
orthogonal to the root `s`, while the orthogonal complement of an isotropic vector of the
rank-one lattice is positive semidefinite) and two nonzero semistable objects of one phase do not
have opposite classes (`PreStabilityCondition.WithClassMap.classOf_ne_neg`).

So the tower theorem of Picard rank one follows from the split tower theorem over paths of named
walls (`WallTowerHypotheses.tower_of_rankOne`), with the Gram matrices of the stable spheres of each
wall and their anisotropy proved, not assumed, and with no empty Gram matrices. That "Picard rank
one enters only as anisotropy" is the draft's reading; here it is what this proof uses.

## Real objects

The structure `RankOneWall` and the fields of `WallStep` have no instance built from real objects:
the library has no 2-Calabi–Yau triangulated category of a K3 surface, so no stability condition on
`D^b(X)`, its stable objects, their constituents, or the rank-one count of sphere types. The Gram
matrices of named walls are computed from the library's classes: the wall of `𝒪_X` and `𝒪_X(-H)[1]`
has Gram matrix `[[-2, d + 2], [d + 2, -2]]` and is anisotropic for `d ≥ 1`
(`gram_structureSheaf_shift`, `WallStep.anisotropic_of_structureSheaf_shift`).

## Main results

* `MukaiVector.eq_neg_of_pairing_eq_two`: two roots of pairing `2` are opposite.
* `RankOneWall.anisotropic`: a rank-one wall has no isotropic sphere sum at any phase.
* `WallTowerHypotheses.tower_of_rankOne`: the tower theorem in Picard rank one, through the split
  tower theorem.
* `gram_structureSheaf_shift`, `WallStep.anisotropic_of_structureSheaf_shift`: the wall of `𝒪_X`
  and `𝒪_X(-H)[1]`.

## Tags

K3 surface, Picard rank one, wall, spherical object, Gram matrix, isotropic, tower
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated Matrix

universe w u

namespace MukaiVector

/-- **Two roots of pairing two are opposite** in the Mukai lattice of Picard rank one. With
`u = s + t`, `u² = 0` and `⟨s, u⟩ = 0`; writing `Q(r, c, x) = dc² - rx` (half the square),
`R²·Q(s) = d(cR - rK)²` for `u = (R, K, ·)`, so `Q(s) = -1` forces `R = 0`, then `K = 0`, then
`u = 0`. -/
theorem eq_neg_of_pairing_eq_two {d : ℤ} (hd : 0 < d) {s t : MukaiVector ℤ} (hs : IsRoot d s)
    (ht : IsRoot d t) (hst : pairing d s t = 2) : t = -s := by
  obtain ⟨r, c, x⟩ := s
  obtain ⟨r', c', x'⟩ := t
  simp only [IsRoot, pairing] at hs ht hst
  have hE1 : 2 * (d * (c + c') ^ 2 - (r + r') * (x + x')) = 0 := by
    linear_combination hs + ht + 2 * hst
  have hE2 : 2 * d * c * (c + c') - r * (x + x') - (r + r') * x = 0 := by
    linear_combination hs + hst
  have key : 2 * (r + r') ^ 2 + 2 * d * (c * (r + r') - r * (c + c')) ^ 2 = 0 := by
    linear_combination (r + r') ^ 2 * hs + r ^ 2 * hE1 - 2 * r * (r + r') * hE2
  have hR : r + r' = 0 := by
    have h1 : 0 ≤ d * (c * (r + r') - r * (c + c')) ^ 2 := by positivity
    have h2 : (r + r') ^ 2 = 0 := by nlinarith [sq_nonneg (r + r')]
    exact pow_eq_zero_iff (two_ne_zero) |>.mp h2
  have hK : c + c' = 0 := by
    rw [hR, zero_mul, sub_zero] at hE1
    have : (c + c') ^ 2 = 0 := by
      have := (mul_eq_zero.mp ((mul_eq_zero.mp hE1).resolve_left two_ne_zero)).resolve_left hd.ne'
      exact this
    exact pow_eq_zero_iff two_ne_zero |>.mp this
  have hX : x + x' = 0 := by
    rw [hK, hR, mul_zero, zero_mul, zero_sub, sub_zero, neg_eq_zero] at hE2
    rcases mul_eq_zero.mp hE2 with h | h
    · subst h
      nlinarith [sq_nonneg c]
    · exact h
  ext <;> simp <;> lia

end MukaiVector

namespace AlgebraicGeometry.K3.PicardRankOne

open MukaiVector

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {b : MukaiBudget C} {d : ℤ} {v : K₀ C →+ MukaiVector ℤ} {carrier : Slicing C → ObjectProperty C}
  {t₁ t₂ : Slicing C}

/-- **The Picard-rank-one inputs at a wall.** The classes of stable spheres are roots, and each
phase has at most two sphere types. -/
structure RankOneWall (W : WallStep b (mukaiForm d) v carrier t₁ t₂) : Prop where
  /-- **Riemann–Roch**: a stable rigid object `S` has `End(S) = k`, `Ext¹(S, S) = 0` and, by Serre
  duality, `Ext²(S, S) = k`, so `v(S)² = -χ(S, S) = -2` (Mukai; Huybrechts, *Fourier–Mukai
  transforms in algebraic geometry*, Ch. 10). -/
  isRoot : ∀ φ S, W.IsSphere φ S → IsRoot d (classOf C v S)
  /-- Finitely many sphere types in each phase. -/
  finite : ∀ φ, Finite (W.SphereType φ)
  /-- **At most two sphere types** in each phase of a wall, in Picard rank one
  (Bayer–Bridgeland, arXiv:1310.8266, Lemma 3.3 and Proposition 3.4). -/
  card_le_two : ∀ φ, Nat.card (W.SphereType φ) ≤ 2

namespace RankOneWall

variable {W : WallStep b (mukaiForm d) v carrier t₁ t₂}

theorem isRoot_sphereClass (hW : RankOneWall W) {φ : ℝ} (i : W.SphereType φ) :
    IsRoot d (W.sphereClass φ i) := by
  obtain ⟨S, hS, rfl⟩ := WallStep.SphereType.exists_eq_mk W i
  exact hW.isRoot φ S hS

/-- **A wall in Picard rank one is anisotropic**: no phase has an isotropic sum of the classes of
its stable spheres. -/
theorem anisotropic (hd : 0 < d) (hW : RankOneWall W) : W.Anisotropic := by
  intro φ hiso
  haveI := hW.finite φ
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin (W.SphereType φ)
  have hn : n ≤ 2 := by
    have := hW.card_le_two φ
    rwa [Nat.card_eq_of_equiv_fin e] at this
  rw [← isotropicSphereSum_submatrix_equiv (W.gram φ) e.symm] at hiso
  have hdiag : ∀ i, (W.gram φ).submatrix e.symm e.symm i i = -2 := fun i =>
    hW.isRoot_sphereClass (e.symm i)
  interval_cases n
  · exact not_isotropicSphereSum_of_isEmpty _ hiso
  · exact noIsotropic_one _ (hdiag 0) hiso
  · set g := (W.gram φ).submatrix e.symm e.symm 0 1 with hg
    have hG : (W.gram φ).submatrix e.symm e.symm = !![-2, g; g, -2] := by
      ext i j
      fin_cases i <;> fin_cases j
      · exact hdiag 0
      · rfl
      · simp only [hg, submatrix_apply, WallStep.gram_apply, mukaiForm_apply]
        exact pairing_comm d _ _
      · exact hdiag 1
    rw [hG, isotropicSphereSum_two_iff] at hiso
    obtain ⟨S₀, hS₀, h₀⟩ := WallStep.SphereType.exists_eq_mk W (e.symm 0)
    obtain ⟨S₁, hS₁, h₁⟩ := WallStep.SphereType.exists_eq_mk W (e.symm 1)
    have hpair : pairing d (classOf C v S₀) (classOf C v S₁) = 2 := by
      rw [← hiso, hg, submatrix_apply, WallStep.gram_apply, h₀, h₁]
      rfl
    have hneg := eq_neg_of_pairing_eq_two hd (hW.isRoot φ S₀ hS₀) (hW.isRoot φ S₁ hS₁) hpair
    exact W.wall.classOf_ne_neg (W.semistable_of_stable φ S₀ hS₀.1)
      (W.nonzero_of_stable φ S₀ hS₀.1) (W.semistable_of_stable φ S₁ hS₁.1)
      (W.nonzero_of_stable φ S₁ hS₁.1) hneg

end RankOneWall

/-- **The tower theorem in Picard rank one, through the split tower theorem.** If every wall along
the paths satisfies the rank-one inputs, every wall is anisotropic, and at the target exactly one
HN factor of `W 𝒪_x` carries the point, once, and every other factor is spherical. The Gram
matrices are those of the stable spheres of each wall; none is empty by construction. -/
theorem WallTowerHypotheses.tower_of_rankOne (T : WallTowerHypotheses C (mukaiForm d) v)
    (hd : 0 < d) (hleg : ∀ j k (hk : k < (T.leg j).n), RankOneWall ((T.leg j).step k hk))
    (hfinal : ∀ k (hk : k < T.final.n), RankOneWall (T.final.step k hk)) :
    T.target.CarriesOnce (T.carrier T.target) (T.spherical T.target) (T.word T.length) :=
  T.tower (fun j k hk => (hleg j k hk).anisotropic hd) (fun k hk => (hfinal k hk).anisotropic hd)

/-! ### The wall of `𝒪_X` and `𝒪_X(-H)[1]` -/

/-- **The Gram matrix of `𝒪_X` and `𝒪_X(-H)[1]`**: `[[-2, d + 2], [d + 2, -2]]`. -/
theorem gram_structureSheaf_shift (d : ℤ) :
    BilinearForm.gram (mukaiForm d) ![lineBundle d 0, -lineBundle d (-1)] =
      !![-2, d + 2; d + 2, -2] := by
  have h01 := pairing_structureSheaf_shift d
  have h00 := isRoot_lineBundle d 0
  have h11 : IsRoot d (-lineBundle d (-1)) := by
    unfold IsRoot
    rw [pairing_neg_left, pairing_neg_right, neg_neg]
    exact isRoot_lineBundle d (-1)
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact (pairing_comm d _ _).trans h01
  · exact h11

/-- **The wall of `𝒪_X` and `𝒪_X(-H)[1]` has no isotropic sphere sum** for `d ≥ 1`. -/
theorem not_isotropicSphereSum_structureSheaf_shift {d : ℤ} (hd : 1 ≤ d) :
    ¬(BilinearForm.gram (mukaiForm d)
      ![lineBundle d 0, -lineBundle d (-1)]).IsotropicSphereSum := by
  rw [gram_structureSheaf_shift]
  exact noIsotropic_two (by rw [abs_of_nonneg (by lia)]; lia)

/-- **A named wall in Picard rank one.** If the sphere types of phase `φ` of a wall are `𝒪_X` and
`𝒪_X(-H)[1]`, that is, they are indexed by `Fin 2` with these classes, then the phase has no
isotropic sphere sum: the Gram matrix of the stable spheres of a named wall slicing, computed
from the library's classes. -/
theorem WallStep.anisotropic_of_structureSheaf_shift
    (W : WallStep b (mukaiForm d) v carrier t₁ t₂) (hd : 1 ≤ d) {φ : ℝ}
    (e : W.SphereType φ ≃ Fin 2)
    (hc : ∀ i, W.sphereClass φ (e.symm i) = ![lineBundle d 0, -lineBundle d (-1)] i) :
    ¬(W.gram φ).IsotropicSphereSum := by
  rw [W.isotropicSphereSum_gram_iff_of_equiv e _ hc]
  exact not_isotropicSphereSum_structureSheaf_shift hd

end AlgebraicGeometry.K3.PicardRankOne
