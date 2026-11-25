/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.EllipticWithSection.Braid
import K3Twists.GroupTheory.Coxeter.GeometricRepresentation

/-!
# The `A₂` Weyl gallery on the elliptic K3 surface, on classes

On an elliptic K3 surface `X` with a section `C`, the Mukai vectors `α₀ = v(𝒪_X[1]) = -(1, 0, 1)`
and `α₁ = v(𝒪_C) = (0, C, 1)` have norm `-2` and pair to `1` (`a2`, `pairing_a2`): their Gram
matrix is `rootMatrix (extA 2)`, the `A₂` matrix in the Mukai sign. This file instantiates, on
these real classes, every class-level input of the Weyl-gallery theorems of
`CategoryTheory.Triangulated.WeylGalleryHypotheses`:

* the two reduced words `[0, 1, 0]` and `[1, 0, 1]` of the longest element `w₀` of `W(A₂)` are
  root-positive for the Mukai pairing, with prefix roots `α₀, α₀ + α₁, α₁` and `α₁, α₀ + α₁, α₀`
  (`isRootPositive_a2_longest`, `prefixRoots_a2_longest`);
* they have the same image in the Artin group (the braid relation, `ofSignedWord_a2_longest`);
* `w₀(α_i) = -α_{1-i}`, and the prefixes `[0, 1]`, `[1, 0]` send `α₀ ↦ α₁` and `α₁ ↦ α₀`
  (`reflectWord_a2_longest`, `reflectWord_a2_prefix`), so the diagram automorphism is the swap;
* the two classes are linearly independent (`linearIndependent_a2`).

These are the hypotheses of `WeylGalleryHypotheses.longest_obj_iso_shift` that concern classes.
Given the categorical fields, with a heart in which `𝒪_X[1]` and `𝒪_C` are simple, that theorem
gives `F_{w₀} 𝒪_X[1] ≅ 𝒪_C[-1]` and `F_{w₀} 𝒪_C ≅ 𝒪_X` for
`F_{w₀} = T_{𝒪_X} T_{𝒪_C} T_{𝒪_X}`. The categorical fields have no instance:
the configuration `conf` needs the twist functors `T_{𝒪_X}`, `T_{𝒪_C}` of `D^b(X)`, and the
simple-tilt and tilt-composition fields need a heart of `D^b(X)` in which `𝒪_X[1]` and `𝒪_C` are
simple; Mathlib has neither the derived category of a K3 surface with its twist functors nor
tilts of hearts. The class identities are what the library proves here.

The computations are done once on `ℤ²` (`CoxeterMatrix.isRootPositive_longestWordA`,
`CoxeterMatrix.stdWord_longestWordA`) and transferred along `e_i ↦ α_i`
(`BilinearForm.IsRootPositive.of_rootForm`, `CoxeterMatrix.reflectWord_of_rootForm`).
-/

namespace AlgebraicGeometry.K3.EllipticWithSection

open Mukai CoxeterMatrix

/-- The classes `α₀ = v(𝒪_X[1])`, `α₁ = v(𝒪_C)` as vectors of the Mukai lattice. -/
def a2Class (i : Fin 2) : MukaiLattice ℤ NS := (a2 i).1

theorem a2Class_zero : a2Class 0 = -lineBundle 0 := rfl

theorem a2Class_one : a2Class 1 = curveSheaf 0 := rfl

/-- The Gram matrix of `α₀, α₁` for the Mukai pairing is `rootMatrix (extA 2)`. -/
theorem mukaiForm_a2Class (i j : Fin 2) :
    mukaiForm intersection (a2Class j) (a2Class i) = rootMatrix (extA 2) j i := by
  fin_cases i <;> fin_cases j <;>
    simp [a2Class, a2, curve, rootMatrix, extA]

theorem mukaiForm_a2Class_self (i : Fin 2) :
    mukaiForm intersection (a2Class i) (a2Class i) = -2 := by
  rw [mukaiForm_a2Class]; simp [rootMatrix]

/-- `α₀` and `α₁` are linearly independent. -/
theorem linearIndependent_a2 : LinearIndependent ℤ a2Class := by
  refine Fintype.linearIndependent_iff.2 fun g hg => ?_
  simp only [Fin.sum_univ_two, a2Class, a2] at hg
  have h1 := congrArg Prod.fst hg
  have h2 := congrArg (fun v => v.2.1.1) hg
  simp [lineBundle, curveSheaf, curve] at h1 h2
  intro i
  fin_cases i
  · simpa using h1
  · simpa using h2

/-- The reduced word `[0, 1, 0]` of `w₀`, and its braid image `[1, 0, 1]`. -/
theorem longestWordA_two : longestWordA 2 = [0, 1, 0] := rfl

/-- **Both reduced words of `w₀` are root-positive** on the classes of `𝒪_X[1]` and `𝒪_C`. -/
theorem isRootPositive_a2_longest :
    BilinearForm.IsRootPositive (mukaiForm intersection) a2Class [0, 1, 0] ∧
      BilinearForm.IsRootPositive (mukaiForm intersection) a2Class [1, 0, 1] := by
  have h₁ : BilinearForm.IsRootPositive (rootForm (extA 2)) stdRoot [1, 0, 1] :=
    isRootPositive_rootForm_of _ (by decide)
  exact ⟨(isRootPositive_longestWordA (n := 2) (by norm_num)).of_rootForm _ mukaiForm_a2Class,
    h₁.of_rootForm _ mukaiForm_a2Class⟩

/-- The prefix roots are `α₀, α₀ + α₁, α₁` and `α₁, α₀ + α₁, α₀`. -/
theorem prefixRoots_a2_longest :
    BilinearForm.prefixRoots (mukaiForm intersection) a2Class [0, 1, 0] =
        [a2Class 0, a2Class 0 + a2Class 1, a2Class 1] ∧
      BilinearForm.prefixRoots (mukaiForm intersection) a2Class [1, 0, 1] =
        [a2Class 1, a2Class 0 + a2Class 1, a2Class 0] := by
  have h01 := mukaiForm_a2Class 0 1
  have h10 := mukaiForm_a2Class 1 0
  have h00 := mukaiForm_a2Class_self 0
  have h11 := mukaiForm_a2Class_self 1
  simp only [rootMatrix, extA, Matrix.of_apply] at h01 h10
  norm_num at h01 h10
  constructor
  · simp [BilinearForm.prefixRoots, BilinearForm.reflect_apply, h01, h10, h00]
    abel
  · simp [BilinearForm.prefixRoots, BilinearForm.reflect_apply, h01, h10, h11]

/-- `w₀(α_i) = -α_{1-i}` on the Mukai lattice. -/
theorem reflectWord_a2_longest (i : Fin 2) :
    BilinearForm.reflectWord (mukaiForm intersection) a2Class [0, 1, 0] (a2Class i) =
      -a2Class i.rev := by
  have h := reflectWord_of_rootForm (extA 2) mukaiForm_a2Class (longestWordA 2) (stdRoot i)
  rw [rootMap_stdRoot, stdWord_longestWordA (by norm_num), map_neg, rootMap_stdRoot] at h
  exact h

/-- The prefixes `[0, 1]` and `[1, 0]` send `α₀ ↦ α₁` and `α₁ ↦ α₀`. -/
theorem reflectWord_a2_prefix :
    BilinearForm.reflectWord (mukaiForm intersection) a2Class [0, 1] (a2Class 0) = a2Class 1 ∧
      BilinearForm.reflectWord (mukaiForm intersection) a2Class [1, 0] (a2Class 1) =
        a2Class 0 := by
  have h₀ := reflectWord_of_rootForm (extA 2) mukaiForm_a2Class [0, 1] (stdRoot 0)
  have h₁ := reflectWord_of_rootForm (extA 2) mukaiForm_a2Class [1, 0] (stdRoot 1)
  rw [rootMap_stdRoot, show stdWord (extA 2) [0, 1] (stdRoot 0) = stdRoot 1 by decide,
    rootMap_stdRoot] at h₀
  rw [rootMap_stdRoot, show stdWord (extA 2) [1, 0] (stdRoot 1) = stdRoot 0 by decide,
    rootMap_stdRoot] at h₁
  exact ⟨h₀, h₁⟩

/-- `[0, 1, 0]` and `[1, 0, 1]` have the same image in `Art(A₂)`: the braid relation. -/
theorem ofSignedWord_a2_longest :
    ArtinGroup.ofSignedWord (CoxeterMatrix.A 2) ([0, 1, 0].map fun k => (k, true)) =
      ArtinGroup.ofSignedWord (CoxeterMatrix.A 2) ([1, 0, 1].map fun k => (k, true)) := by
  rw [ArtinGroup.ofSignedWord_map_true, ArtinGroup.ofSignedWord_map_true]
  have h := ArtinGroup.isBraidLiftable_artinGen (M := CoxeterMatrix.A 2) 0 1
  have h₁₀ : CoxeterMatrix.A 2 1 0 = 3 := rfl
  have h₀₁ : CoxeterMatrix.A 2 0 1 = 3 := rfl
  rw [CoxeterSystem.braidWord, CoxeterSystem.braidWord, h₁₀, h₀₁] at h
  first
    | simpa [CoxeterSystem.alternatingWord, mul_assoc] using h
    | simpa [CoxeterSystem.alternatingWord, mul_assoc] using h.symm

/-- The words ending in each letter: `[0, 1] ++ [0]` and `[1, 0] ++ [1]`. -/
def a2Prefix : Fin 2 → List (Fin 2) := ![[0, 1], [1, 0]]

/-- **The class-level inputs of `WeylGalleryHypotheses.longest_obj_iso_shift` hold for
`𝒪_X[1]`, `𝒪_C`**, with `ω₀ = [0, 1, 0]`, the words `a2Prefix i ++ [i]` and the swap
`π = Fin.rev`: each word is root-positive, has the Artin image of `ω₀`, and sends `α_i` to
`-α_{π i}` through `(a2Prefix i)(α_i) = α_{π i}`; and the classes are linearly independent. -/
theorem a2_longest_inputs :
    LinearIndependent ℤ a2Class ∧
      (∀ i, BilinearForm.IsRootPositive (mukaiForm intersection) a2Class (a2Prefix i ++ [i])) ∧
      (∀ i, ArtinGroup.ofSignedWord (CoxeterMatrix.A 2)
          ((a2Prefix i ++ [i]).map fun k => (k, true)) =
        ArtinGroup.ofSignedWord (CoxeterMatrix.A 2) ([0, 1, 0].map fun k => (k, true))) ∧
      ∀ i, BilinearForm.reflectWord (mukaiForm intersection) a2Class (a2Prefix i) (a2Class i) =
        a2Class i.rev := by
  refine ⟨linearIndependent_a2, fun i => ?_, fun i => ?_, fun i => ?_⟩ <;> fin_cases i
  · exact isRootPositive_a2_longest.1
  · exact isRootPositive_a2_longest.2
  · rfl
  · exact ofSignedWord_a2_longest.symm
  · exact reflectWord_a2_prefix.1
  · exact reflectWord_a2_prefix.2

end AlgebraicGeometry.K3.EllipticWithSection
