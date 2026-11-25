/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.WeylTilt
import K3Twists.AlgebraicGeometry.Surface.K3.EllipticWithSection.WeylGallery
import K3TwistsTest.ArtinModel

/-!
# Models of the Weyl-gallery layer

* `zeroHeartTStructure C`: in any pretriangulated category, `≤ n` is everything and `≥ n` is the
  zero objects. This is a t-structure, with zero heart.
* `WeylGalleryHypotheses.emptyModel`: over it, with no simple objects (the Coxeter matrix on
  `Fin 0`) and the trivial twists `τ ≡ 1`, every field of `WeylGalleryHypotheses` holds. So the
  fields are consistent. The model has no simple object and no gallery: a model with simple
  objects needs a heart with spherical simple objects and their twist functors, which Mathlib
  does not provide. The class-level inputs of the gallery theorems are instantiated from real
  classes instead, the `A₂` configuration `𝒪_X[1]`, `𝒪_C` of an elliptic K3 surface
  (`AlgebraicGeometry.K3.EllipticWithSection.a2_longest_inputs`), checked below.
* Root-positivity is not vacuous: `[0, 0]` is not root-positive, and neither is `[0, 1, 0, 1]`.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated CategoryTheory.Triangulated.WeylGallery
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction
open ZeroObject

namespace CategoryTheory.Triangulated

variable (C : Type*) [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The t-structure whose `≤ n` part is everything and whose `≥ n` part is the zero objects. -/
def zeroHeartTStructure : TStructure C where
  le _ := ⊤
  ge _ := IsZero
  le_shift _ _ _ _ _ _ := trivial
  ge_shift _ a _ _ _ hX := (shiftFunctor C a).map_isZero hX
  zero' _ _ _ _ hY := hY.eq_of_tgt _ _
  le_zero_le := le_rfl
  ge_one_le := le_rfl
  exists_triangle_zero_one A :=
    ⟨A, 0, trivial, isZero_zero C, 𝟙 A, 0, 0, contractible_distinguished A⟩

/-- Its heart is the zero objects. -/
example (X : C) : (zeroHeartTStructure C).heart X ↔ IsZero X :=
  ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩

/-- **The empty model**: no simple objects, trivial twists, zero heart. Every field holds, so the
fields are consistent; the model has no gallery. -/
def WeylGalleryHypotheses.emptyModel : WeylGalleryHypotheses C (CoxeterMatrix.A 0) ℤ where
  t := zeroHeartTStructure C
  twists := TwistConjugation.trivial C
  conf :=
    { obj := Fin.elim0
      isSpherical_obj := fun i => i.elim0
      T := Fin.elim0
      mk_T := fun i => i.elim0
      edge := fun i => i.elim0 }
  cl _ := 0
  cl_iso _ := rfl
  cl_triangle _ _ _ _ := (add_zero 0).symm
  form := 0
  form_symm _ _ := rfl
  form_self i := i.elim0
  cl_twist i := i.elim0
  cone := ⊥
  cl_mem_cone _ hX h0 := absurd hX.2 h0
  neg_not_mem_cone _ hv := absurd hv AddSubsemigroup.notMem_bot
  isSimpleIn_obj i := i.elim0
  image_heart_eq_lowerTilt i := i.elim0
  lowerTilt_lowerTilt_eq _ _ _ hX hX' := absurd hX'.1.2 hX.2.1
  hull := ⊤
  hull_obj i := i.elim0
  hull_twist _ _ _ := trivial
  heart_inf_hull_le _ hX := filtration_of_isZero _ hX.1.2

/-- In the empty model the gallery is the starting heart. -/
example : (WeylGalleryHypotheses.emptyModel C).heartOf [] = (zeroHeartTStructure C).heart := rfl

variable {C}

/-- The image of a property under the identity is the property itself. -/
example (P : ObjectProperty C) : image TriEquiv.id P = P := rfl

/-- The lower tilt at the zero class is the heart. -/
example (t : TStructure C) : lowerTilt t.heart IsZero = t.heart := lowerTilt_isZero t

end CategoryTheory.Triangulated

namespace CoxeterMatrix

open BilinearForm

/-- `longestWordA 3 = [0, 1, 0, 2, 1, 0]`. -/
example : longestWordA 3 = [0, 1, 0, 2, 1, 0] := rfl

/-- Non-reduced words are not root-positive: `ρ₀ α₀ = -α₀`. -/
example : ¬IsRootPositive (rootForm (extA 2)) stdRoot [0, 0] := by
  rw [isRootPositive_rootForm_iff]; decide

/-- `[0, 1, 0, 1]` is not reduced in `W(A₂)` and not root-positive. -/
example : ¬IsRootPositive (rootForm (extA 2)) stdRoot [0, 1, 0, 1] := by
  rw [isRootPositive_rootForm_iff]; decide

/-- The affine `Ã₁` matrix (`e = 2`): the alternating words are root-positive at every length;
here length six. -/
example : IsRootPositive (rootForm fun i j : Fin 2 => if i = j then 0 else 2) stdRoot
    [0, 1, 0, 1, 0, 1] := by
  rw [isRootPositive_rootForm_iff]; decide

/-- `w₀` of `A₄` sends `α₀` to `-α₃`. -/
example : stdWord (extA 4) (longestWordA 4) (stdRoot 0) = -stdRoot 3 :=
  stdWord_longestWordA (by norm_num) 0

/-- The longest word of `A₆` is reduced. -/
example : (CoxeterMatrix.A 6).toCoxeterSystem.IsReduced (longestWordA 6) :=
  isReduced_longestWordA le_rfl

end CoxeterMatrix

namespace AlgebraicGeometry.K3.EllipticWithSection

/-- The prefix roots of `[0, 1, 0]` on the classes of `𝒪_X[1]`, `𝒪_C`: `α₀, α₀ + α₁, α₁`. -/
example : BilinearForm.prefixRoots (Mukai.mukaiForm intersection) a2Class [0, 1, 0] =
    [a2Class 0, a2Class 0 + a2Class 1, a2Class 1] :=
  prefixRoots_a2_longest.1

/-- `w₀ v(𝒪_X[1]) = -v(𝒪_C)`: the class of `F_{w₀} 𝒪_X[1] ≅ 𝒪_C[-1]`. -/
example : BilinearForm.reflectWord (Mukai.mukaiForm intersection) a2Class [0, 1, 0] (a2Class 0) =
    -a2Class 1 :=
  reflectWord_a2_longest 0

/-- The class-level inputs of `WeylGalleryHypotheses.longest_obj_iso_shift` for the `A₂`
configuration. -/
example : LinearIndependent ℤ a2Class := a2_longest_inputs.1

end AlgebraicGeometry.K3.EllipticWithSection
