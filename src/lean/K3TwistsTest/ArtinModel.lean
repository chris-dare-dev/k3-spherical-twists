/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Autoequivalence.Slicing.Artin
import K3Twists.AlgebraicGeometry.Surface.K3.EllipticWithSection.Braid

/-!
# Models of the braid layer

A theorem proved from hypotheses that cannot hold together says nothing, and one proved from
hypotheses that trivial data satisfy says little. This file records both facts for
`TwistConjugation`.

* `TwistConjugation.trivial`: the four fields of `TwistConjugation` hold for `twist ≡ 1`, with
  every object spherical. The structure alone constrains nothing.
* `TwistConjugation.trivialConfiguration`: over it, the identity autoequivalences at a single
  object form a configuration for every Coxeter matrix. So the fields of `Configuration` are
  consistent; in this model the whole Artin group acts trivially (`toAutQuot_trivial`).

The content of the braid layer is in the link `[T_i] = τ(x_i)` and the edge identities, which
need twist functors of real spherical objects; Mathlib has none. The library's instance from real
data is on classes: `AlgebraicGeometry.K3.EllipticWithSection.a2Hom`, the `A₂` configuration
`𝒪_X[1]`, `𝒪_C` on the Mukai lattice of an elliptic K3 surface with a section, checked below.

The file also checks the conventions the braid layer relies on: `AutQuot` multiplies in the
usual composition order, and `CoxeterMatrix.ofExt` reads no diagonal entry.
-/

open CoxeterSystem CoxeterMatrix
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {B : Type*}

/-- `AutQuot` multiplies in composition order: `[A] [B]` is the class of `A ∘ B`. -/
example (A B : TriEquiv C) : AutQuot.mk A * AutQuot.mk B = AutQuot.mk (B.comp A) := rfl

example (A B : TriEquiv C) (X : C) :
    (B.comp A).e.functor.obj X = A.e.functor.obj (B.e.functor.obj X) := rfl

/-- **The trivial model**: `twist ≡ 1` satisfies every field of `TwistConjugation`. -/
def TwistConjugation.trivial (C : Type*) [Category C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] :
    TwistConjugation C where
  IsSpherical _ := True
  twist _ := 1
  twist_eq _ _ _ _ := rfl
  twist_conj Φ _ _ := by simp

/-- A word in the identity autoequivalences fixes every object. -/
theorem TriEquiv.ofWord_id_obj (ω : List B) (X : C) :
    (TriEquiv.ofWord (fun _ : B => TriEquiv.id) ω).e.functor.obj X = X := by
  induction ω with
  | nil => rfl
  | cons i ω ih => exact ih

/-- **A configuration over the trivial model**, for every Coxeter matrix: one object `X`, the
identity autoequivalences, and the edge identities `X ≅ X[0]`. -/
def TwistConjugation.trivialConfiguration (M : CoxeterMatrix B) (X : C) :
    (TwistConjugation.trivial C).Configuration M where
  obj _ := X
  isSpherical_obj _ := True.intro
  T _ := TriEquiv.id
  mk_T _ := rfl
  edge _ _ _ _ := Or.inl
    ⟨0, ⟨eqToIso (TriEquiv.ofWord_id_obj _ X) ≪≫ ((shiftFunctorZero C ℤ).app X).symm⟩⟩

/-- In the trivial model the whole Artin group acts trivially. -/
theorem TwistConjugation.toAutQuot_trivial (M : CoxeterMatrix B) (X : C) :
    (TwistConjugation.trivial C).toAutQuot (TwistConjugation.trivialConfiguration M X) = 1 :=
  ArtinGroup.hom_ext fun i => by
    rw [TwistConjugation.toAutQuot_of_eq_twist]
    rfl

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

namespace CoxeterMatrix

variable {B : Type*}

/-- `ofExt` reads only the off-diagonal Ext numbers. -/
example [DecidableEq B] (e e' : B → B → ℕ) (he : ∀ i j, e i j = e j i)
    (he' : ∀ i j, e' i j = e' j i) (hoff : ∀ i j, i ≠ j → e i j = e' i j) (i j : B) :
    ofExt e he i j = ofExt e' he' i j := by
  by_cases h : i = j
  · subst h; simp [ofExt]
  · rw [ofExt_apply_of_ne e he h, ofExt_apply_of_ne e' he' h, hoff i j h]

/-- The anti-automorphism reads words backwards. -/
example (M : CoxeterMatrix B) (i j : B) :
    ArtinGroup.reverse M (M.artinGen i * M.artinGen j) =
      MulOpposite.op (M.artinGen j * M.artinGen i) := by
  simp

/-- The squares of the generators are pure braids. -/
example (M : CoxeterMatrix B) (i : B) : M.artinGen i ^ 2 ∈ M.pureArtinGroup := by
  rw [pureArtinGroup_eq_normalClosure]
  exact Subgroup.subset_normalClosure ⟨i, rfl⟩

end CoxeterMatrix

namespace AlgebraicGeometry.K3.EllipticWithSection

/-- On the Mukai lattice the pure braid `σ₀²` acts trivially. -/
example : a2Hom ((CoxeterMatrix.A 2).artinGen 0 ^ 2) = 1 := by
  rw [map_pow, a2Hom_of]
  exact reflection_sq _

/-- The braid relation `ρ₀ ρ₁ ρ₀ = ρ₁ ρ₀ ρ₁` of the reflections in `v(𝒪_X[1])` and `v(𝒪_C)`. -/
example : reflection (a2 0) * reflection (a2 1) * reflection (a2 0) =
    reflection (a2 1) * reflection (a2 0) * reflection (a2 1) := by
  have h := isBraidLiftable_a2 1 0
  have h₁₀ : CoxeterMatrix.A 2 1 0 = 3 := rfl
  have h₀₁ : CoxeterMatrix.A 2 0 1 = 3 := rfl
  rw [braidWord, braidWord, h₁₀, h₀₁] at h
  simpa [alternatingWord, mul_assoc] using h

end AlgebraicGeometry.K3.EllipticWithSection
