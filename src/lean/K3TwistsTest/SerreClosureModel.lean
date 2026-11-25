/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.SerreClosure

/-!
# The Serre preimage in the derived category

The Serre-preimage theorem takes any homological functor. Its instance from objects Mathlib has
is `H⁰ : D(A) ⥤ A` on the derived category of an abelian category `A`, with any Serre class `P`
of `A`: the complexes whose cohomology lies in `P` form a thick subcategory, words in letters
with cones there preserve it, and the theorem applies to chains of letter steps.

The checks below also pin the two extreme Serre classes: `P = ⊤` gives every object, and
`P = IsZero` gives the homological kernel.
-/

open CategoryTheory Limits Pretriangulated DerivedCategory

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A] (P : ObjectProperty A)
  [P.IsSerreClass]

/-- In `D(A)`, the complexes with cohomology in a Serre class form a thick subcategory. -/
example : ((homologyFunctor A 0).serrePreimage P).IsTriangulated := inferInstance

example : ((homologyFunctor A 0).serrePreimage P).IsStableUnderRetracts := inferInstance

example : ((homologyFunctor A 0).serrePreimage P).IsClosedUnderIsomorphisms := inferInstance

/-- The top Serre class gives every object. -/
example (X : DerivedCategory A) : (homologyFunctor A 0).serrePreimage ⊤ X := fun _ ↦ trivial

/-- The zero Serre class gives the homological kernel. -/
example : (homologyFunctor A 0).serrePreimage (IsZero (C := A)) =
    (homologyFunctor A 0).homologicalKernel := rfl

/-- An object in degree zero lies in the Serre preimage iff it lies in `P`. -/
example (X : A) (hX : P X) : (homologyFunctor A 0).serrePreimage P ((singleFunctor A 0).obj X) :=
  (singleFunctor_mem_serrePreimage_iff P X).2 hX

/-- The Serre-preimage theorem in `D(A)`: if the seed `E` and the centres have cohomology in `P`,
so does every object reached from `E` by letter steps at the centres. -/
example {𝒮 : ObjectProperty (DerivedCategory A)}
    (h𝒮 : ∀ S, 𝒮 S → ∀ n : ℤ, P ((homologyFunctor A n).obj S)) {E Y : DerivedCategory A}
    (hE : ∀ n : ℤ, P ((homologyFunctor A n).obj E))
    (h : Relation.ReflTransGen (ObjectProperty.LetterStep (ObjectProperty.shiftSums 𝒮)) E Y)
    (n : ℤ) : P ((homologyFunctor A n).obj Y) :=
  (mem_serrePreimage_homologyFunctor_iff P Y).1
    ((homologyFunctor A 0).prop_obj_shift_of_reflTransGen P
      (fun S hS ↦ (mem_serrePreimage_homologyFunctor_iff P S).2 (h𝒮 S hS))
      ((mem_serrePreimage_homologyFunctor_iff P E).2 hE) h) n

/-- A single letter step: the third vertex of a distinguished triangle on `X ⟶ Y` lying in the
Serre preimage makes `X` and `Y` lie in it together. -/
example {X Y Z : DerivedCategory A} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g h ∈ distTriang _) (hZ : (homologyFunctor A 0).serrePreimage P Z) :
    (homologyFunctor A 0).serrePreimage P X ↔ (homologyFunctor A 0).serrePreimage P Y :=
  ObjectProperty.prop_iff_of_trW _ ⟨Z, g, h, hT, hZ⟩

/-- The identity word acts as the identity modulo any `K`. -/
example (K : ObjectProperty (DerivedCategory A)) : K.IsWordModulo (𝟭 _) := .id
