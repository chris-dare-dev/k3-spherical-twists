/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.TStructure
import K3Twists.CategoryTheory.Triangulated.TStructure.HeartAbelian

/-!
# The heart of a slicing as an abelian category

For a slicing `s` of a triangulated category and `a ∈ ℝ`, the half-open interval
`P((a, a+1])` (`Slicing.HeartCat s a`) is the heart of the t-structure `s.toTStructure a`, so it
is an abelian category (Bridgeland, arXiv:math/0212237, §3; Beilinson–Bernstein–Deligne,
*Faisceaux pervers*, Théorème 1.3.6). Its short exact sequences are
the distinguished triangles of the ambient category with vertices in `P((a, a+1])`.

## Main results

* `Slicing.instAbelianHeartCat`: `P((a, a+1])` is abelian.
* `Slicing.HeartCat.shortExact_of_distTriang`, `Slicing.HeartCat.exists_distTriang_of_shortExact`:
  short exact sequences of the heart are the distinguished triangles on heart objects.

## Tags

slicing, heart, abelian category, t-structure
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

/-- **The heart of a slicing is abelian**: `P((a, a+1])` is the heart of `s.toTStructure a`. -/
instance Slicing.instAbelianHeartCat (s : Slicing C) (a : ℝ) : Abelian (s.HeartCat C a) :=
  (s.toTStructure C a).heartAbelian (s.HeartCat C a)

variable {C}

namespace Slicing.HeartCat

variable {s : Slicing C} {a : ℝ}

/-- A distinguished triangle `X₁ → X₂ → X₃ → X₁⟦1⟧` with vertices in `P((a, a+1])` is a short
exact sequence of the heart. -/
theorem shortExact_of_distTriang {X₁ X₂ X₃ : s.HeartCat C a} {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃}
    {δ : X₃.obj ⟶ X₁.obj⟦(1 : ℤ)⟧} (hT : Triangle.mk f.hom g.hom δ ∈ distTriang C) :
    (ShortComplex.mk f g (ObjectProperty.hom_ext _ (by
      simpa using comp_distTriang_mor_zero₁₂ _ hT))).ShortExact :=
  (s.toTStructure C a).shortExact_of_distTriang (H := s.HeartCat C a) hT

/-- A short exact sequence of `P((a, a+1])` extends to a distinguished triangle of the ambient
category. -/
theorem exists_distTriang_of_shortExact {S : ShortComplex (s.HeartCat C a)}
    (hS : S.ShortExact) :
    ∃ δ : S.X₃.obj ⟶ S.X₁.obj⟦(1 : ℤ)⟧, Triangle.mk S.f.hom S.g.hom δ ∈ distTriang C :=
  (s.toTStructure C a).exists_distTriang_of_shortExact (H := s.HeartCat C a) hS

end Slicing.HeartCat

end CategoryTheory.Triangulated
