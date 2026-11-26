/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.RepresentationTheory.Quiver.Preprojective.Kronecker
import K3Twists.RepresentationTheory.Quiver.Preprojective.SingleVertex

/-!
# Models of the general wall model

* The Euler form of the Jordan quiver (one vertex, one loop) vanishes on every dimension vector:
  the vertex of an object with `e = 2` is isotropic. The Euler form of the Kronecker quiver of
  two spheres at pairing `g` is `2x₀y₀ + 2x₁y₁ - g(x₀y₁ + x₁y₀)`.
* The rigid representation of dimension `(g², g)` is rigid for the general complex.
* `FormalWallHypotheses` and `RealizationHypotheses` have the instance of one sphere from real
  objects: the derived category of finite-dimensional vector spaces with the identity as
  realization. Every finite-dimensional space is a wall object, and its subspaces carry the HN
  filtrations of the charges of the two sides.
-/

namespace Quiver.Preprojective

open CategoryTheory

/-- The Jordan quiver: one vertex, one loop. -/
abbrev jordanQuiver : Unit → Unit → Type :=
  fun _ _ ↦ Unit

example (x y : Unit → ℤ) : eulerForm jordanQuiver x y = 0 := by
  simp [eulerForm]
  ring

example (g : ℕ) (x : Bool → ℤ) :
    titsForm (wallArrow (Fin g) PEmpty) x =
      x false ^ 2 + x true ^ 2 - g * (x false * x true) := by
  rw [DoubledRep.titsForm_wallArrow_pEmpty, Fintype.card_fin]

example (g : ℕ) (x : Bool → ℤ) :
    titsForm (wallArrow (Fin g) PUnit) x = x false ^ 2 - g * (x false * x true) := by
  rw [DoubledRep.titsForm_wallArrow_pUnit, Fintype.card_fin]

/-- The rigid representation is rigid for the general complex. -/
example (k : Type) [Field k] :
    DoubledRep.selfExtDim (DoubledRep.ofKronecker (Kronecker.rigidRep k (Fin 3))) = 0 :=
  DoubledRep.selfExtDim_ofKronecker_rigidRep

variable (k : Type) [Field k] [HasDerivedCategory (FGModuleCat.{0} k)]

/-- The realization hypotheses of one sphere. -/
noncomputable example :
    RealizationHypotheses k pointQuiver (𝟭 (DerivedCategory (FGModuleCat.{0} k)))
    (DerivedCategory.singleFunctor (FGModuleCat.{0} k) 0)
    (DerivedCategory.singleFunctor (FGModuleCat.{0} k) 0) :=
  SingleVertex.realizationHypotheses

/-- The formal wall model of one sphere. -/
noncomputable example : FormalWallHypotheses (FGModuleCat.{0} k) k pointQuiver :=
  SingleVertex.formalWallHypotheses

/-- Every finite-dimensional space is a wall object. -/
example (X : FGModuleCat.{0} k) : (SingleVertex.formalWallHypotheses (k := k)).IsWall X :=
  ⟨X, ⟨Iso.refl _⟩⟩

/-- The subspaces of a finite-dimensional space carry an HN filtration on each side. -/
example (X : FGModuleCat.{0} k) (s : Bool) :
    Nonempty ((SingleVertex.formalWallHypotheses (k := k)).chargeFunction s X
      ⟨X, ⟨Iso.refl _⟩⟩).HNFiltration :=
  FormalWallHypotheses.nonempty_hnFiltration _ s X _

end Quiver.Preprojective
