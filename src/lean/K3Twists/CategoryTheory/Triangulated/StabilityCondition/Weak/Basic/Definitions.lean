/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.GrothendieckGroup.Basic
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Weak stability: the weak prestability condition

Definition 14.1 of arXiv:1902.08184v4 for a pretriangulated category: a slicing and a central charge
whose nonzero semistable objects have charge on the closed ray `ℝ_{≥0}·e^{iπφ}` at integer phases
`φ` and on the open ray elsewhere. Ordinary prestability (`Foundation/PreStabilityCondition.lean`)
extends this structure.

## Main definitions

* `CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition`: a slicing and a
  central charge on a class lattice `Λ`, compatible in the weak sense above.

## Implementation notes

Only Definition 14.1 is formalized. Definitions 14.2 and 14.3 (weak stability functions on the
heart of a t-structure and the zero-charge subcategory) would need stability functions on an
abelian category; the prestability and stability conditions of `Foundation/` need only this
structure.

## References

* arXiv:1902.08184v4, §14, Definition 14.1.

## Tags

weak stability condition, prestability condition, central charge, slicing
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition

open CategoryTheory.Triangulated
open CategoryTheory Limits Pretriangulated CategoryTheory.Triangulated Complex

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

variable {Λ : Type*} [AddCommGroup Λ]

/-- A weak prestability condition with respect to a class map `v : K₀ C →+ Λ`
(Definition 14.1): a slicing and a central charge on `Λ` such that a nonzero
semistable object of phase `φ` has charge on the ray `ℝ_{>0}·e^{iπφ}` when
`φ ∉ ℤ`, and on the closed ray `ℝ_{≥0}·e^{iπφ}` — so possibly zero — when
`φ ∈ ℤ`. -/
structure WeakPreStabilityCondition (v : K₀ C →+ Λ) where
  /-- The underlying slicing. -/
  slicing : Slicing C
  /-- The central charge on the class lattice `Λ`. -/
  Z : Λ →+ ℂ
  /-- Compatibility: nonnegative radius always, positive off the integers. -/
  compat' : ∀ (φ : ℝ) (E : C), slicing.P φ E → ¬IsZero E →
    ∃ m : ℝ, 0 ≤ m ∧ ((∀ n : ℤ, φ ≠ (n : ℝ)) → 0 < m) ∧
      Z (v (K₀.of C E)) = ↑m * Complex.exp (↑(Real.pi * φ) * Complex.I)

end CategoryTheory.Triangulated.WeakStabilityCondition
