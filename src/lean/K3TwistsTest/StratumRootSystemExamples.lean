/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.EllipticWithSection.StratumRootSystem
import K3Twists.AlgebraicGeometry.Surface.K3.PicardRankOne.StratumRootSystem
import K3Twists.AlgebraicGeometry.Surface.K3.EllipticWithSection.PhaseGap

/-!
# Strata of type `A₁`

* The `A₁` stratum of the elliptic K3 surface: its root system over `ℚ` is a Mathlib root system
  with a base, and its Cartan matrix over `ℤ` is `(2)`.
* In Picard rank one with `H² = 2`, the structure sheaf `v(𝒪_X) = (1, 0, 1)` is a root whose
  charge vanishes at `p = (0, 1)`: that stratum has a base `{v(𝒪_X)}` over `ℤ` and over `ℚ`.
* The lattice gap at the curve wall exists for every bound and phase set.
-/

open RootPairing

namespace K3TwistsTest.StratumRootSystemExamples

open AlgebraicGeometry.K3

example : EllipticWithSection.stratumRootSystem.IsRootSystem :=
  inferInstance

example (i j : EllipticWithSection.stratumRootPairingBase.support) :
    EllipticWithSection.stratumRootPairingBase.cartanMatrix i j = 2 :=
  EllipticWithSection.cartanMatrix_stratumRootPairingBase i j

/-- The stratum of `𝒪_X` in Picard rank one, `H² = 2`. -/
noncomputable example :=
  PicardRankOne.stratumRootSystemBase (d := 1) one_pos (p := (0, 1 / (1 : ℤ)))
    (by norm_num) (MukaiVector.isRoot_lineBundle 1 0)
    (PicardRankOne.modelCharge_lineBundle_zero one_pos)

example (R : ℝ) : ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 8 := by
  obtain ⟨ε, h₁, h₂, -⟩ := EllipticWithSection.exists_latticeGap_charge R {0, 1 / 2}
  exact ⟨ε, h₁, h₂⟩

end K3TwistsTest.StratumRootSystemExamples
