/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.EllipticWithSection.KernelRootSystem
import K3Twists.LinearAlgebra.RootSystem.Stratum

/-!
# The root systems of the `A₁` stratum of the elliptic K3 surface

At the stratum charge of `EllipticWithSection/KernelRootSystem.lean` (`x = 3`, `β = -C/2`,
`H = C + 2F`, `a = 1`) the kernel roots are `±v(𝒪_C)` (`kernelRoots_stratumCharge`). Here are the
two root systems of the stratum and their bases:

* `stratumRootPairingBase`: `{v(𝒪_C)}` is a base of the kernel root pairing over `ℤ`, with Cartan
  matrix `(2)` (`cartanMatrix_stratumRootPairingBase`): type `A₁`.
* `stratumRootSystem`: the root system of the stratum over `ℚ`, on the span of its roots in
  `ℚ ⊗ (ker Z ∩ N)`, a Mathlib `IsRootSystem` with finitely many roots; `stratumRootSystemBase`:
  `{1 ⊗ v(𝒪_C)}` is a base of it.

These are lattice statements: that the charge is the central charge of a stability condition is
not formalized.
-/

namespace AlgebraicGeometry.K3.EllipticWithSection

open RootPairing Mukai

/-- **The base of the stratum over `ℤ`**: `{v(𝒪_C)}`. -/
noncomputable def stratumRootPairingBase :
    (kernelRootPairing mukaiForm_intersection_comm negDef_ker_stratumChargeInt).Base :=
  kernelRootPairingBaseOfEq _ _ kernelRoots_stratumCharge

/-- The base of the stratum has the single root `v(𝒪_C)`. -/
theorem coe_root_stratumRootPairingBase
    (i : (stratumRootPairingBase).support) :
    (((kernelRootPairing mukaiForm_intersection_comm negDef_ker_stratumChargeInt).root i :
      kernelLattice stratumChargeInt) : MukaiLattice ℤ NS) = wallA := by
  have := Finset.mem_singleton.mp i.2
  rw [this]
  rfl

/-- **The Cartan matrix of the stratum is `(2)`**: type `A₁`. -/
theorem cartanMatrix_stratumRootPairingBase (i j : (stratumRootPairingBase).support) :
    stratumRootPairingBase.cartanMatrix i j = 2 :=
  cartanMatrix_kernelRootPairingBaseOfEq _ _ _ i j

/-- **The root system of the stratum over `ℚ`.** -/
noncomputable abbrev stratumRootSystem :=
  kernelRootSystem mukaiForm_intersection_comm negDef_ker_stratumChargeInt

/-- It is a Mathlib root system. -/
example : stratumRootSystem.IsRootSystem :=
  inferInstance

/-- It has finitely many roots. -/
theorem finite_stratumRootSystem_roots :
    Finite (latticeRoots (kernelFormRat (mukaiForm intersection) stratumChargeInt)
      (kernelLatticeRat stratumChargeInt)) :=
  finite_kernelRootSystem_roots mukaiForm_intersection_comm negDef_ker_stratumChargeInt

/-- **The base of the stratum over `ℚ`**: `{1 ⊗ v(𝒪_C)}`. -/
noncomputable def stratumRootSystemBase : stratumRootSystem.Base :=
  kernelRootSystemBaseOfEq _ _ kernelRoots_stratumCharge

end AlgebraicGeometry.K3.EllipticWithSection
