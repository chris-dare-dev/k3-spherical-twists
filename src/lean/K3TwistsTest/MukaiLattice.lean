/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.Lattice.Mukai.CentralCharge
import K3Twists.LinearAlgebra.Lattice.Mukai.Slice
import Mathlib.Data.ZMod.Basic

/-!
# Tests for the Mukai lattice

* The slice lemma `Mukai.reflect_expSlice` needs the halved root condition `rs = dμ² + 1`: over
  `ZMod 2`, with `b = 0`, `ℓ = 1`, `d = 1`, the class `δ = (1, 0, 0)` has `⟪δ, δ⟫ = 0 = -2`, the
  halved condition fails, and so does the formula at `z = 1`.
* The scalar actions on `MukaiVector ℤ` agree definitionally: `ℤ` acts through the module
  structure exactly as through the coordinatewise action.
* The reflection of the Mukai lattice is Mathlib's `Module.preReflection` and, at a spherical
  class, `Module.reflection`.
* The Picard-rank-one lattice is the Mukai lattice of `(R, 2dxy)`.

Built by `lake test`.
-/

namespace K3TwistsTest.MukaiLattice

open Mukai

/-- The zero form on `ZMod 2`, for which `b 1 1 = 0 = 2 · 1`. -/
def zeroForm : ZMod 2 →ₗ[ZMod 2] ZMod 2 →ₗ[ZMod 2] ZMod 2 := 0

/-- **`⟪δ, δ⟫ = -2` does not give the slice formula in characteristic two.** -/
example :
    zeroForm 1 1 = 2 * (1 : ZMod 2) ∧
      IsSpherical zeroForm ((1 : ZMod 2), (0 : ZMod 2) • (1 : ZMod 2), (0 : ZMod 2)) ∧
      ¬((1 : ZMod 2) * 0 = 1 * 0 ^ 2 + 1) ∧
      reflect zeroForm ((1 : ZMod 2), (0 : ZMod 2) • (1 : ZMod 2), (0 : ZMod 2))
          (expSlice 1 1 1) ≠
        (-(1 * 1 ^ 2 * (1 - 0 / 1) ^ 2 : ZMod 2)) •
          expSlice (1 : ZMod 2) 1 (0 / 1 - 1 / (1 * 1 ^ 2) / (1 - 0 / 1)) := by
  refine ⟨by simp [zeroForm]; decide, by simp [IsSpherical, zeroForm]; decide, by decide, ?_⟩
  intro h
  have h1 := congrArg (fun v => v.1) h
  simp [reflect_apply, expSlice, zeroForm, pairing] at h1

/-- The `ℤ`-action is coordinatewise, by `rfl`, and it is the `ℤ`-module structure of the
additive group: no diamond. -/
example (n : ℤ) (v : MukaiVector ℤ) : n • v = ⟨n * v.r, n * v.c, n * v.s⟩ :=
  rfl

example : AddCommGroup.toIntModule (MukaiVector ℤ) = MukaiVector.instModule :=
  rfl

example (a : ℚ) (v : MukaiVector ℚ) : a • v = ⟨a * v.r, a * v.c, a * v.s⟩ :=
  rfl

/-- The Mukai reflection is Mathlib's `preReflection` for the functional `-⟪·, s⟫`. -/
example {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N] (b : N →ₗ[R] N →ₗ[R] R)
    (s : MukaiLattice R N) :
    reflectHom b s = Module.preReflection s (-(mukaiForm b).flip s) :=
  rfl

/-- At a spherical class it is Mathlib's `Module.reflection`, so Mathlib's reflection API (the
Chebyshev formula for products of two reflections among it) applies to it as stated. -/
example {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N] (b : N →ₗ[R] N →ₗ[R] R)
    (s : MukaiLattice R N) (hs : IsSpherical b s) :
    reflectEquiv b s hs =
      Module.reflection (BilinearForm.neg_flip_apply_self (mukaiForm b) s hs) :=
  rfl

/-- `v(𝒪_X) = (1, 0, 1)` is a root of the rank-one lattice, and it is the same root of the Mukai
lattice of `(ℤ, 2dxy)`. -/
example (d : ℤ) :
    mukaiForm (rankOneForm d) (MukaiVector.isometryEquivMukaiLattice d ⟨1, 0, 1⟩)
      (MukaiVector.isometryEquivMukaiLattice d ⟨1, 0, 1⟩) = -2 := by
  rw [LinearMap.BilinForm.IsometryEquiv.map_app, MukaiVector.mukaiForm_apply,
    ← MukaiVector.lineBundle_zero d]
  exact MukaiVector.isRoot_lineBundle d 0

end K3TwistsTest.MukaiLattice
