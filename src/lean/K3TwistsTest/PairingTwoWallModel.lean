/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.PairingTwoWall
import Mathlib.Algebra.Category.ModuleCat.Simple
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Data.ZMod.Basic

/-!
# The inputs at a wall of pairing two are consistent

A theorem proved from hypotheses that cannot hold together says nothing. This file builds a model
of `PairingTwoWallHypotheses` in abelian groups: `A = B = ℤ/2`, `P = U = ℤ/4` and `M = ℤ/8`, where
`ℤ/2 → ℤ/4 → ℤ/8` are multiplication by `2` and the maps onto `ℤ/2` and `ℤ/4` reduce. The
extension `ℤ/4` of `ℤ/2` by `ℤ/2` does not split, and the chain of subobjects of `ℤ/8` is
`0 ⊂ 4ℤ/8ℤ ⊂ 2ℤ/8ℤ ⊂ ℤ/8`.

The model says nothing about K3 surfaces (in it `A = B`); it shows that the fields can hold
together.

Built by `lake test`.
-/

namespace AlgebraicGeometry.K3.PairingTwoWallModel

open CategoryTheory

lemma zmod_two_cases (y : ZMod 2) : y = 0 ∨ y = 1 := by
  revert y; decide

/-- `ℤ/2` is a simple abelian group. -/
instance : IsSimpleModule ℤ (ZMod 2) where
  eq_bot_or_eq_top N := by
    by_cases h : (1 : ZMod 2) ∈ N
    · right
      rw [eq_top_iff]
      intro y _
      rcases zmod_two_cases y with rfl | rfl
      · exact N.zero_mem
      · exact h
    · left
      rw [eq_bot_iff]
      intro y hy
      rcases zmod_two_cases y with rfl | rfl
      · exact Submodule.zero_mem _
      · exact absurd hy h

instance : Simple (ModuleCat.of ℤ (ZMod 2)) :=
  simple_iff_isSimpleModule.mpr inferInstance

/-- Multiplication by `2`, `ℤ/2 → ℤ/4`. -/
def twoMul24 : ZMod 2 →+ ZMod 4 :=
  AddMonoidHom.mk' (fun x => 2 * (x.val : ZMod 4)) (by decide)

/-- Multiplication by `2`, `ℤ/4 → ℤ/8`. -/
def twoMul48 : ZMod 4 →+ ZMod 8 :=
  AddMonoidHom.mk' (fun x => 2 * (x.val : ZMod 8)) (by decide)

/-- Reduction `ℤ/4 → ℤ/2`. -/
def red42 : ZMod 4 →+ ZMod 2 :=
  AddMonoidHom.mk' (fun x => (x.val : ZMod 2)) (by decide)

/-- Reduction `ℤ/8 → ℤ/2`. -/
def red82 : ZMod 8 →+ ZMod 2 :=
  AddMonoidHom.mk' (fun x => (x.val : ZMod 2)) (by decide)

/-- Reduction `ℤ/8 → ℤ/4`. -/
def red84 : ZMod 8 →+ ZMod 4 :=
  AddMonoidHom.mk' (fun x => (x.val : ZMod 4)) (by decide)

/-- An additive map of cyclic groups as a morphism of `ℤ`-modules. -/
abbrev hom {m n : ℕ} (f : ZMod m →+ ZMod n) :
    ModuleCat.of ℤ (ZMod m) ⟶ ModuleCat.of ℤ (ZMod n) :=
  ModuleCat.ofHom f.toIntLinearMap

/-- An additive map `ℤ/2 → ℤ/4` has image in `2ℤ/4ℤ`, so `ℤ/4 → ℤ/2` has no section. -/
lemma red42_ne_one {σ : ZMod 2 →ₗ[ℤ] ZMod 4} : red42 (σ 1) ≠ 1 := by
  have h2 : σ 1 + σ 1 = 0 := by
    rw [← map_add, show (1 : ZMod 2) + 1 = 0 by decide, map_zero]
  have key : ∀ y : ZMod 4, y + y = 0 → red42 y ≠ 1 := by decide
  exact key _ h2

/-- **The model.** -/
def model : PairingTwoWallHypotheses (ModuleCat.{0} ℤ) where
  A := ModuleCat.of ℤ (ZMod 2)
  B := ModuleCat.of ℤ (ZMod 2)
  P := ModuleCat.of ℤ (ZMod 4)
  M := ModuleCat.of ℤ (ZMod 8)
  U := ModuleCat.of ℤ (ZMod 4)
  simple_A := inferInstance
  simple_B := inferInstance
  j := hom twoMul24
  q := hom red42
  i := hom twoMul48
  p := hom red82
  k := hom twoMul24
  l := hom red42
  π := hom red84
  zero_jq := by ext x; revert x; decide
  zero_ip := by ext x; revert x; decide
  zero_kl := by ext x; revert x; decide
  zero_π := by ext x; revert x; decide
  shortExact_P := ModuleCat.shortComplex_shortExact _ (by
    intro y; simp only [Set.mem_range]; revert y; decide) (by decide) (by decide)
  shortExact_M := ModuleCat.shortComplex_shortExact _ (by
    intro y; simp only [Set.mem_range]; revert y; decide) (by decide) (by decide)
  shortExact_U := ModuleCat.shortComplex_shortExact _ (by
    intro y; simp only [Set.mem_range]; revert y; decide) (by decide) (by decide)
  shortExact_π := ModuleCat.shortComplex_shortExact _ (by
    intro y; simp only [Set.mem_range]; revert y; decide) (by decide) (by decide)
  π_l := by ext x; revert x; decide
  nonsplit_P σ hσ := red42_ne_one (σ := σ.hom) (by
    simpa using congrArg (fun f => f.hom (1 : ZMod 2)) hσ)
  nonsplit_U σ hσ := red42_ne_one (σ := σ.hom) (by
    simpa using congrArg (fun f => f.hom (1 : ZMod 2)) hσ)

/-- In the model, the subobjects of `ℤ/8` form the chain `0 ⊂ 4ℤ/8ℤ ⊂ 2ℤ/8ℤ ⊂ ℤ/8`. -/
example (T : Subobject model.M) :
    T = ⊥ ∨ T = Subobject.mk (model.j ≫ model.i) ∨ T = Subobject.mk model.i ∨ T = ⊤ :=
  model.subobject_M T

end AlgebraicGeometry.K3.PairingTwoWallModel
