/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.PicardRankOne.HNTower

/-!
# The tower hypotheses can hold together

A theorem proved from hypotheses that cannot hold together says nothing. This file shows that the
fields of `TowerHypotheses` are consistent relative to the existence of one slicing with a nonzero
semistable object: from such a slicing it builds an instance (the identity word, no walls, the
point as the only carrier), and the tower theorem applies to it.

This is a relative check. It does not exercise the wall inputs, and it does not construct a
slicing: Mathlib has no triangulated category with a slicing yet (for instance the bounded derived
category of vector spaces with its standard slicing), so the slicing is a variable here.

`TowerHypotheses` moved from `AlgebraicGeometry.K3.PicardRankOne` to
`CategoryTheory.Triangulated`; the last example checks that the old names still elaborate.
-/

namespace CategoryTheory.Triangulated.TowerModel

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The objects isomorphic to `P`. -/
def isoClass (P : C) : ObjectProperty C := fun X => Nonempty (X ≅ P)

instance (P : C) : (isoClass P).IsClosedUnderIsomorphisms :=
  ⟨fun e ⟨f⟩ => ⟨e.symm.trans f⟩⟩

instance : (⊥ : ObjectProperty C).IsClosedUnderIsomorphisms :=
  ⟨fun _ h => h⟩

/-- The leg with no walls, staying at `s`. -/
def stayLeg (s : Slicing C) (Pt Rg : Slicing C → ObjectProperty C) (𝒪 : ObjectProperty C) :
    Leg Pt Rg 𝒪 where
  n := 0
  chamber := fun _ => s
  wall := fun _ => s
  crossing := fun _ hk => absurd hk (Nat.not_lt_zero _)

/-- `Φ⁻¹ s = s` for the identity autoequivalence. -/
theorem TriEquiv.id_symm_act (s : Slicing C) : (TriEquiv.id (C := C)).symm.act s = s :=
  Slicing.ext C (by funext φ X; rfl)

/-- **A model of the tower hypotheses.** From one slicing `s` and a nonzero `s`-semistable `P`:
the identity word, no walls, `P` as the only carrier and no spherical factors. -/
noncomputable def TowerHypotheses.ofSemistable (s : Slicing C) (P : C) (φ : ℝ) (hP : s.P φ P)
    (hP0 : ¬IsZero P) : TowerHypotheses C where
  point := P
  letter := fun _ => TriEquiv.id
  length := 0
  anchor := s
  target := s
  carrier := fun _ => isoClass P
  spherical := fun _ => ⊥
  carrier_iso := fun _ => inferInstance
  spherical_iso := fun _ => inferInstance
  pointLike := ⊤
  pointLike_point := trivial
  pointLike_letter := fun _ _ _ => trivial
  point_nonzero := hP0
  point_semistable := ⟨φ, hP⟩
  carrier_point := ⟨Iso.refl P⟩
  carrier_letter := fun _ _ _ => Iff.rfl
  spherical_letter := fun _ _ _ h => h
  leg := fun _ => stayLeg s _ _ _
  leg_start := fun _ => rfl
  leg_end := fun _ => (TriEquiv.id_symm_act s).symm
  final := stayLeg s _ _ _
  final_start := rfl
  final_target := fun _ _ h => h

/-- The tower theorem holds in the model: the point is its own tower. -/
example [IsTriangulated C] (s : Slicing C) (P : C) (φ : ℝ) (hP : s.P φ P) (hP0 : ¬IsZero P) :
    s.CarriesOnce (isoClass P) ⊥ P :=
  (TowerHypotheses.ofSemistable s P φ hP hP0).tower

set_option linter.deprecated false in
/-- The deprecated names of the Picard-rank-one directory still elaborate. -/
example [IsTriangulated C] (s : Slicing C) (P : C) (φ : ℝ) (hP : s.P φ P) (hP0 : ¬IsZero P) :
    s.CarriesOnce (isoClass P) ⊥ P :=
  let T : AlgebraicGeometry.K3.PicardRankOne.TowerHypotheses C :=
    TowerHypotheses.ofSemistable s P φ hP hP0
  AlgebraicGeometry.K3.PicardRankOne.TowerHypotheses.tower T

end CategoryTheory.Triangulated.TowerModel
