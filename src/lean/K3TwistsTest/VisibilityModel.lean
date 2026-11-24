/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.PicardRankOne.VisibilityOnCover

/-!
# The field list of `VisibilityHypotheses` can be met

This file builds a model of `VisibilityHypotheses` at `d = 1`: the objects are the shifts
`𝒪_x[n]` of one point, with classes `±(0, 0, 1)`, no spherical objects, no stability conditions
and no marked punctures, under the trivial group. The fields about objects hold outright, and
those about stability conditions and marked punctures hold vacuously.

So the model only shows that the list of fields is not contradictory in itself. A model with
stability conditions needs Bridgeland stability on a K3 surface, which Mathlib does not have.

Built by `lake test`.
-/

namespace AlgebraicGeometry.K3.PicardRankOne.VisibilityModel

open MukaiVector

/-- The object `n` is `𝒪_x[n]`. -/
abbrev Obj := ℤ

/-- `v(𝒪_x[n]) = (-1)ⁿ (0, 0, 1)`. -/
def cl (n : Obj) : MukaiVector ℤ := if Even n then point else -point

/-- The trivial group acts trivially on the objects. -/
instance : MulAction Unit Obj where
  smul _ U := U
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The trivial group acts trivially on the (empty) space of stability conditions. -/
instance : MulAction Unit Empty where
  smul _ σ := σ
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The model. -/
noncomputable def model : VisibilityHypotheses Obj Empty Empty Unit where
  d := 1
  d_pos := one_pos
  cl := cl
  cl_vadd_one n := by
    simp only [cl, vadd_eq_add]
    by_cases h : Even n
    · have : ¬Even (1 + n) := by rw [add_comm, Int.even_add_one]; exact not_not.mpr h
      simp [h, this]
    · have : Even (1 + n) := by rw [add_comm, Int.even_add_one]; exact h
      simp only [h, this, ↓reduceIte]
      ext <;> simp
  Spherical _ := False
  spherical_vadd _ _ h := h
  isRoot_cl _ h := h.elim
  base σ := σ.elim
  base_mem σ := σ.elim
  charge σ := σ.elim
  normalization σ := σ.elim
  charge_eq σ := σ.elim
  charge_ne_zero σ := σ.elim
  Semistable σ := σ.elim
  Stable σ := σ.elim
  semistable_of_stable σ := σ.elim
  stable_vadd σ := σ.elim
  phase σ := σ.elim
  phase_vadd σ := σ.elim
  charge_cl σ := σ.elim
  factors σ := σ.elim
  factors_stable σ := σ.elim
  factors_sum σ := σ.elim
  stable_of_length_factors σ := σ.elim
  spherical_of_mem_factors σ := σ.elim
  pairing_nonneg σ := σ.elim
  isOpen_stable _ := by
    convert isOpen_empty
  isClosed_semistable _ := by
    convert isClosed_empty
  root ℓ := ℓ.elim
  isRoot_root ℓ := ℓ.elim
  root_r_pos ℓ := ℓ.elim
  Sees σ := σ.elim
  segmentClear_of_sees σ := σ.elim
  exists_sees σ := σ.elim
  isPreconnected_sees _ := by
    convert isPreconnected_empty
  sphere ℓ := ℓ.elim
  spherical_sphere ℓ := ℓ.elim
  cl_sphere ℓ := ℓ.elim
  exists_stable_sphere ℓ := ℓ.elim
  sphere_injective ℓ := ℓ.elim
  exists_stable _ h := h.elim
  stable_smul _ σ := σ.elim
  point := 0
  Geometric σ := σ.elim
  stable_point_iff σ := σ.elim
  OnGeometricSheet σ := σ.elim
  geometric_iff σ := σ.elim

/-- In the model a spherical object would be a shifted marked sphere: vacuously, since there are
none. -/
example (E : Obj) (hE : model.Spherical E) : ∃ ℓ, ∃ n : ℤ, E = n +ᵥ model.sphere ℓ :=
  model.exists_eq_vadd_sphere hE

end AlgebraicGeometry.K3.PicardRankOne.VisibilityModel
