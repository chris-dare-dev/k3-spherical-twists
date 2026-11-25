/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.BilinearForm.Eichler
import K3Twists.LinearAlgebra.Lattice.Mukai.Slice

/-!
# Line bundles and Eichler transvections on the Mukai lattice

On the Mukai lattice `MukaiLattice R N`, tensoring with a line bundle `𝒪(D)` acts by
multiplication by `ch(𝒪(D)) = (1, D, D²/2)`:

```
⊗𝒪(D) : (r, c, s) ↦ (r, c + rD, s + b(c, D) + r D²/2).
```

`tensorLine b D q` is this map with `q` in place of `D²/2`, and it is the Eichler transvection
at the class `pt = (0, 0, 1)` of a point (`tensorLine_eq_eichler`):

```
⊗𝒪(D) = E(pt, (0, -D, 0), D²/2).
```

**The convention.** `E(e, x, q)(v) = v + ⟪v, e⟫x - ⟪v, x⟫e - q⟪v, e⟫e` (`BilinearForm.eichler`),
and `⊗𝒪(D)` is the transvection with direction `(0, -D, 0)`, the sign that makes it
multiplication by `ch(𝒪(D))` rather than by `ch(𝒪(-D))`.

The identity holds for every `q`; the map is an isometry exactly in the case `2q = b(D, D)`. To
tie `q` to `D²/2` without dividing by two, the Mukai lattice of a quadratic module `(N, q_N)`
carries the quadratic form `Q(r, c, s) = q_N(c) - rs` (`quadraticForm`), whose polar form is the
Mukai form of the polar form of `q_N` (`polarBilin_quadraticForm`), and
`⊗𝒪(D) = E_Q(pt, (0, -D, 0))` with the parameter `Q(0, -D, 0) = q_N(D)` forced
(`tensorLine_eq_eichlerQ`). Line bundles then compose by the group law of the Eichler
homomorphism at `pt` (`tensorLine_mul`).

## Main results

* `tensorLine_eq_eichler`, `tensorLine_eq_eichlerQ` — `⊗𝒪(D)` is the Eichler transvection at the
  point class.
* `tensorLine_mul`, `mukaiForm_tensorLine` — `⊗𝒪(D) ⊗𝒪(D') = ⊗𝒪(D + D')`, and `⊗𝒪(D)` is an
  isometry.
* `reflectHom_mul_reflectHom_curve` — `ρ_{(0, C, 0)} ρ_{(0, C, 1)} = ⊗𝒪(C)` from `C² = -2` alone:
  the two spherical simples `𝒪_C(-1)[1]` and `𝒪_C` of the wall contracting a `(-2)`-curve `C`.
* `slice_lineBundle` — in Picard rank one, `v(𝒪(mH)) = ⊗𝒪(mH) v(𝒪_X)`.
-/

namespace Mukai

open BilinearForm

variable {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N]

/-! ### The Mukai quadratic form -/

/-- The Mukai quadratic form `Q(r, c, s) = q_N(c) - rs` of a quadratic module `(N, q_N)`. -/
def quadraticForm (qN : QuadraticForm R N) : QuadraticForm R (MukaiLattice R N) :=
  qN.comp (LinearMap.fst R N R ∘ₗ LinearMap.snd R R (N × R)) -
    LinearMap.BilinMap.toQuadraticMap
      ((LinearMap.mul R R).compl₁₂ (LinearMap.fst R R (N × R))
        (LinearMap.snd R N R ∘ₗ LinearMap.snd R R (N × R)))

@[simp]
theorem quadraticForm_apply (qN : QuadraticForm R N) (v : MukaiLattice R N) :
    quadraticForm qN v = qN v.2.1 - v.1 * v.2.2 :=
  rfl

/-- The polar form of the Mukai quadratic form is the Mukai form of the polar form of `q_N`. -/
theorem polarBilin_quadraticForm (qN : QuadraticForm R N) :
    (quadraticForm qN).polarBilin = mukaiForm qN.polarBilin := by
  refine LinearMap.ext₂ fun v w => ?_
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, quadraticForm_apply,
    Prod.fst_add, Prod.snd_add, mukaiForm_apply, pairing]
  ring

variable (b : N →ₗ[R] N →ₗ[R] R)

/-! ### Tensoring with a line bundle -/

/-- Tensoring with a line bundle `𝒪(D)` on Mukai vectors, multiplication by `ch(𝒪(D))`:
`(r, c, s) ↦ (r, c + rD, s + b(c, D) + rq)`, with `q` standing for `D²/2`. -/
def tensorLine (D : N) (q : R) : MukaiLattice R N →ₗ[R] MukaiLattice R N where
  toFun v := (v.1, v.2.1 + v.1 • D, v.2.2 + b v.2.1 D + v.1 * q)
  map_add' v w := by
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · simp only [Prod.fst_add, Prod.snd_add, add_smul]
      abel
    · simp only [Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]
      ring
  map_smul' a v := by
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, smul_add, smul_eq_mul, mul_smul]
    · simp only [Prod.smul_fst, Prod.smul_snd, map_smul, LinearMap.smul_apply, smul_eq_mul,
        RingHom.id_apply]
      ring

@[simp]
theorem tensorLine_apply (D : N) (q : R) (v : MukaiLattice R N) :
    tensorLine b D q v = (v.1, v.2.1 + v.1 • D, v.2.2 + b v.2.1 D + v.1 * q) :=
  rfl

/-- **Tensoring with a line bundle is an Eichler transvection at the point class:**
`⊗𝒪(D) = E(pt, (0, -D, 0), q)`, for every `D` and every `q`. -/
theorem tensorLine_eq_eichler (D : N) (q : R) :
    tensorLine b D q = eichler (mukaiForm b) corankUnit (0, -D, 0) q := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨r, c, s⟩ := v
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [eichler_apply, corankUnit, pairing]
  ring

/-- With the Mukai quadratic form the parameter is forced: `⊗𝒪(D) = E_Q(pt, (0, -D, 0))` with
`q = q_N(D)`, which is `D²/2`. -/
theorem tensorLine_eq_eichlerQ (qN : QuadraticForm R N) (D : N) :
    tensorLine qN.polarBilin D (qN D) = eichlerQ (quadraticForm qN) corankUnit (0, -D, 0) := by
  rw [tensorLine_eq_eichler, eichlerQ, polarBilin_quadraticForm, quadraticForm_apply]
  simp

@[simp]
theorem tensorLine_zero : tensorLine b 0 0 = 1 := by
  ext <;> simp

theorem isIsotropic_corankUnit' : mukaiForm b (corankUnit : MukaiLattice R N) corankUnit = 0 := by
  simp [corankUnit, pairing]

theorem mukaiForm_direction_corankUnit (D : N) :
    mukaiForm b ((0, -D, 0) : MukaiLattice R N) corankUnit = 0 := by
  simp [corankUnit, pairing]

/-- **Line bundles compose by the Eichler group law:**
`⊗𝒪(D) ⊗𝒪(D') = ⊗𝒪(D + D')`, with `q + q' + b(D, D')` for `(D + D')²/2`. -/
theorem tensorLine_mul (hb : ∀ x y, b x y = b y x) (D D' : N) (q q' : R) :
    tensorLine b D q * tensorLine b D' q' = tensorLine b (D + D') (q + q' + b D D') := by
  rw [tensorLine_eq_eichler, tensorLine_eq_eichler, tensorLine_eq_eichler,
    eichler_mul _ (mukaiForm_comm b hb) (isIsotropic_corankUnit' b)
      (mukaiForm_direction_corankUnit b D) (mukaiForm_direction_corankUnit b D')]
  congr 1
  · simp only [Prod.mk_add_mk, add_zero, neg_add]
  · simp [pairing]

/-- `⊗𝒪(D)` is an isometry of the Mukai form when `2q = b(D, D)` and `b` is symmetric. -/
theorem mukaiForm_tensorLine (hb : ∀ x y, b x y = b y x) {D : N} {q : R} (hq : 2 * q = b D D)
    (v w : MukaiLattice R N) :
    mukaiForm b (tensorLine b D q v) (tensorLine b D q w) = mukaiForm b v w := by
  rw [tensorLine_eq_eichler]
  exact eichler_isometry _ (mukaiForm_comm b hb) (isIsotropic_corankUnit' b)
    (mukaiForm_direction_corankUnit b D) (by simp [pairing, hq]) v w

/-! ### The wall of a `(-2)`-curve -/

/-- **`ρ_{(0, C, 0)} ρ_{(0, C, 1)} = ⊗𝒪(C)` on the whole Mukai lattice**, for any `C` with
`C² = -2`; `b` need not be symmetric. For a smooth rational curve `C` on a K3 surface these are
the reflections in the classes of `𝒪_C(-1)[1]` and `𝒪_C`, and `C²/2 = -1`. -/
theorem reflectHom_mul_reflectHom_curve (C : N) (hC : b C C = -2) :
    reflectHom b (0, C, 0) * reflectHom b (0, C, 1) = tensorLine b C (-1) := by
  have h2 : mukaiForm b ((0 : R), C, (1 : R)) ((0 : R), -C, (0 : R)) = 2 := by
    simp [pairing, hC]
  rw [reflectHom, reflectHom, show ((0 : R), C, (0 : R)) = -((0 : R), -C, (0 : R)) by simp,
    BilinearForm.reflectHom_neg, reflectHom_mul_reflectHom_of_apply_eq_two _ h2,
    tensorLine_eq_eichler]
  congr 1
  simp [corankUnit]

/-! ### Picard rank one -/

/-- **Line bundles in Picard rank one.** `v(𝒪(mH)) = ⊗𝒪(mH) v(𝒪_X)`: on the slice of `H`, with
`H² = 2d` and `(mH)²/2 = dm²`. -/
theorem slice_lineBundle (d m : R) :
    slice (1 : R) (MukaiVector.lineBundle d m) =
      tensorLine (rankOneForm d) m (d * m ^ 2) (slice 1 (MukaiVector.lineBundle d 0)) := by
  simp [MukaiVector.lineBundle]
  ring

end Mukai
