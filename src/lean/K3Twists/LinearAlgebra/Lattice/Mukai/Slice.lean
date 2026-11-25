/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.Lattice.Mukai.PicardRankOne
import K3Twists.LinearAlgebra.Lattice.Mukai.Reflection
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv

/-!
# The slice of a class in the Mukai lattice

Fix a class `ℓ` of an `R`-module `N` with a bilinear form `b`, and write `b ℓ ℓ = 2d`. The
**slice** of `ℓ` is the `R`-linear map

```
MukaiVector R → MukaiLattice R N,   (r, c, s) ↦ (r, c ℓ, s),
```

and it carries the Picard-rank-one pairing `2dcc' - rs' - r's` to the Mukai form of `b`
(`mukaiForm_slice`). For a K3 surface with an ample class `ℓ = H`, it is the inclusion of the
classes `r + cH + s` into the Mukai lattice `H⁰ ⊕ NS ⊕ H⁴`.

The slice is defined over every commutative ring. It is injective when `c ↦ c ℓ` is, but it is
not surjective unless `N = Rℓ`, so no additive equivalence onto `MukaiLattice R N` is claimed.
For `N = R`, `ℓ = 1` and `b x y = 2dxy` (`rankOneForm d`) it is the coordinate equivalence
`MukaiVector.toMukaiLatticeEquiv`, and an isometry (`MukaiVector.isometryEquivMukaiLattice`): the
lattice of a K3 surface of Picard rank one is the Mukai lattice of the rank-one lattice
`(ℤ, 2dxy)`.

## The slice lemma

On the slice, the exponential points are `e^{zℓ} = (1, zℓ, dz²)` (`expSlice`), isotropic for
every `z`. For a root `δ = (r, μℓ, s)` the reflection `ρ_δ` carries `e^{zℓ}` to a multiple of
another exponential point (`reflect_expSlice`):

```
ρ_δ(e^{zℓ}) = -d r² (z - μ/r)² · e^{z'ℓ},   z' = μ/r - 1/(d r² (z - μ/r)).
```

It holds over **any field**, under the halved root condition `rs = dμ² + 1`. The condition
`⟪δ, δ⟫ = -2` alone does not suffice in characteristic two, where `⟪δ, δ⟫ = 2dμ² - 2rs = 0 = -2`
holds for every `δ` (the counterexample `δ = (1, 0, 0)` over `ZMod 2` is a test); over a domain
in which `2 ≠ 0` the two conditions agree.

The coordinate `z'` is the base map of a twist in Picard rank one, and the scalar is the factor
of the half-turn identity `charge_halfTurn` (`AlgebraicGeometry/Surface/K3/PicardRankOne/`
`CentralCharge.lean`); the coordinate-free statement behind it is
`Mukai.charge_halfTurn_of_isometry` (`Lattice/Mukai/CentralCharge.lean`).

## Main results

* `slice` — the `R`-linear slice map; `mukaiForm_slice`, `slice_reflect`: it is isometric and
  intertwines the reflections, whenever `b ℓ ℓ = 2d`.
* `MukaiVector.isometryEquivMukaiLattice` — the rank-one lattice is `MukaiLattice R R`.
* `mukaiForm_expSlice_slice` — `⟪e^{zℓ}, (r, cℓ, s)⟫ = 2dcz - s - drz²`.
* `reflect_expSlice` — the slice lemma, over any field, under `rs = dμ² + 1`.
-/

namespace Mukai

variable {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N]
variable (b : N →ₗ[R] N →ₗ[R] R)

/-! ### The slice map -/

/-- The slice of `ℓ`: `(r, c, s) ↦ (r, c ℓ, s)`, an `R`-linear map from the Picard-rank-one
lattice to the Mukai lattice of `N`. -/
def slice (ℓ : N) : MukaiVector R →ₗ[R] MukaiLattice R N where
  toFun v := (v.r, v.c • ℓ, v.s)
  map_add' v w := by
    simp only [MukaiVector.add_r, MukaiVector.add_c, MukaiVector.add_s, add_smul, Prod.mk_add_mk]
  map_smul' a v := by
    simp only [MukaiVector.smul_r, MukaiVector.smul_c, MukaiVector.smul_s, mul_smul,
      RingHom.id_apply, Prod.smul_mk, smul_eq_mul]

@[simp]
theorem slice_apply (ℓ : N) (v : MukaiVector R) : slice ℓ v = (v.r, v.c • ℓ, v.s) :=
  rfl

variable {b}

/-- **The slice is isometric.** For `b ℓ ℓ = 2d` the Mukai form of `b` restricts to the
Picard-rank-one pairing. No symmetry of `b` is needed. -/
theorem mukaiForm_slice {ℓ : N} {d : R} (hℓ : b ℓ ℓ = 2 * d) (v w : MukaiVector R) :
    mukaiForm b (slice ℓ v) (slice ℓ w) = MukaiVector.pairing d v w := by
  simp only [mukaiForm_apply, slice_apply, pairing_mk, map_smul, LinearMap.smul_apply,
    smul_eq_mul, hℓ, MukaiVector.pairing]
  ring

/-- A class of the slice is spherical exactly when it is a root of the rank-one lattice. -/
theorem isSpherical_slice_iff {ℓ : N} {d : R} (hℓ : b ℓ ℓ = 2 * d) (δ : MukaiVector R) :
    IsSpherical b (slice ℓ δ) ↔ MukaiVector.IsRoot d δ := by
  rw [IsSpherical, selfPairing_eq_pairing, ← mukaiForm_apply, mukaiForm_slice hℓ,
    MukaiVector.IsRoot]

/-- **The slice intertwines the reflections.** The reflection of the rank-one lattice in `δ` is
the restriction of the reflection of the Mukai lattice in `slice ℓ δ`. -/
theorem slice_reflect {ℓ : N} {d : R} (hℓ : b ℓ ℓ = 2 * d) (δ v : MukaiVector R) :
    slice ℓ (BilinearForm.reflect (MukaiVector.mukaiForm d) δ v) =
      reflect b (slice ℓ δ) (slice ℓ v) := by
  rw [BilinearForm.reflect_apply, reflect_apply, map_add, map_smul, MukaiVector.mukaiForm_apply,
    ← mukaiForm_apply, mukaiForm_slice hℓ]

/-! ### Picard rank one -/

variable (d : R)

/-- The rank-one lattice `(R, 2dxy)`: the Néron–Severi lattice `ℤH` with `H² = 2d` of a K3
surface of Picard rank one, written in the coordinate of `H`. -/
def rankOneForm : LinearMap.BilinForm R R := (2 * d) • LinearMap.mul R R

@[simp]
theorem rankOneForm_apply (x y : R) : rankOneForm d x y = 2 * d * (x * y) :=
  rfl

theorem rankOneForm_one_one : rankOneForm d 1 1 = 2 * d := by
  simp

/-- On `N = R` the slice of `ℓ = 1` is the coordinate equivalence. -/
theorem slice_one (v : MukaiVector R) : slice (1 : R) v = MukaiVector.toMukaiLatticeEquiv v := by
  simp

end Mukai

namespace MukaiVector

variable {R : Type*} [CommRing R]

/-- **The Picard-rank-one lattice is a Mukai lattice.** The coordinates `(r, c, s)` are an
isometry from `MukaiVector R` with the pairing `2dcc' - rs' - r's` to the Mukai lattice
`MukaiLattice R R` of the rank-one lattice `(R, 2dxy)`. -/
def isometryEquivMukaiLattice (d : R) :
    (mukaiForm d).IsometryEquiv (Mukai.mukaiForm (Mukai.rankOneForm d)) where
  toLinearEquiv := toMukaiLatticeEquiv
  map_app' v w := by
    change Mukai.mukaiForm _ (toMukaiLatticeEquiv v) (toMukaiLatticeEquiv w) = _
    rw [← Mukai.slice_one, ← Mukai.slice_one,
      Mukai.mukaiForm_slice (Mukai.rankOneForm_one_one d), mukaiForm_apply]

@[simp]
theorem isometryEquivMukaiLattice_apply (d : R) (v : MukaiVector R) :
    isometryEquivMukaiLattice d v = (v.r, v.c, v.s) :=
  rfl

/-- The pairing of the rank-one lattice is the Mukai form of `(R, 2dxy)` in coordinates. -/
theorem pairing_eq_mukaiForm_rankOneForm (d : R) (v w : MukaiVector R) :
    pairing d v w =
      Mukai.mukaiForm (Mukai.rankOneForm d) (toMukaiLatticeEquiv v) (toMukaiLatticeEquiv w) :=
  ((isometryEquivMukaiLattice d).map_app w v).symm

end MukaiVector

namespace Mukai

variable {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N]
variable {b : N →ₗ[R] N →ₗ[R] R}

/-! ### Exponential points on the slice -/

/-- The exponential point `e^{zℓ} = (1, zℓ, dz²)`; for `b ℓ ℓ = 2d` its last coordinate is
`b(zℓ, zℓ)/2`. -/
def expSlice (ℓ : N) (d z : R) : MukaiLattice R N := (1, z • ℓ, d * z ^ 2)

/-- `⟪e^{zℓ}, (r, cℓ, s)⟫ = 2dcz - s - drz²`: on the slice, the Mukai form against an exponential
point is the central charge of Picard rank one. -/
theorem mukaiForm_expSlice_slice {ℓ : N} {d : R} (hℓ : b ℓ ℓ = 2 * d) (z : R)
    (v : MukaiVector R) :
    mukaiForm b (expSlice ℓ d z) (slice ℓ v) = 2 * d * v.c * z - v.s - d * v.r * z ^ 2 := by
  simp only [mukaiForm_apply, expSlice, slice_apply, pairing_mk, map_smul, LinearMap.smul_apply,
    smul_eq_mul, hℓ]
  ring

/-- Exponential points are isotropic. -/
theorem isIsotropic_expSlice {ℓ : N} {d : R} (hℓ : b ℓ ℓ = 2 * d) (z : R) :
    IsIsotropic b (expSlice ℓ d z) := by
  simp only [IsIsotropic, expSlice, selfPairing_mk, map_smul, LinearMap.smul_apply, smul_eq_mul,
    hℓ]
  ring

/-- **The slice lemma.** Let `b ℓ ℓ = 2d` and `δ = (r, μℓ, s)` with the halved root condition
`rs = dμ² + 1`, `r ≠ 0`, `d ≠ 0`. Off the slope `μ/r`,

`ρ_δ(e^{zℓ}) = -d r² (z - μ/r)² · e^{z'ℓ}`,  `z' = μ/r - 1/(d r²)/(z - μ/r)`.

Over any field: no characteristic hypothesis. The condition `⟪δ, δ⟫ = -2` would not do in
characteristic two (see the module docstring). -/
theorem reflect_expSlice {K N : Type*} [Field K] [AddCommGroup N] [Module K N]
    {b : N →ₗ[K] N →ₗ[K] K} {ℓ : N} {d : K} (hℓ : b ℓ ℓ = 2 * d) {r μ s : K}
    (hδ : r * s = d * μ ^ 2 + 1) (hr : r ≠ 0) (hd : d ≠ 0) {z : K} (hz : z ≠ μ / r) :
    reflect b (r, μ • ℓ, s) (expSlice ℓ d z) =
      (-(d * r ^ 2 * (z - μ / r) ^ 2)) • expSlice ℓ d (μ / r - 1 / (d * r ^ 2) / (z - μ / r)) := by
  have hs : s = (d * μ ^ 2 + 1) / r := by
    field_simp
    linear_combination hδ
  obtain ⟨w, rfl⟩ : ∃ w, z = μ / r + w := ⟨z - μ / r, by ring⟩
  have hw : w ≠ 0 := by
    rintro rfl
    exact hz (add_zero _)
  simp only [reflect_apply, expSlice, pairing_mk, map_smul, LinearMap.smul_apply, smul_eq_mul,
    hℓ, Prod.smul_mk, Prod.mk_add_mk, smul_smul, ← add_smul, add_sub_cancel_left, hs]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp only
  · field_simp
    ring
  · congr 1
    field_simp
    ring
  · field_simp
    ring

end Mukai
