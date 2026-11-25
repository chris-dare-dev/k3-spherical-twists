/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.BilinearForm.Reflection
import K3Twists.LinearAlgebra.Lattice.Mukai.Basic
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The Mukai lattice of a K3 surface of Picard rank one

Let `X` be a K3 surface with `Pic X = ℤH` and `H² = 2d`. The algebraic Mukai lattice is
`ℤ ⊕ ℤH ⊕ ℤ`; we write a vector as `(r, c, s)` for `r + cH + s`. The Mukai vector of a sheaf of
rank `r` with `c₁ = cH` has last coordinate `s = ch₂ + r`, so

* `v(𝒪_X) = (1, 0, 1)`, `v(𝒪_X(mH)) = (1, m, dm² + 1)`, `v(𝒪_x) = (0, 0, 1)`.

The Mukai pairing is `⟨(r, c, s), (r', c', s')⟩ = 2dcc' - rs' - r's`, and
`χ(E, F) = -⟨v(E), v(F)⟩`. A *root* is a vector of square `-2`: the class of a spherical
object. An *isotropic* vector has square `0`: the class of a point, for instance.

A spherical twist `T_Y` acts on Mukai vectors by `v ↦ v + ⟨v, v(Y)⟩ v(Y)`, the reflection in the
root `v(Y)`; `T_Y⁻¹` acts by the same reflection. We record the coordinates of the puncture of a
root in the projective model of the stability space.

The definitions work over any commutative ring `R`, so that one set of definitions serves for
integral classes and for complex central charges.

## One lattice

`MukaiVector R` is an `R`-module, and `toMukaiLattice` identifies it with `MukaiLattice R R`
coordinate by coordinate. The pairing is the Mukai form of `b x y = 2dxy` on the middle summand
(`Lattice/Mukai/Slice.lean`), bundled here as `mukaiForm d`. The action of a twist is the
reflection `BilinearForm.reflect (mukaiForm d) δ` of the general theory, which is Mathlib's
`Module.preReflection`: the involution, isometry and `T_Y Y = Y[-1]` statements are the general
ones of `BilinearForm/Reflection.lean`, applied to `mukaiForm d`. The rank-one reflection
`MukaiVector.reflect` and its lemmas are deprecated in favour of it.
-/

/-- A vector `(r, c, s)` of the Mukai lattice `R ⊕ RH ⊕ R` of a K3 surface with `Pic = ℤH`. -/
@[ext]
structure MukaiVector (R : Type*) where
  /-- The rank. -/
  r : R
  /-- The coefficient of `H` in the first Chern class. -/
  c : R
  /-- The last coordinate, `ch₂ + r`. -/
  s : R

namespace MukaiVector

variable {R : Type*} [CommRing R]

instance : Zero (MukaiVector R) := ⟨⟨0, 0, 0⟩⟩
instance : Add (MukaiVector R) := ⟨fun v w => ⟨v.r + w.r, v.c + w.c, v.s + w.s⟩⟩
instance : Neg (MukaiVector R) := ⟨fun v => ⟨-v.r, -v.c, -v.s⟩⟩
instance : Sub (MukaiVector R) := ⟨fun v w => ⟨v.r - w.r, v.c - w.c, v.s - w.s⟩⟩
/-- Scalars act coordinatewise, as on `R × R × R`; for `S = ℕ` and `S = ℤ` this is the
`nsmul` and `zsmul` of the additive group below, so the instances agree definitionally. -/
instance {S : Type*} [SMul S R] : SMul S (MukaiVector R) :=
  ⟨fun a v => ⟨a • v.r, a • v.c, a • v.s⟩⟩

@[simp] lemma zero_r : (0 : MukaiVector R).r = 0 := rfl
@[simp] lemma zero_c : (0 : MukaiVector R).c = 0 := rfl
@[simp] lemma zero_s : (0 : MukaiVector R).s = 0 := rfl
@[simp] lemma add_r (v w : MukaiVector R) : (v + w).r = v.r + w.r := rfl
@[simp] lemma add_c (v w : MukaiVector R) : (v + w).c = v.c + w.c := rfl
@[simp] lemma add_s (v w : MukaiVector R) : (v + w).s = v.s + w.s := rfl
@[simp] lemma neg_r (v : MukaiVector R) : (-v).r = -v.r := rfl
@[simp] lemma neg_c (v : MukaiVector R) : (-v).c = -v.c := rfl
@[simp] lemma neg_s (v : MukaiVector R) : (-v).s = -v.s := rfl
@[simp] lemma sub_r (v w : MukaiVector R) : (v - w).r = v.r - w.r := rfl
@[simp] lemma sub_c (v w : MukaiVector R) : (v - w).c = v.c - w.c := rfl
@[simp] lemma sub_s (v w : MukaiVector R) : (v - w).s = v.s - w.s := rfl
@[simp] lemma smul_r (a : R) (v : MukaiVector R) : (a • v).r = a * v.r := rfl
@[simp] lemma smul_c (a : R) (v : MukaiVector R) : (a • v).c = a * v.c := rfl
@[simp] lemma smul_s (a : R) (v : MukaiVector R) : (a • v).s = a * v.s := rfl

/-! ### The module structure -/

/-- The coordinates `(r, c, s)` of a Mukai vector, as a vector of the Mukai lattice
`MukaiLattice R R = R × R × R`. -/
def toMukaiLattice (v : MukaiVector R) : MukaiLattice R R := (v.r, v.c, v.s)

omit [CommRing R] in
@[simp] lemma toMukaiLattice_mk (r c s : R) :
    toMukaiLattice (⟨r, c, s⟩ : MukaiVector R) = (r, c, s) := rfl

omit [CommRing R] in
lemma toMukaiLattice_injective : Function.Injective (toMukaiLattice : MukaiVector R → _) := by
  rintro ⟨r, c, s⟩ ⟨r', c', s'⟩ h
  simp only [toMukaiLattice_mk, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

instance : AddCommGroup (MukaiVector R) :=
  toMukaiLattice_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

instance : Module R (MukaiVector R) :=
  toMukaiLattice_injective.module R
    { toFun := toMukaiLattice, map_zero' := rfl, map_add' := fun _ _ => rfl } fun _ _ => rfl

/-- **The rank-one lattice is a Mukai lattice.** The coordinates identify `MukaiVector R` with
`MukaiLattice R R`, `R`-linearly; under this identification the pairing is the Mukai form of
`b x y = 2dxy` (`Mukai.mukaiForm_rankOne_toMukaiLatticeEquiv` in `Lattice/Mukai/Slice.lean`). -/
def toMukaiLatticeEquiv : MukaiVector R ≃ₗ[R] MukaiLattice R R where
  toFun := toMukaiLattice
  invFun v := ⟨v.1, v.2.1, v.2.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] lemma toMukaiLatticeEquiv_apply (v : MukaiVector R) :
    toMukaiLatticeEquiv v = (v.r, v.c, v.s) := rfl

/-! ### Distinguished vectors -/

/-- `v(𝒪_x) = (0, 0, 1)`, the class of a point. -/
def point : MukaiVector R := ⟨0, 0, 1⟩

/-- `v(𝒪_X(mH)) = (1, m, dm² + 1)`. -/
def lineBundle (d m : R) : MukaiVector R := ⟨1, m, d * m ^ 2 + 1⟩

/-- `v(𝒪_X) = (1, 0, 1)`. -/
lemma lineBundle_zero (d : R) : lineBundle d 0 = (⟨1, 0, 1⟩ : MukaiVector R) := by
  ext <;> simp [lineBundle]

/-! ### The pairing -/

/-- The Mukai pairing `⟨(r, c, s), (r', c', s')⟩ = 2dcc' - rs' - r's`, where `H² = 2d`. -/
def pairing (d : R) (v w : MukaiVector R) : R :=
  2 * d * v.c * w.c - v.r * w.s - w.r * v.s

lemma pairing_comm (d : R) (v w : MukaiVector R) : pairing d v w = pairing d w v := by
  unfold pairing; ring

lemma pairing_add_left (d : R) (u v w : MukaiVector R) :
    pairing d (u + v) w = pairing d u w + pairing d v w := by
  simp only [pairing, add_r, add_c, add_s]; ring

lemma pairing_add_right (d : R) (u v w : MukaiVector R) :
    pairing d u (v + w) = pairing d u v + pairing d u w := by
  simp only [pairing, add_r, add_c, add_s]; ring

lemma pairing_smul_left (d a : R) (v w : MukaiVector R) :
    pairing d (a • v) w = a * pairing d v w := by
  simp only [pairing, smul_r, smul_c, smul_s]; ring

lemma pairing_smul_right (d a : R) (v w : MukaiVector R) :
    pairing d v (a • w) = a * pairing d v w := by
  simp only [pairing, smul_r, smul_c, smul_s]; ring

lemma pairing_neg_left (d : R) (v w : MukaiVector R) : pairing d (-v) w = -pairing d v w := by
  simp only [pairing, neg_r, neg_c, neg_s]; ring

lemma pairing_neg_right (d : R) (v w : MukaiVector R) : pairing d v (-w) = -pairing d v w := by
  simp only [pairing, neg_r, neg_c, neg_s]; ring

/-- The Mukai pairing as a bundled symmetric bilinear form on the `R`-module `MukaiVector R`. Its
value is `pairing` by `rfl`, so a root `IsRoot d δ` is accepted wherever the general theory asks
for `mukaiForm d δ δ = -2`. -/
def mukaiForm (d : R) : LinearMap.BilinForm R (MukaiVector R) :=
  LinearMap.mk₂ R (pairing d) (pairing_add_left d)
    (fun a v w => by rw [pairing_smul_left, smul_eq_mul]) (pairing_add_right d)
    (fun a v w => by rw [pairing_smul_right, smul_eq_mul])

@[simp] lemma mukaiForm_apply (d : R) (v w : MukaiVector R) : mukaiForm d v w = pairing d v w :=
  rfl

lemma mukaiForm_comm (d : R) (v w : MukaiVector R) : mukaiForm d v w = mukaiForm d w v :=
  pairing_comm d v w

/-- A root: a vector of Mukai square `-2`, the class of a spherical object. -/
def IsRoot (d : R) (δ : MukaiVector R) : Prop :=
  pairing d δ δ = -2

/-- An isotropic vector: Mukai square `0`. -/
def IsIsotropic (d : R) (v : MukaiVector R) : Prop :=
  pairing d v v = 0

lemma isIsotropic_point (d : R) : IsIsotropic d (point : MukaiVector R) := by
  simp [IsIsotropic, pairing, point]

lemma isRoot_lineBundle (d m : R) : IsRoot d (lineBundle d m) := by
  simp only [IsRoot, pairing, lineBundle]; ring

/-- `χ(𝒪_x, 𝒪_X(mH)) = 1`: the pairing of a point with a line bundle is `-1`. -/
lemma pairing_point_lineBundle (d m : R) : pairing d point (lineBundle d m) = -1 := by
  simp [pairing, point, lineBundle]

/-- Two line bundles pair to `-(d(m - m')² + 2)`; for `𝒪_X` and `𝒪_X(H)` this is `-(d + 2)`. -/
lemma pairing_lineBundle (d m m' : R) :
    pairing d (lineBundle d m) (lineBundle d m') = -(d * (m - m') ^ 2 + 2) := by
  simp only [pairing, lineBundle]; ring

/-- Over a ring in which `2` cancels, a vector is a root exactly when `rs = dc² + 1`. -/
lemma isRoot_iff [IsDomain R] [CharZero R] (d : R) (δ : MukaiVector R) :
    IsRoot d δ ↔ δ.r * δ.s = d * δ.c ^ 2 + 1 := by
  unfold IsRoot pairing
  constructor
  · intro h
    have h2 : (2 : R) * (δ.r * δ.s) = 2 * (d * δ.c ^ 2 + 1) := by linear_combination -h
    exact mul_left_cancel₀ (OfNat.ofNat_ne_zero 2) h2
  · intro h; linear_combination (-2 : R) * h

/-! ### Reflections: the action of a spherical twist

The action of `T_Y` on Mukai vectors is the reflection `BilinearForm.reflect (mukaiForm d) δ` in
the root `δ = v(Y)`. The general lemmas apply to it directly: `BilinearForm.reflect_reflect`
(an involution, so `T_Y` and `T_Y⁻¹` act alike), `BilinearForm.apply_reflect_reflect` (an
isometry, with `mukaiForm_comm`), `BilinearForm.reflect_self` (`T_Y Y = Y[-1]`) and
`BilinearForm.reflect_of_apply_eq_zero` (it fixes `δ^⊥`). The rank-one names below are
deprecated aliases, each proved from the general statement. -/

/-- The rank-one reflection is the reflection of the bundled Mukai form. -/
lemma bilinearFormReflect_apply (d : R) (δ v : MukaiVector R) :
    BilinearForm.reflect (mukaiForm d) δ v = v + pairing d δ v • δ := by
  rw [BilinearForm.reflect_apply, mukaiForm_apply, pairing_comm]

/-- The reflection `v ↦ v + ⟨δ, v⟩ δ` in a root `δ`. -/
@[deprecated BilinearForm.reflect +typeChanged (since := "2026-11-25")]
def reflect (d : R) (δ v : MukaiVector R) : MukaiVector R :=
  v + pairing d δ v • δ

set_option linter.deprecated false in
@[deprecated bilinearFormReflect_apply (since := "2026-11-25")]
lemma reflect_eq_bilinearFormReflect (d : R) (δ v : MukaiVector R) :
    reflect d δ v = BilinearForm.reflect (mukaiForm d) δ v :=
  (bilinearFormReflect_apply d δ v).symm

set_option linter.deprecated false in
/-- The reflection reverses the sign of the pairing with its root. -/
@[deprecated BilinearForm.apply_reflect_right (since := "2026-11-25")]
lemma pairing_reflect_root {d : R} {δ : MukaiVector R} (hδ : IsRoot d δ) (v : MukaiVector R) :
    pairing d δ (reflect d δ v) = -pairing d δ v := by
  rw [pairing_comm d δ, pairing_comm d δ, reflect_eq_bilinearFormReflect, ← mukaiForm_apply,
    BilinearForm.apply_reflect_right (mukaiForm d) δ hδ, mukaiForm_apply]

set_option linter.deprecated false in
/-- `T_Y` sends the class of `Y` to its negative (`T_Y Y = Y[-1]`). -/
@[deprecated BilinearForm.reflect_self (since := "2026-11-25")]
lemma reflect_self {d : R} {δ : MukaiVector R} (hδ : IsRoot d δ) : reflect d δ δ = -δ := by
  rw [reflect_eq_bilinearFormReflect, BilinearForm.reflect_self (mukaiForm d) δ hδ]

set_option linter.deprecated false in
/-- The reflection is an involution: `T_Y` and `T_Y⁻¹` act by the same map on classes. -/
@[deprecated BilinearForm.reflect_reflect (since := "2026-11-25")]
lemma reflect_reflect {d : R} {δ : MukaiVector R} (hδ : IsRoot d δ) (v : MukaiVector R) :
    reflect d δ (reflect d δ v) = v := by
  rw [reflect_eq_bilinearFormReflect, reflect_eq_bilinearFormReflect,
    BilinearForm.reflect_reflect (mukaiForm d) δ hδ]

set_option linter.deprecated false in
/-- The reflection is an isometry of the Mukai lattice. -/
@[deprecated BilinearForm.apply_reflect_reflect (since := "2026-11-25")]
lemma pairing_reflect {d : R} {δ : MukaiVector R} (hδ : IsRoot d δ) (v w : MukaiVector R) :
    pairing d (reflect d δ v) (reflect d δ w) = pairing d v w := by
  rw [reflect_eq_bilinearFormReflect, reflect_eq_bilinearFormReflect, ← mukaiForm_apply,
    BilinearForm.apply_reflect_reflect (mukaiForm d) (mukaiForm_comm d) δ hδ, mukaiForm_apply]

set_option linter.deprecated false in
/-- Reflecting in a root fixes every vector orthogonal to it. -/
@[deprecated BilinearForm.reflect_of_apply_eq_zero (since := "2026-11-25")]
lemma reflect_of_pairing_eq_zero {d : R} {δ v : MukaiVector R} (h : pairing d δ v = 0) :
    reflect d δ v = v := by
  rw [reflect_eq_bilinearFormReflect, BilinearForm.reflect_of_apply_eq_zero]
  rwa [mukaiForm_apply, pairing_comm]

set_option linter.deprecated false in
/-- Reflecting twice in the same root (or in two spherical objects with one class, as for
`𝒪_X` and `T_L² 𝒪_X`) acts trivially on Mukai vectors. -/
@[deprecated BilinearForm.reflect_involutive (since := "2026-11-25")]
lemma reflect_comp_reflect {d : R} {δ : MukaiVector R} (hδ : IsRoot d δ) :
    reflect d δ ∘ reflect d δ = id := by
  funext v; exact reflect_reflect hδ v

/-! ### Punctures

A root `(r, c, s)` of positive rank has its puncture at `(b, t) = (c/r, s/(dr))` in the
coordinates `t = b² + a²` of `z = b + ia`. Its height above the parabola `t = b²` of isotropic
lines is `1/(dr²)`. -/

/-- The puncture of a root lies at height `1/(dr²)` above the parabola `t = b²`:
`s/(dr) = (c/r)² + 1/(dr²)`. -/
lemma puncture_height {K : Type*} [Field K] [CharZero K] {d : K} {δ : MukaiVector K}
    (hδ : IsRoot d δ) (hd : d ≠ 0) (hr : δ.r ≠ 0) :
    δ.s / (d * δ.r) = (δ.c / δ.r) ^ 2 + 1 / (d * δ.r ^ 2) := by
  rw [isRoot_iff] at hδ
  field_simp
  linear_combination hδ

/-! ### Change of coefficients -/

section map

variable {S : Type*} [CommRing S]

/-- Push a Mukai vector forward along a ring map, for instance from `ℤ` to `ℂ`. -/
def map (f : R →+* S) (v : MukaiVector R) : MukaiVector S := ⟨f v.r, f v.c, f v.s⟩

@[simp] lemma map_r (f : R →+* S) (v : MukaiVector R) : (v.map f).r = f v.r := rfl
@[simp] lemma map_c (f : R →+* S) (v : MukaiVector R) : (v.map f).c = f v.c := rfl
@[simp] lemma map_s (f : R →+* S) (v : MukaiVector R) : (v.map f).s = f v.s := rfl

lemma pairing_map (f : R →+* S) (d : R) (v w : MukaiVector R) :
    pairing (f d) (v.map f) (w.map f) = f (pairing d v w) := by
  simp [pairing, map, map_ofNat]

/-- The reflection commutes with change of coefficients. -/
lemma map_bilinearFormReflect (f : R →+* S) (d : R) (δ v : MukaiVector R) :
    (BilinearForm.reflect (mukaiForm d) δ v).map f =
      BilinearForm.reflect (mukaiForm (f d)) (δ.map f) (v.map f) := by
  ext <;> simp [BilinearForm.reflect_apply, map, pairing, map_ofNat]

set_option linter.deprecated false in
@[deprecated map_bilinearFormReflect (since := "2026-11-25")]
lemma reflect_map (f : R →+* S) (d : R) (δ v : MukaiVector R) :
    (reflect d δ v).map f = reflect (f d) (δ.map f) (v.map f) := by
  rw [reflect_eq_bilinearFormReflect, reflect_eq_bilinearFormReflect, map_bilinearFormReflect]

end map

end MukaiVector
