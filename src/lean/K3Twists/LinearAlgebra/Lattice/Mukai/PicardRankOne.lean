/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Basic
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

A spherical twist `T_Y` acts on Mukai vectors by `v ↦ v + ⟨v(Y), v⟩ v(Y)`, the reflection in the
root `v(Y)`; `T_Y⁻¹` acts by the same reflection. We prove that it is an isometric involution
sending the root to its negative, and we record the coordinates of the puncture of a root in the
projective model of the stability space.

The definitions work over any commutative ring `R`, so that one set of definitions serves for
integral classes and for complex central charges.
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
instance : SMul R (MukaiVector R) := ⟨fun a v => ⟨a * v.r, a * v.c, a * v.s⟩⟩

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

/-! ### Reflections: the action of a spherical twist -/

/-- The reflection `v ↦ v + ⟨δ, v⟩ δ` in a root `δ`. For `δ = v(Y)` this is the action of the
spherical twist `T_Y` (and of `T_Y⁻¹`) on Mukai vectors. -/
def reflect (d : R) (δ v : MukaiVector R) : MukaiVector R :=
  v + pairing d δ v • δ

/-- The reflection reverses the sign of the pairing with its root. -/
lemma pairing_reflect_root {d : R} {δ : MukaiVector R} (hδ : IsRoot d δ) (v : MukaiVector R) :
    pairing d δ (reflect d δ v) = -pairing d δ v := by
  unfold reflect
  rw [pairing_add_right, pairing_smul_right]
  unfold IsRoot at hδ
  rw [hδ]; ring

/-- `T_Y` sends the class of `Y` to its negative (`T_Y Y = Y[-1]`). -/
lemma reflect_self {d : R} {δ : MukaiVector R} (hδ : IsRoot d δ) : reflect d δ δ = -δ := by
  unfold IsRoot at hδ
  ext <;> simp only [reflect, add_r, add_c, add_s, smul_r, smul_c, smul_s, neg_r, neg_c,
    neg_s, hδ] <;> ring

/-- The reflection is an involution: `T_Y` and `T_Y⁻¹` act by the same map on classes. -/
lemma reflect_reflect {d : R} {δ : MukaiVector R} (hδ : IsRoot d δ) (v : MukaiVector R) :
    reflect d δ (reflect d δ v) = v := by
  have h := pairing_reflect_root hδ v
  ext <;> simp only [reflect, add_r, add_c, add_s, smul_r, smul_c, smul_s] at h ⊢ <;>
    rw [h] <;> ring

/-- The reflection is an isometry of the Mukai lattice. -/
lemma pairing_reflect {d : R} {δ : MukaiVector R} (hδ : IsRoot d δ) (v w : MukaiVector R) :
    pairing d (reflect d δ v) (reflect d δ w) = pairing d v w := by
  unfold reflect
  simp only [pairing_add_left, pairing_add_right, pairing_smul_left, pairing_smul_right]
  unfold IsRoot at hδ
  rw [hδ, pairing_comm d v δ]; ring

/-- Reflecting in a root fixes every vector orthogonal to it. -/
lemma reflect_of_pairing_eq_zero {d : R} {δ v : MukaiVector R} (h : pairing d δ v = 0) :
    reflect d δ v = v := by
  ext <;> simp [reflect, h]

/-- Reflecting twice in the same root (or in two spherical objects with one class, as for
`𝒪_X` and `T_L² 𝒪_X`) acts trivially on Mukai vectors. -/
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

lemma reflect_map (f : R →+* S) (d : R) (δ v : MukaiVector R) :
    (reflect d δ v).map f = reflect (f d) (δ.map f) (v.map f) := by
  ext <;> simp [reflect, map, pairing, map_ofNat]

end map

end MukaiVector
