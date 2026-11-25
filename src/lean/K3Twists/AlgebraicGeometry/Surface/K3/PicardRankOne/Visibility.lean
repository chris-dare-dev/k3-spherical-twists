/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.PicardRankOne.CentralCharge
import K3Twists.Analysis.Complex.UpperHalfPlane.ProjectiveModel
import K3Twists.LinearAlgebra.Lattice.Mukai.ProjectiveModel
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Order.Interval.Set.Infinite

/-!
# Visibility on the cover: the lattice and the geometry

Let `X` be a K3 surface with `Pic X = ℤH`, `H² = 2d > 0`. Modulo `GL⁺₂(ℝ)`, the distinguished
component of its stability space is the universal cover of the upper half-plane with one puncture
for each root `δ = (r, c, s)` of positive rank. In the projective model `(b, t)`, `t = b² + a²` of
`z = b + ia` (`UpperHalfPlane.projectiveModel`), the half-plane is the region `t > b²`, the
central charge `Z_z` vanishes on the kernel vector `κ = (1, b, dt)`, geodesics are straight, and
the puncture of `δ` is its point `(c/r, s/(dr))`. The lemma "Visibility on the cover" of the
article "Harder–Narasimhan towers of spherical twist words on a Picard-rank-one K3 surface" says
that a spherical object is stable exactly where the straight segment to its puncture is clear (and
lifts to its marking). This file proves the lattice and geometric part of it from Mathlib alone.

## The central charge on real classes

* `modelCharge d p v`: the central charge `Z_z(v) = 2dcz - s - drz²` at the point `z` over
  `p = (b, t)`; `modelCharge_projectiveModel` identifies it with `charge` on `ℍ`;
* `im_modelCharge`, `re_modelCharge`: `Im Z = 2da(c - rb)` and `Re Z = 2db(c - rb) + drt - s`;
* `modelCharge_eq_zero_iff`: `Z_p(v) = 0` exactly on the line of `κ_p`, and
  `modelCharge_eq_ofReal_mul_iff`: `Z_p(v) = λ Z_p(w)` with `λ` real exactly when
  `v = λ w + t κ_p` for some real `t`;
* `im_modelCharge_mul_conj`: the charges of `v` and `w` are real-collinear on the straight line
  `(c - rb)(dRt - S) - (C - Rb)(drt - s) = 0` through the points of `v` and `w` (the wall line of
  the article; `wallLine_eq_neg_det` writes it as `-det(κ_p, v, w)`).

## Punctures and visibility

* `puncture d δ = (c/r, s/(dr))`; it lies at height `1/(dr²)` above the parabola, and `Z_p(δ)`
  vanishes exactly at `p = puncture d δ`;
* `SegmentClear d p δ`: the closed segment from `p` to the puncture of `δ` meets no other puncture;
  `RayClear d p`: the upward ray from `p`, the geodesic ray to the cusp at infinity of the point
  class, meets no puncture; `CuspClear d p m`: the segment from `p` to the finite cusp `(m, m²)`
  meets no puncture. `rayClear_iff` identifies `RayClear` with Bayer–Bridgeland's condition
  `Z(δ) ∉ ℝ_{≤0}` for every root of positive rank (the region `V(X)` of Theorem 2.2 of
  arXiv:1310.8266): the complement of the downward slits under the punctures.

## The lattice arguments of the lemma

* `puncture_mem_segment_iff`: a root lies on the segment from `p` to the puncture of `δ` exactly
  when its class is `l κ_p + m δ` with `l, m ≥ 0`;
* `eq_singleton_of_segmentClear`: if the segment to `δ` is clear and `δ = Σ δ_i` is a sum of roots
  whose central charges are positive multiples of `Z_p(δ)`, then the sum has one term. In the
  proof of the lemma these are the stable factors of a sphere on the verge of losing stability:
  their classes are `λ_i δ + t_i κ` with `Σ λ_i = 1`, `Σ t_i = 0`; a positive `t_i` gives a root of
  positive rank strictly between `δ` and `κ`, and if all `t_i` vanish the root condition forces
  a single term;
* `obstacle_charge_pos_mul`, `pairing_le_neg_three`: an obstacle `δ'` on the way to `δ` has
  `Z_p(δ') = μ Z_p(δ)` with `μ > 0` and `⟨δ, δ'⟩ ≤ -3 < 0`, which contradicts stability of both
  spheres at one phase; the same argument with `⟨δ, δ⟩ = -2` gives uniqueness;
* `exists_first_obstacle`: an obstructed segment has a first obstacle, whose own segment is clear.

## The finite search

* `height_obstacle_ge`, `obstacle_rank_sq_le`: an obstacle on the segment to a root of rank `r`
  has rank `r'` with `r'² ≤ max(r², 1/(d h))`, where `h = t - b²` is the height of `p`; its
  abscissa lies between those of the two ends (`obstacle_abs_c_le`);
* `finite_obstacles`: so only finitely many roots can obstruct a segment;
* `cusp_obstacle_rank_le`, `ray_obstacle_rank_sq_le`: the bounds `r' ≤ e|b - m|/(d h)` for the
  segment to a finite cusp `m = c₀/e` and `d r'² h ≤ 1` for the upward ray;
* `rank_eq_of_slope_eq`: on a vertical sight line through a cusp `c₀/e` in lowest terms, a root
  has rank `e`, since the rank and first Chern class of a root are coprime;
* `cuspClear_of_lt`, `rayClear_of_one_lt`, `segmentClear_of_one_lt`: the resulting clear-sight
  criteria. The opening example (`opening_cuspClear`, `opening_rayClear_segmentClear`) and the
  rigid wall example (`rigid_segmentClear`) are instances; `cuspClear_of_lt` generalizes
  `opening_segment_clear`.

## Sight lines to cusps

* `CuspObstacle`, `CuspRayClear`: the sight line from `p` to the cusp of an isotropic class `w`,
  described by the pairing and the central charge alone: a root `δ'` obstructs it when
  `⟨δ', w⟩ < 0` and `Z_p(δ') ∈ ℝ_{≥0} Z_p(w)`;
* `cuspRayClear_point_iff`, `cuspRayClear_iff_rayClear`: for the point class, or any isotropic
  class of rank zero, it is the upward ray; `cuspRayClear_iff_cuspClear`: for an isotropic class
  `(r, c, s)` of rank `r ≠ 0`, it is the straight segment to the cusp `(c/r, (c/r)²)`; it does not
  depend on the sign or a positive multiple of `w` (`cuspRayClear_neg`, `cuspRayClear_smul`);
* `cuspRayClear_iff_of_isometry`: an isometry of the Mukai lattice that matches real
  proportionality of charges at `p` with that at `q` carries the sight line from `p` to the cusp
  of `u` to the sight line from `q` to the cusp of its image of `u`.

## A decision procedure

* `mem_segment_iff_collinear`: a point is on a segment of the plane exactly when it is on its line
  and in its bounding box, which is decidable for rational points (`castPoint_mem_segment_iff`);
* `rootCandidates`, `segmentClearCheck`: the finite search over the roots `(r, c, (dc² + 1)/r)`
  allowed by the bounds;
* `segmentClear_iff_check`: for a rational point the search decides `SegmentClear`. The kernel
  runs it: `not_segmentClear_example` finds the root `(2, 1, 1)` on the segment from `(3/5, 2/5)`
  to the puncture of `𝒪_X` at `d = 1`, and `rigid_segmentClear_by_search` reproves a case of
  `rigid_segmentClear`.
-/

noncomputable section

namespace AlgebraicGeometry.K3.PicardRankOne

open MukaiVector Complex

/-! ### The central charge on real classes -/

/-- The point `b + i√(t - b²)` of the half-plane over the point `p = (b, t)` of the model. -/
def basePoint (p : ℝ × ℝ) : ℂ := p.1 + Real.sqrt (p.2 - p.1 ^ 2) * I

@[simp] lemma basePoint_re (p : ℝ × ℝ) : (basePoint p).re = p.1 := by simp [basePoint]

@[simp] lemma basePoint_im (p : ℝ × ℝ) : (basePoint p).im = Real.sqrt (p.2 - p.1 ^ 2) := by
  simp [basePoint]

lemma basePoint_projectiveModel (z : UpperHalfPlane) :
    basePoint (UpperHalfPlane.projectiveModel z) = z := by
  apply Complex.ext
  · simp
  · simp [Real.sqrt_sq z.im_pos.le]

/-- The central charge `Z_p(v)` of a real class at the point over `p = (b, t)`. -/
def modelCharge (d : ℝ) (p : ℝ × ℝ) (v : MukaiVector ℝ) : ℂ :=
  charge d (basePoint p) (v.map Complex.ofRealHom)

/-- On the half-plane, `modelCharge` is the central charge `charge`. -/
lemma modelCharge_projectiveModel (d : ℝ) (z : UpperHalfPlane) (v : MukaiVector ℝ) :
    modelCharge d (UpperHalfPlane.projectiveModel z) v = charge d z (v.map Complex.ofRealHom) := by
  rw [modelCharge, basePoint_projectiveModel]

lemma modelCharge_add (d : ℝ) (p : ℝ × ℝ) (v w : MukaiVector ℝ) :
    modelCharge d p (v + w) = modelCharge d p v + modelCharge d p w := by
  simp only [modelCharge, charge, map, add_r, add_c, add_s, map_add]; ring

lemma modelCharge_smul (d : ℝ) (p : ℝ × ℝ) (a : ℝ) (v : MukaiVector ℝ) :
    modelCharge d p (a • v) = a * modelCharge d p v := by
  simp only [modelCharge, charge, map, smul_r, smul_c, smul_s, map_mul, Complex.ofRealHom_eq_coe]
  ring

lemma modelCharge_neg (d : ℝ) (p : ℝ × ℝ) (v : MukaiVector ℝ) :
    modelCharge d p (-v) = -modelCharge d p v := by
  simp only [modelCharge, charge, map, neg_r, neg_c, neg_s, map_neg]; ring

lemma modelCharge_sub (d : ℝ) (p : ℝ × ℝ) (v w : MukaiVector ℝ) :
    modelCharge d p (v - w) = modelCharge d p v - modelCharge d p w := by
  simp only [modelCharge, charge, map, sub_r, sub_c, sub_s, map_sub]; ring

/-- `Im Z_p(v) = 2da(c - rb)`, with `a = √(t - b²)`. -/
lemma im_modelCharge (d : ℝ) (p : ℝ × ℝ) (v : MukaiVector ℝ) :
    (modelCharge d p v).im = 2 * d * Real.sqrt (p.2 - p.1 ^ 2) * (v.c - v.r * p.1) := by
  simp [modelCharge, charge, map, basePoint, sq]
  ring

/-- `Re Z_p(v) = 2db(c - rb) + drt - s` above the parabola. -/
lemma re_modelCharge (d : ℝ) {p : ℝ × ℝ} (hp : p.1 ^ 2 ≤ p.2) (v : MukaiVector ℝ) :
    (modelCharge d p v).re = 2 * d * p.1 * (v.c - v.r * p.1) + d * v.r * p.2 - v.s := by
  have ha : Real.sqrt (p.2 - p.1 ^ 2) ^ 2 = p.2 - p.1 ^ 2 := Real.sq_sqrt (sub_nonneg.mpr hp)
  simp [modelCharge, charge, map, basePoint, sq] at ha ⊢
  rw [ha]
  ring

/-- The central charge vanishes on the kernel vector: `Z_p(κ_p) = 0`. -/
lemma modelCharge_kernelVector (d : ℝ) {p : ℝ × ℝ} (hp : p.1 ^ 2 ≤ p.2) :
    modelCharge d p (kernelVector d p) = 0 := by
  apply Complex.ext
  · rw [re_modelCharge d hp]; simp
  · rw [im_modelCharge]; simp

/-- **The kernel line.** Above the parabola, `Z_p(v) = 0` exactly when `v` is a multiple of the
kernel vector `κ_p = (1, b, dt)`. -/
theorem modelCharge_eq_zero_iff {d : ℝ} (hd : d ≠ 0) {p : ℝ × ℝ} (hp : p.1 ^ 2 < p.2)
    (v : MukaiVector ℝ) : modelCharge d p v = 0 ↔ v = v.r • kernelVector d p := by
  have ha : 0 < Real.sqrt (p.2 - p.1 ^ 2) := Real.sqrt_pos.mpr (sub_pos.mpr hp)
  constructor
  · intro h
    have him := congrArg Complex.im h
    have hre := congrArg Complex.re h
    rw [im_modelCharge, Complex.zero_im] at him
    rw [re_modelCharge d hp.le, Complex.zero_re] at hre
    have hc : v.c = v.r * p.1 := by
      have : 2 * d * Real.sqrt (p.2 - p.1 ^ 2) ≠ 0 := by positivity
      have := (mul_eq_zero.mp him).resolve_left this
      linarith
    rw [hc, sub_self, mul_zero, zero_add] at hre
    ext <;> simp [kernelVector, hc]
    linarith
  · intro h
    rw [h, modelCharge_smul, modelCharge_kernelVector d hp.le, mul_zero]

/-- **Real-proportional charges.** Above the parabola, `Z_p(v) = λ Z_p(w)` for a real `λ` exactly
when `v = λ w + t κ_p` for some real `t`. -/
theorem modelCharge_eq_ofReal_mul_iff {d : ℝ} (hd : d ≠ 0) {p : ℝ × ℝ} (hp : p.1 ^ 2 < p.2)
    (v w : MukaiVector ℝ) (l : ℝ) :
    modelCharge d p v = l * modelCharge d p w ↔ ∃ t : ℝ, v = l • w + t • kernelVector d p := by
  have key : modelCharge d p v = l * modelCharge d p w ↔ modelCharge d p (v - l • w) = 0 := by
    rw [modelCharge_sub, modelCharge_smul, sub_eq_zero]
  rw [key, modelCharge_eq_zero_iff hd hp]
  constructor
  · intro h
    refine ⟨(v - l • w).r, ?_⟩
    ext <;> [have := congrArg MukaiVector.r h; have := congrArg MukaiVector.c h;
      have := congrArg MukaiVector.s h] <;> simp at this ⊢ <;> linarith
  · rintro ⟨t, rfl⟩
    ext <;> simp [kernelVector]

/-- **The wall line.** `Im(Z_p(v) · conj Z_p(w)) = 2da · ((c - rb)(dRt - S) - (C - Rb)(drt - s))`:
the charges of `v = (r, c, s)` and `w = (R, C, S)` are real-collinear exactly on this straight
line of the model. -/
theorem im_modelCharge_mul_conj (d : ℝ) {p : ℝ × ℝ} (hp : p.1 ^ 2 ≤ p.2) (v w : MukaiVector ℝ) :
    (modelCharge d p v * (starRingEnd ℂ) (modelCharge d p w)).im =
      2 * d * Real.sqrt (p.2 - p.1 ^ 2) *
        ((v.c - v.r * p.1) * (d * w.r * p.2 - w.s) -
          (w.c - w.r * p.1) * (d * v.r * p.2 - v.s)) := by
  rw [Complex.mul_im, Complex.conj_re, Complex.conj_im, im_modelCharge, im_modelCharge,
    re_modelCharge d hp, re_modelCharge d hp]
  ring

/-- The wall line is `-det(κ_p, v, w)`; it passes through the points of `v` and `w`. -/
theorem wallLine_eq_neg_det (d : ℝ) (p : ℝ × ℝ) (v w : MukaiVector ℝ) :
    (v.c - v.r * p.1) * (d * w.r * p.2 - w.s) - (w.c - w.r * p.1) * (d * v.r * p.2 - v.s) =
      -(1 * (v.c * w.s - v.s * w.c) - p.1 * (v.r * w.s - v.s * w.r) +
        d * p.2 * (v.r * w.c - v.c * w.r)) := by
  ring

/-! ### Sums of classes -/

lemma listSum_r {R : Type*} [CommRing R] (L : List (MukaiVector R)) :
    L.sum.r = (L.map MukaiVector.r).sum := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [ih]

lemma toReal_listSum (L : List (MukaiVector ℤ)) : L.sum.toReal = (L.map toReal).sum := by
  induction L with
  | nil => ext <;> simp
  | cons a L ih => rw [List.sum_cons, List.map_cons, List.sum_cons, ← ih]; ext <;> simp

lemma modelCharge_listSum (d : ℝ) (p : ℝ × ℝ) (L : List (MukaiVector ℝ)) :
    modelCharge d p L.sum = (L.map (modelCharge d p)).sum := by
  induction L with
  | nil => simp [modelCharge, charge, map]
  | cons a L ih => rw [List.sum_cons, modelCharge_add, ih, List.map_cons, List.sum_cons]

/-! ### Punctures -/

/-- The puncture `(c/r, s/(dr))` of an integral class of nonzero rank: the point of the model
where its central charge vanishes. -/
def puncture (d : ℤ) (δ : MukaiVector ℤ) : ℝ × ℝ := toModel d δ.toReal

lemma puncture_eq (d : ℤ) (δ : MukaiVector ℤ) :
    puncture d δ = ((δ.c : ℝ) / δ.r, (δ.s : ℝ) / (d * δ.r)) := rfl

variable {d : ℤ}

/-- The puncture of a root of nonzero rank lies at height `1/(dr²)` above the parabola. -/
lemma height_puncture (hd : 0 < d) {δ : MukaiVector ℤ} (hδ : IsRoot d δ) (hr : δ.r ≠ 0) :
    height (puncture d δ) = 1 / (d * (δ.r : ℝ) ^ 2) := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  exact height_toModel_of_isRoot hd' (isRoot_toReal.mpr hδ) (by simpa using hr)

lemma puncture_mem (hd : 0 < d) {δ : MukaiVector ℤ} (hδ : IsRoot d δ) (hr : δ.r ≠ 0) :
    (puncture d δ).1 ^ 2 < (puncture d δ).2 := by
  have h := height_puncture hd hδ hr
  have : (0 : ℝ) < 1 / (d * (δ.r : ℝ) ^ 2) := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    have : (δ.r : ℝ) ≠ 0 := by exact_mod_cast hr
    positivity
  rw [height] at h
  linarith

lemma kernelVector_puncture (hd : 0 < d) {δ : MukaiVector ℤ} (hr : δ.r ≠ 0) :
    δ.toReal = (δ.r : ℝ) • kernelVector (d : ℝ) (puncture d δ) := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have h := eq_smul_kernelVector_toModel hd' (v := δ.toReal) (by simpa using hr)
  rw [toReal_r] at h
  exact h

/-- The central charge of a root of nonzero rank vanishes exactly at its puncture. -/
theorem modelCharge_eq_zero_iff_eq_puncture (hd : 0 < d) {δ : MukaiVector ℤ} (hr : δ.r ≠ 0)
    {p : ℝ × ℝ} (hp : p.1 ^ 2 < p.2) :
    modelCharge d p δ.toReal = 0 ↔ p = puncture d δ := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [modelCharge_eq_zero_iff hd' hp]
  constructor
  · intro h
    have := congrArg (toModel (d : ℝ)) h
    rw [toModel_smul (by simpa using hr), toModel_kernelVector hd'] at this
    exact this.symm
  · rintro rfl
    simpa using kernelVector_puncture hd hr

/-! ### Visibility -/

/-- **Visibility of a puncture.** The closed straight segment from `p` to the puncture of the root
`δ` meets no puncture of another root of positive rank. -/
def SegmentClear (d : ℤ) (p : ℝ × ℝ) (δ : MukaiVector ℤ) : Prop :=
  ∀ δ' : MukaiVector ℤ, IsRoot d δ' → 0 < δ'.r → puncture d δ' ∈ segment ℝ p (puncture d δ) →
    δ' = δ

/-- **Visibility of the cusp at infinity.** The upward ray from `p`, the geodesic ray to the cusp
of the point class `(0, 0, 1)`, meets no puncture. -/
def RayClear (d : ℤ) (p : ℝ × ℝ) : Prop :=
  ∀ δ' : MukaiVector ℤ, IsRoot d δ' → 0 < δ'.r →
    ¬((puncture d δ').1 = p.1 ∧ p.2 ≤ (puncture d δ').2)

/-- **Visibility of a finite cusp.** The straight segment from `p` to the cusp `(m, m²)` on the
parabola meets no puncture. -/
def CuspClear (d : ℤ) (p : ℝ × ℝ) (m : ℝ) : Prop :=
  ∀ δ' : MukaiVector ℤ, IsRoot d δ' → 0 < δ'.r → puncture d δ' ∉ segment ℝ p (m, m ^ 2)

/-- The upward ray is clear exactly when no root of positive rank has its central charge on the
closed negative real axis: `RayClear` is the condition `Z(δ) ∉ ℝ_{≤0}` defining the region `V(X)`
in Theorem 2.2 of Bayer–Bridgeland (arXiv:1310.8266), the base of the geometric chamber. The
excluded points are the downward slits `{(c/r, t) : t ≤ s/(dr)}` under the punctures. -/
theorem rayClear_iff (hd : 0 < d) {p : ℝ × ℝ} (hp : p.1 ^ 2 < p.2) :
    RayClear d p ↔ ∀ δ' : MukaiVector ℤ, IsRoot d δ' → 0 < δ'.r →
      ∀ x : ℝ, x ≤ 0 → modelCharge d p δ'.toReal ≠ x := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have ha : 0 < Real.sqrt (p.2 - p.1 ^ 2) := Real.sqrt_pos.mpr (sub_pos.mpr hp)
  have key : ∀ δ' : MukaiVector ℤ, 0 < δ'.r →
      ((puncture d δ').1 = p.1 ∧ p.2 ≤ (puncture d δ').2 ↔
        ∃ x : ℝ, x ≤ 0 ∧ modelCharge d p δ'.toReal = x) := by
    intro δ' hr
    have hr' : (0 : ℝ) < δ'.r := by exact_mod_cast hr
    simp only [puncture_eq]
    constructor
    · rintro ⟨h1, h2⟩
      have hc : (δ'.c : ℝ) = δ'.r * p.1 := by rw [← h1]; field_simp
      refine ⟨(modelCharge d p δ'.toReal).re, ?_, ?_⟩
      · rw [re_modelCharge _ hp.le]
        simp only [toReal_r, toReal_c, toReal_s]
        rw [hc, sub_self, mul_zero, zero_add]
        rw [le_div_iff₀ (by positivity)] at h2
        nlinarith
      · apply Complex.ext
        · simp
        · rw [im_modelCharge]
          simp only [toReal_r, toReal_c, Complex.ofReal_im]
          rw [hc, sub_self, mul_zero]
    · rintro ⟨x, hx, h⟩
      have him := congrArg Complex.im h
      have hre := congrArg Complex.re h
      rw [im_modelCharge, Complex.ofReal_im] at him
      rw [re_modelCharge _ hp.le, Complex.ofReal_re] at hre
      simp only [toReal_r, toReal_c, toReal_s] at him hre
      have hc : (δ'.c : ℝ) = δ'.r * p.1 := by
        have : 2 * (d : ℝ) * Real.sqrt (p.2 - p.1 ^ 2) ≠ 0 := by positivity
        have := (mul_eq_zero.mp him).resolve_left this
        linarith
      refine ⟨by rw [hc, mul_div_cancel_left₀ _ hr'.ne'], ?_⟩
      rw [hc, sub_self, mul_zero, zero_add] at hre
      rw [le_div_iff₀ (by positivity)]
      nlinarith
  constructor
  · intro h δ' hδ' hr x hx hZ
    exact h δ' hδ' hr ((key δ' hr).mpr ⟨x, hx, hZ⟩)
  · intro h δ' hδ' hr hmem
    obtain ⟨x, hx, hZ⟩ := (key δ' hr).mp hmem
    exact h δ' hδ' hr x hx hZ

/-- **The cone form of a sight segment.** A root `δ'` of positive rank has its puncture on the
segment from `p` to the puncture of `δ` exactly when `δ' = l κ_p + m δ` with `l, m ≥ 0`. -/
theorem puncture_mem_segment_iff (hd : 0 < d) {δ δ' : MukaiVector ℤ} (hr : 0 < δ.r)
    (hr' : 0 < δ'.r) (p : ℝ × ℝ) :
    puncture d δ' ∈ segment ℝ p (puncture d δ) ↔
      ∃ l m : ℝ, 0 ≤ l ∧ 0 ≤ m ∧ δ'.toReal = l • kernelVector (d : ℝ) p + m • δ.toReal := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have h := toModel_mem_segment_iff hd' (u := δ'.toReal) (v := kernelVector (d : ℝ) p)
    (w := δ.toReal) (by simpa using hr') (by simp) (by simpa using hr)
  rwa [toModel_kernelVector hd'] at h

/-- The cone form of the upward ray: a root of positive rank has its puncture on the upward ray
from `p` exactly when `δ' = l κ_p + m (0, 0, 1)` with `l, m ≥ 0`. -/
theorem puncture_mem_ray_iff (hd : 0 < d) {δ' : MukaiVector ℤ} (hr' : 0 < δ'.r) (p : ℝ × ℝ) :
    ((puncture d δ').1 = p.1 ∧ p.2 ≤ (puncture d δ').2) ↔
      ∃ l m : ℝ, 0 ≤ l ∧ 0 ≤ m ∧ δ'.toReal = l • kernelVector (d : ℝ) p + m • point :=
  toModel_mem_ray_iff (by exact_mod_cast hd) (by simpa using hr') p

/-! ### The lattice arguments of the lemma -/

/-- A family of nonpositive reals summing to zero vanishes. -/
private lemma eq_zero_of_nonpos_of_sum_eq_zero {ι : Type*} (f : ι → ℝ) :
    ∀ L : List ι, (∀ x ∈ L, f x ≤ 0) → (L.map f).sum = 0 → ∀ x ∈ L, f x = 0 := by
  have hnp : ∀ L : List ι, (∀ x ∈ L, f x ≤ 0) → (L.map f).sum ≤ 0 := by
    intro L
    induction L with
    | nil => simp
    | cons a L ih =>
      intro h
      simp only [List.map_cons, List.sum_cons]
      have := h a (by simp)
      have := ih (fun x hx => h x (by simp [hx]))
      linarith
  intro L
  induction L with
  | nil => simp
  | cons a L ih =>
    intro h hs x hx
    simp only [List.map_cons, List.sum_cons] at hs
    have ha := h a (by simp)
    have hL := hnp L (fun y hy => h y (by simp [hy]))
    rcases List.mem_cons.mp hx with rfl | hx
    · linarith
    · exact ih (fun y hy => h y (by simp [hy])) (by linarith) x hx

/-- **The decomposition of a sum of roots with positively proportional charges.** If
`δ = Σ δ_i` and `Z_p(δ_i) = λ_i Z_p(δ) ≠ 0` with `λ_i` real, then
`δ_i = λ_i δ + t_i κ_p` with `t_i = r_i - λ_i r`, `Σ λ_i = 1` and `Σ t_i = 0`. -/
theorem decomposition_of_charge (hd : 0 < d) {p : ℝ × ℝ} (hp : p.1 ^ 2 < p.2)
    {δ : MukaiVector ℤ} (hZ : modelCharge d p δ.toReal ≠ 0) {L : List (MukaiVector ℤ)}
    (hsum : L.sum = δ) (lam : MukaiVector ℤ → ℝ)
    (hcharge : ∀ δ' ∈ L, modelCharge d p δ'.toReal = lam δ' * modelCharge d p δ.toReal) :
    (∀ δ' ∈ L, δ'.toReal =
      lam δ' • δ.toReal + ((δ'.r : ℝ) - lam δ' * δ.r) • kernelVector (d : ℝ) p) ∧
      (L.map lam).sum = 1 ∧ (L.map fun δ' => (δ'.r : ℝ) - lam δ' * δ.r).sum = 0 := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  -- the coefficients `λ_i` sum to one, by additivity of the central charge
  have hlam : (L.map lam).sum = 1 := by
    have h1 : modelCharge d p δ.toReal =
        (L.map fun δ' => modelCharge d p δ'.toReal).sum := by
      rw [← hsum, toReal_listSum, modelCharge_listSum, List.map_map]
      rfl
    rw [List.map_congr_left hcharge, List.sum_map_mul_right] at h1
    have h2 : ((L.map lam).sum : ℂ) = (L.map fun δ' => (lam δ' : ℂ)).sum := by
      rw [← Complex.ofRealHom_eq_coe, map_list_sum, List.map_map]
      rfl
    rw [← h2] at h1
    have : ((L.map lam).sum : ℂ) = 1 := by
      have := mul_right_cancel₀ hZ (h1.symm.trans (one_mul _).symm)
      exact this
    exact_mod_cast this
  refine ⟨?_, hlam, ?_⟩
  · intro δ' hδ'
    obtain ⟨t, ht⟩ := (modelCharge_eq_ofReal_mul_iff hd' hp _ _ _).mp (hcharge δ' hδ')
    have hrk := congrArg MukaiVector.r ht
    simp only [toReal_r, add_r, smul_r, kernelVector_r, mul_one] at hrk
    have ht' : t = (δ'.r : ℝ) - lam δ' * δ.r := by linarith
    rw [ht, ht']
  · -- the coefficients `t_i` sum to zero, by additivity of the rank
    have hr : (δ.r : ℝ) = (L.map fun δ' => (δ'.r : ℝ)).sum := by
      rw [← hsum, listSum_r, Int.cast_list_sum, List.map_map]
      rfl
    have : (L.map fun δ' => (δ'.r : ℝ) - lam δ' * δ.r).sum =
        (L.map fun δ' => (δ'.r : ℝ)).sum + (L.map fun δ' => -(lam δ' * δ.r)).sum := by
      rw [← List.sum_map_add]; rfl
    rw [this, ← hr]
    have : (L.map fun δ' => -(lam δ' * δ.r)).sum = -((L.map lam).sum * δ.r) := by
      rw [← List.sum_map_mul_right]
      have : (L.map fun δ' => -(lam δ' * (δ.r : ℝ))) =
          (L.map fun δ' => (-1 : ℝ) * (lam δ' * δ.r)) := by
        apply List.map_congr_left; intros; ring
      rw [this, List.sum_map_mul_left]; ring
    rw [this, hlam]
    ring

/-- **No first loss of stability along a clear segment** (the lattice argument in the proof of the
lemma "Visibility on the cover"). Let `δ` be a root of positive rank whose puncture is not `p`
and is seen from `p` along a clear segment. If the classes `δ_i = λ_i δ + t_i κ_p` of a family of
roots have `λ_i > 0`, `Σ λ_i = 1` and `Σ t_i = 0`, the family is the single root `δ`.

Indeed a positive `t_i` would give a root `δ_i` of positive rank whose puncture lies strictly
between `p` and the puncture of `δ`; so every `t_i ≤ 0`, hence every `t_i = 0`, and then
`δ_i = λ_i δ` is a root only for `λ_i = 1`. -/
theorem eq_singleton_of_decomposition (hd : 0 < d) {p : ℝ × ℝ} {δ : MukaiVector ℤ}
    (hδ : IsRoot d δ) (hr : 0 < δ.r) (hpδ : p ≠ puncture d δ)
    (hclear : SegmentClear d p δ) {L : List (MukaiVector ℤ)} (hroots : ∀ δ' ∈ L, IsRoot d δ')
    (lam t : MukaiVector ℤ → ℝ) (hlam : ∀ δ' ∈ L, 0 < lam δ')
    (hdec : ∀ δ' ∈ L, δ'.toReal = lam δ' • δ.toReal + t δ' • kernelVector (d : ℝ) p)
    (hsl : (L.map lam).sum = 1) (hst : (L.map t).sum = 0) :
    L = [δ] := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hr' : (0 : ℝ) < δ.r := by exact_mod_cast hr
  -- every `t_i ≤ 0`
  have hneg : ∀ δ' ∈ L, t δ' ≤ 0 := by
    intro δ' hδ'
    by_contra hpos
    push Not at hpos
    have hrk : (δ'.r : ℝ) = lam δ' * δ.r + t δ' := by
      have := congrArg MukaiVector.r (hdec δ' hδ')
      simpa using this
    have hr'' : 0 < δ'.r := by
      have : (0 : ℝ) < δ'.r := by rw [hrk]; nlinarith [hlam δ' hδ']
      exact_mod_cast this
    have hmem : puncture d δ' ∈ segment ℝ p (puncture d δ) :=
      (puncture_mem_segment_iff hd hr hr'' p).mpr
        ⟨t δ', lam δ', hpos.le, (hlam δ' hδ').le, by rw [hdec δ' hδ']; ext <;> simp <;> ring⟩
    have heq := hclear δ' (hroots δ' hδ') hr'' hmem
    subst heq
    -- `δ = λ δ + t κ` with `t > 0` puts `κ` on the line of `δ`
    apply hpδ
    have h1 : t δ' • kernelVector (d : ℝ) p = (1 - lam δ') • δ'.toReal := by
      have h := hdec δ' hδ'
      ext <;> [have := congrArg MukaiVector.r h; have := congrArg MukaiVector.c h;
        have := congrArg MukaiVector.s h] <;> simp at this ⊢ <;> linarith
    have hl1 : 1 - lam δ' ≠ 0 := by
      intro h0
      rw [h0] at h1
      have := congrArg MukaiVector.r h1
      simp at this
      exact hpos.ne' this
    have := congrArg (toModel (d : ℝ)) h1
    rw [toModel_smul hpos.ne', toModel_kernelVector hd', toModel_smul hl1] at this
    exact this
  -- hence every `t_i = 0`
  have hzero := eq_zero_of_nonpos_of_sum_eq_zero t L hneg hst
  -- so `δ_i = λ_i δ`, which is a root only for `λ_i = 1`
  have hone : ∀ δ' ∈ L, lam δ' = 1 ∧ δ' = δ := by
    intro δ' hδ'
    have h := hdec δ' hδ'
    rw [hzero δ' hδ'] at h
    have hsq := isRoot_toReal.mpr (hroots δ' hδ')
    unfold IsRoot at hsq
    have h2 : pairing (d : ℝ) δ'.toReal δ'.toReal =
        lam δ' ^ 2 * pairing (d : ℝ) δ.toReal δ.toReal := by
      have : δ'.toReal = lam δ' • δ.toReal := by rw [h]; ext <;> simp
      rw [this, pairing_smul_left, pairing_smul_right]; ring
    rw [hsq, isRoot_toReal.mpr hδ] at h2
    have hl : lam δ' = 1 := by nlinarith [hlam δ' hδ']
    refine ⟨hl, toReal_injective ?_⟩
    rw [h, hl]
    ext <;> simp
  -- and `Σ λ_i = 1` leaves a single term
  have hlen : L.length = 1 := by
    have : (L.map lam).sum = L.length := by
      rw [List.map_congr_left (fun δ' hδ' => (hone δ' hδ').1)]
      simp
    rw [hsl] at this
    exact_mod_cast this.symm
  exact List.eq_replicate_iff.mpr ⟨hlen, fun b hb => (hone b hb).2⟩

/-- **No first loss of stability along a clear segment**, in terms of central charges. If the
segment from `p` to the puncture of the root `δ` of positive rank is clear, `p` is not that
puncture, and `δ = Σ δ_i` is a sum of roots whose charges are positive multiples of `Z_p(δ)`
(as for the stable factors of a semistable sphere of class `δ`), then the sum is the single
term `δ`. -/
theorem eq_singleton_of_segmentClear (hd : 0 < d) {p : ℝ × ℝ} (hp : p.1 ^ 2 < p.2)
    {δ : MukaiVector ℤ} (hδ : IsRoot d δ) (hr : 0 < δ.r) (hpδ : p ≠ puncture d δ)
    (hclear : SegmentClear d p δ) {L : List (MukaiVector ℤ)} (hroots : ∀ δ' ∈ L, IsRoot d δ')
    (hsum : L.sum = δ)
    (hcharge : ∀ δ' ∈ L, ∃ l : ℝ, 0 < l ∧
      modelCharge d p δ'.toReal = l * modelCharge d p δ.toReal) :
    L = [δ] := by
  have hZ : modelCharge d p δ.toReal ≠ 0 := by
    rw [Ne, modelCharge_eq_zero_iff_eq_puncture hd hr.ne' hp]; exact hpδ
  choose! lam hlam hZl using hcharge
  obtain ⟨hdec, hsl, hst⟩ := decomposition_of_charge hd hp hZ hsum lam hZl
  exact eq_singleton_of_decomposition hd hδ hr hpδ hclear hroots lam _ hlam hdec hsl hst

/-- **An obstacle on the way to `δ`.** If the puncture of a root `δ'` of positive rank lies on the
segment from `p` to the puncture of `δ`, and `p` is not the puncture of `δ'`, then
`Z_p(δ') = μ Z_p(δ)` with `μ > 0`. So stable spheres of these classes have phases differing by an
even integer; their pairing is negative (`MukaiVector.pairing_le_neg_three`), which contradicts
`Hom` vanishing between stable objects of one phase. -/
theorem obstacle_charge_pos_mul (hd : 0 < d) {p : ℝ × ℝ} (hp : p.1 ^ 2 < p.2)
    {δ δ' : MukaiVector ℤ} (hr : 0 < δ.r) (hr' : 0 < δ'.r)
    (hmem : puncture d δ' ∈ segment ℝ p (puncture d δ)) (hp' : p ≠ puncture d δ') :
    ∃ μ : ℝ, 0 < μ ∧ modelCharge d p δ'.toReal = μ * modelCharge d p δ.toReal := by
  obtain ⟨l, m, hl, hm, h⟩ := (puncture_mem_segment_iff hd hr hr' p).mp hmem
  have hZ : modelCharge d p δ'.toReal = m * modelCharge d p δ.toReal := by
    rw [h, modelCharge_add, modelCharge_smul, modelCharge_smul, modelCharge_kernelVector _ hp.le,
      mul_zero, zero_add]
  refine ⟨m, hm.lt_of_ne ?_, hZ⟩
  rintro rfl
  apply hp'
  rw [← modelCharge_eq_zero_iff_eq_puncture hd hr'.ne' hp, hZ, Complex.ofReal_zero, zero_mul]

/-! ### The finite search -/

/-- The height of the puncture of an obstacle is at least the smaller height of the two ends. -/
theorem height_obstacle_ge {p : ℝ × ℝ} {δ δ' : MukaiVector ℤ}
    (hmem : puncture d δ' ∈ segment ℝ p (puncture d δ)) :
    min (height p) (height (puncture d δ)) ≤ height (puncture d δ') :=
  min_height_le_of_mem_segment hmem

/-- **The rank bound of the finite search.** A root `δ'` of nonzero rank whose puncture lies on the
segment from a point `p` of height `h > 0` to the puncture of a root of rank `r` has
`r'² ≤ max(r², 1/(dh))`: by concavity of the height its puncture is at height
`1/(dr'²) ≥ min(h, 1/(dr²))`. -/
theorem obstacle_rank_sq_le (hd : 0 < d) {p : ℝ × ℝ} (hp : 0 < height p) {δ δ' : MukaiVector ℤ}
    (hδ : IsRoot d δ) (hr : δ.r ≠ 0) (hδ' : IsRoot d δ') (hr' : δ'.r ≠ 0)
    (hmem : puncture d δ' ∈ segment ℝ p (puncture d δ)) :
    (δ'.r : ℝ) ^ 2 ≤ max ((δ.r : ℝ) ^ 2) (1 / (d * height p)) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hr1 : (0 : ℝ) < (δ.r : ℝ) ^ 2 := by positivity
  have hr2 : (0 : ℝ) < (δ'.r : ℝ) ^ 2 := by positivity
  have h := height_obstacle_ge hmem
  rw [height_puncture hd hδ' hr', height_puncture hd hδ hr] at h
  rcases min_choice (height p) (1 / (d * (δ.r : ℝ) ^ 2)) with hmin | hmin
  · rw [hmin] at h
    apply le_max_of_le_right
    rw [le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ (by positivity)] at h
    nlinarith
  · rw [hmin] at h
    apply le_max_of_le_left
    rw [div_le_div_iff₀ (by positivity) (by positivity)] at h
    nlinarith

/-- **The abscissa bound of the finite search.** The abscissa `c'/r'` of an obstacle lies between
those of the two ends, so `|c'| ≤ r' max(|b|, |c/r|)`. -/
theorem obstacle_abs_c_le {p : ℝ × ℝ} {δ δ' : MukaiVector ℤ} (hr' : 0 < δ'.r)
    (hmem : puncture d δ' ∈ segment ℝ p (puncture d δ)) :
    |(δ'.c : ℝ)| ≤ δ'.r * max |p.1| |(puncture d δ).1| := by
  have hr'' : (0 : ℝ) < δ'.r := by exact_mod_cast hr'
  obtain ⟨a, b, ha, hb, hab, h⟩ := hmem
  have h1 := congrArg Prod.fst h
  simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul] at h1
  have hx : |(puncture d δ').1| ≤ max |p.1| |(puncture d δ).1| := by
    rw [← h1]
    calc |a * p.1 + b * (puncture d δ).1| ≤ a * |p.1| + b * |(puncture d δ).1| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * max |p.1| |(puncture d δ).1| + b * max |p.1| |(puncture d δ).1| := by
          gcongr
          · exact le_max_left _ _
          · exact le_max_right _ _
      _ = max |p.1| |(puncture d δ).1| := by rw [← add_mul, hab, one_mul]
  have : (puncture d δ').1 = (δ'.c : ℝ) / δ'.r := rfl
  rw [this, abs_div, abs_of_pos hr'', div_le_iff₀ hr''] at hx
  linarith

/-- On roots of positive rank, `δ ↦ (r, c)` is injective: `s = (dc² + 1)/r`. -/
lemma injOn_rank_c (d : ℤ) :
    Set.InjOn (fun δ : MukaiVector ℤ => (δ.r, δ.c)) {δ | IsRoot d δ ∧ 0 < δ.r} := by
  rintro δ ⟨hδ, hr⟩ δ' ⟨hδ', -⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  rw [isRoot_iff] at hδ hδ'
  refine MukaiVector.ext h1 h2 ?_
  rw [← h1, ← h2] at hδ'
  exact mul_left_cancel₀ hr.ne' (hδ.trans hδ'.symm)

/-- **The finite search.** Only finitely many roots of positive rank have their puncture on the
segment from a point `p` above the parabola to the puncture of a root. -/
theorem finite_obstacles (hd : 0 < d) {p : ℝ × ℝ} (hp : 0 < height p) {δ : MukaiVector ℤ}
    (hδ : IsRoot d δ) (hr : δ.r ≠ 0) :
    {δ' : MukaiVector ℤ | IsRoot d δ' ∧ 0 < δ'.r ∧
      puncture d δ' ∈ segment ℝ p (puncture d δ)}.Finite := by
  set M := max ((δ.r : ℝ) ^ 2) (1 / (d * height p))
  set B := max |p.1| |(puncture d δ).1|
  set R : ℤ := ⌈M⌉
  set C : ℤ := ⌈R * B⌉
  have hsub : {δ' : MukaiVector ℤ | IsRoot d δ' ∧ 0 < δ'.r ∧
      puncture d δ' ∈ segment ℝ p (puncture d δ)} ⊆ {δ' | IsRoot d δ' ∧ 0 < δ'.r} :=
    fun δ' h => ⟨h.1, h.2.1⟩
  have hinj := (injOn_rank_c d).mono hsub
  apply Set.Finite.of_finite_image _ hinj
  apply ((Set.finite_Icc (1 : ℤ) R).prod (Set.finite_Icc (-C) C)).subset
  rintro _ ⟨δ', ⟨hδ', hr', hmem⟩, rfl⟩
  have hrr : (1 : ℝ) ≤ δ'.r := by exact_mod_cast hr'
  have hrank : (δ'.r : ℝ) ≤ M := by
    have := obstacle_rank_sq_le hd hp hδ hr hδ' hr'.ne' hmem
    nlinarith
  have hR : δ'.r ≤ R := by
    have : (δ'.r : ℝ) ≤ R := hrank.trans (Int.le_ceil M)
    exact_mod_cast this
  have hc := obstacle_abs_c_le hr' hmem
  have hB : 0 ≤ B := le_max_of_le_left (abs_nonneg _)
  have hC : |(δ'.c : ℝ)| ≤ C := by
    refine hc.trans ((mul_le_mul_of_nonneg_right ?_ hB).trans (Int.le_ceil _))
    exact_mod_cast hR
  rw [abs_le] at hC
  refine ⟨⟨hr', hR⟩, ?_, ?_⟩
  · have : (-C : ℝ) ≤ δ'.c := by linarith
    exact_mod_cast this
  · exact_mod_cast hC.2

/-- **The first obstacle.** If the segment from `p` to the puncture of the root `δ` is obstructed
some obstacle `δ'` is seen from `p` along a clear segment: the obstacle nearest to `p`, which
exists because there are finitely many (`finite_obstacles`). -/
theorem exists_first_obstacle (hd : 0 < d) {p : ℝ × ℝ} (hp : p.1 ^ 2 < p.2)
    {δ : MukaiVector ℤ} (hδ : IsRoot d δ) (hr : 0 < δ.r) (h : ¬SegmentClear d p δ) :
    ∃ δ', IsRoot d δ' ∧ 0 < δ'.r ∧ δ' ≠ δ ∧ puncture d δ' ∈ segment ℝ p (puncture d δ) ∧
      SegmentClear d p δ' := by
  have hpos : 0 < height p := by rw [height]; linarith
  set S := {δ' : MukaiVector ℤ | IsRoot d δ' ∧ 0 < δ'.r ∧ δ' ≠ δ ∧
    puncture d δ' ∈ segment ℝ p (puncture d δ)}
  have hS : S.Finite := (finite_obstacles hd hpos hδ hr.ne').subset
    fun δ' h => ⟨h.1, h.2.1, h.2.2.2⟩
  have hne : S.Nonempty := by
    unfold SegmentClear at h
    push Not at h
    obtain ⟨δ', h1, h2, h3, h4⟩ := h
    exact ⟨δ', h1, h2, h4, h3⟩
  obtain ⟨δ₀, ⟨h0, hr0, hne0, hmem0⟩, hmin⟩ :=
    Set.exists_min_image S (fun δ' => dist p (puncture d δ')) hS hne
  refine ⟨δ₀, h0, hr0, hne0, hmem0, ?_⟩
  intro δ'' h'' hr'' hmem''
  by_contra hne''
  -- `δ''` lies on the segment to `δ₀`, which lies on the segment to `δ`
  have hsub : segment ℝ p (puncture d δ₀) ⊆ segment ℝ p (puncture d δ) :=
    (convex_segment p (puncture d δ)).segment_subset (left_mem_segment ℝ _ _) hmem0
  have hd1 := dist_add_dist_of_mem_segment hmem''
  have hd2 := dist_add_dist_of_mem_segment hmem0
  have hne''δ : δ'' ≠ δ := by
    rintro rfl
    -- then the punctures of `δ` and `δ₀` lie on each other's segments from `p`, so coincide
    have hd3 : dist (puncture d δ'') (puncture d δ₀) = 0 := by
      nlinarith [dist_nonneg (x := puncture d δ'') (y := puncture d δ₀),
        dist_nonneg (x := puncture d δ₀) (y := puncture d δ''), dist_comm (puncture d δ₀)
          (puncture d δ'')]
    exact hne0 (eq_of_toModel_eq hd h0 h'' hr0 hr'' (dist_eq_zero.mp hd3).symm)
  have hle := hmin δ'' ⟨h'', hr'', hne''δ, hsub hmem''⟩
  have hd3 : dist (puncture d δ'') (puncture d δ₀) = 0 := by
    linarith [dist_nonneg (x := puncture d δ'') (y := puncture d δ₀)]
  exact hne'' (eq_of_toModel_eq hd h'' h0 hr'' hr0 (dist_eq_zero.mp hd3))

/-! ### Sight lines to cusps, and clear-sight criteria -/

/-- **The rank bound for the upward ray.** A root of nonzero rank whose puncture lies on the upward
ray from `p` has `d r'² h ≤ 1`, where `h` is the height of `p`: the height only grows along the
ray. -/
theorem ray_obstacle_rank_sq_le (hd : 0 < d) {p : ℝ × ℝ} {δ' : MukaiVector ℤ}
    (hδ' : IsRoot d δ') (hr' : δ'.r ≠ 0)
    (hmem : (puncture d δ').1 = p.1 ∧ p.2 ≤ (puncture d δ').2) :
    d * (δ'.r : ℝ) ^ 2 * height p ≤ 1 := by
  have hge : height p ≤ height (puncture d δ') := by
    simp only [height]; rw [hmem.1]; linarith [hmem.2]
  rw [height_puncture hd hδ' hr'] at hge
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have : (0 : ℝ) < d * (δ'.r : ℝ) ^ 2 := by
    have : (δ'.r : ℝ) ≠ 0 := by exact_mod_cast hr'
    positivity
  rw [le_div_iff₀ this] at hge
  linarith

/-- **The geometric region.** If `d h > 1` for the height `h` of `p`, that is `a > 1/√d` at
`z = b + ia`, the upward ray from `p` is clear: every puncture has height `1/(dr²) ≤ 1/d`. -/
theorem rayClear_of_one_lt (hd : 0 < d) {p : ℝ × ℝ} (h : 1 < d * height p) : RayClear d p := by
  intro δ' hδ' hr' hmem
  have hb := ray_obstacle_rank_sq_le hd hδ' hr'.ne' hmem
  have hr1 : (1 : ℝ) ≤ (δ'.r : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ δ'.r := by exact_mod_cast hr'
    nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hr1) (le_of_lt (lt_trans one_pos h))]

/-- **A clear segment to a sphere of rank one.** If `d h > 1` for the height `h` of `p`, the
segment from `p` to the puncture of a root of rank one is clear: by concavity its height exceeds
`1/d` everywhere except at the puncture, while every puncture has height `1/(dr²) ≤ 1/d`. -/
theorem segmentClear_of_one_lt (hd : 0 < d) {p : ℝ × ℝ} {δ : MukaiVector ℤ} (hδ : IsRoot d δ)
    (hr : δ.r = 1) (h : 1 < d * height p) : SegmentClear d p δ := by
  intro δ' hδ' hr' hmem
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [segment_eq_image] at hmem
  obtain ⟨θ, ⟨h0, h1⟩, hx⟩ := hmem
  rcases h1.lt_or_eq with h1 | rfl
  · exfalso
    have hx' := congrArg height hx
    rw [height_segment, height_puncture hd hδ (by omega), height_puncture hd hδ' hr'.ne', hr]
      at hx'
    have hr1 : (1 : ℝ) ≤ (δ'.r : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ δ'.r := by exact_mod_cast hr'
      nlinarith
    have hle : 1 / (d * (δ'.r : ℝ) ^ 2) ≤ 1 / d := by
      apply one_div_le_one_div_of_le hd'; nlinarith
    have hgt : 1 / (d : ℝ) < height p := by rw [div_lt_iff₀ hd']; linarith
    have hsq : 0 ≤ θ * (1 - θ) * (p.1 - (puncture d δ).1) ^ 2 := by
      have : 0 ≤ 1 - θ := by linarith
      positivity
    have h1θ : 0 < 1 - θ := by linarith
    have : (1 - θ) * (1 / (d : ℝ)) < (1 - θ) * height p := mul_lt_mul_of_pos_left hgt h1θ
    simp only [Int.cast_one, one_pow, mul_one] at hx'
    nlinarith
  · simp only [sub_self, zero_smul, one_smul, zero_add] at hx
    exact eq_of_toModel_eq hd hδ' hδ hr' (by omega) hx.symm

/-- **The rank bound for a sight segment to a finite cusp.** Let `m = c₀/e` with `e > 0`, and let
`p` have abscissa `b ≠ m` and height `h`. A root of positive rank whose puncture lies on the
segment from `p` to the cusp `(m, m²)` has `d r' h ≤ e |b - m|`. Indeed along the segment the
height is at least `h |x - m|/|b - m|` by concavity, it equals `1/(dr'²)` at the puncture, and
`|c'/r' - m| ≥ 1/(er')` there. -/
theorem cusp_obstacle_rank_le (hd : 0 < d) {p : ℝ × ℝ} {c₀ e : ℤ}
    (he : 0 < e) (hb : p.1 ≠ c₀ / e) {δ' : MukaiVector ℤ} (hδ' : IsRoot d δ') (hr' : 0 < δ'.r)
    (hmem : puncture d δ' ∈ segment ℝ p ((c₀ / e : ℝ), (c₀ / e : ℝ) ^ 2)) :
    d * δ'.r * height p ≤ e * |p.1 - c₀ / e| := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have hr'' : (0 : ℝ) < δ'.r := by exact_mod_cast hr'
  set m : ℝ := c₀ / e with hm
  rw [segment_eq_image] at hmem
  obtain ⟨θ, ⟨h0, h1⟩, hx⟩ := hmem
  have hheight := congrArg height hx
  rw [height_segment, height_puncture hd hδ' hr'.ne'] at hheight
  have hm0 : height (m, m ^ 2) = 0 := by simp [height]
  rw [hm0, mul_zero, add_zero] at hheight
  have hpos : (0 : ℝ) < 1 / (d * (δ'.r : ℝ) ^ 2) := by positivity
  -- the obstacle is not the cusp, so `θ < 1`
  have h1θ : 0 < 1 - θ := by
    rcases h1.lt_or_eq with h1 | rfl
    · linarith
    · exfalso
      simp at hheight
      rcases hheight with h | h <;> omega
  -- its height: `1/(dr'²) ≥ (1 - θ) h`
  have hA : (1 - θ) * height p ≤ 1 / (d * (δ'.r : ℝ) ^ 2) := by
    rw [← hheight]
    have : 0 ≤ θ * (1 - θ) * (p.1 - m) ^ 2 := by positivity
    nlinarith
  -- its abscissa: `c'/r' - m = (1 - θ)(b - m)`, and `|c'/r' - m| ≥ 1/(er')`
  have hx1 := congrArg Prod.fst hx
  simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul] at hx1
  have hdiff : (puncture d δ').1 - m = (1 - θ) * (p.1 - m) := by rw [← hx1]; ring
  have hD : 0 < |p.1 - m| := abs_pos.mpr (sub_ne_zero.mpr hb)
  have hB : 1 / (e * δ'.r : ℝ) ≤ (1 - θ) * |p.1 - m| := by
    have hne : (puncture d δ').1 - m ≠ 0 := by
      rw [hdiff]; exact mul_ne_zero h1θ.ne' (sub_ne_zero.mpr hb)
    have hfrac : (puncture d δ').1 - m = ((δ'.c * e - c₀ * δ'.r : ℤ) : ℝ) / (e * δ'.r) := by
      simp only [puncture_eq, hm]
      push_cast
      field_simp
    rw [hfrac] at hne
    have hn : (δ'.c * e - c₀ * δ'.r : ℤ) ≠ 0 := by
      intro h0; apply hne; rw [h0]; simp
    have hn1 : (1 : ℝ) ≤ |((δ'.c * e - c₀ * δ'.r : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hn
    calc 1 / (e * δ'.r : ℝ) ≤ |((δ'.c * e - c₀ * δ'.r : ℤ) : ℝ)| / (e * δ'.r) := by
          gcongr
      _ = |(puncture d δ').1 - m| := by
          rw [hfrac, abs_div, abs_of_pos (by positivity : (0 : ℝ) < e * δ'.r)]
      _ = (1 - θ) * |p.1 - m| := by rw [hdiff, abs_mul, abs_of_pos h1θ]
  -- combine: `(1 - θ) h d r'² ≤ 1 ≤ (1 - θ) |b - m| e r'`
  have hA' : (1 - θ) * height p * (d * (δ'.r : ℝ) ^ 2) ≤ 1 := by
    rwa [le_div_iff₀ (by positivity)] at hA
  have hB' : 1 ≤ (1 - θ) * |p.1 - m| * (e * δ'.r) := by
    rwa [div_le_iff₀ (by positivity)] at hB
  have key : (1 - θ) * δ'.r * (d * δ'.r * height p) ≤ (1 - θ) * δ'.r * (e * |p.1 - m|) := by
    nlinarith
  exact le_of_mul_le_mul_left key (by positivity)

/-- **A clear segment to a finite cusp.** Let `m = c₀/e` with `e > 0`, and let `p` have abscissa
`b ≠ m` and height `h`. If `e |b - m| < d h`, the segment from `p` to the cusp `(m, m²)` is clear.
This generalizes `opening_segment_clear`; see `opening_cuspClear`. -/
theorem cuspClear_of_lt (hd : 0 < d) {p : ℝ × ℝ} (hp : 0 < height p) {c₀ e : ℤ} (he : 0 < e)
    (hb : p.1 ≠ c₀ / e) (h : e * |p.1 - c₀ / e| < d * height p) : CuspClear d p (c₀ / e) := by
  intro δ' hδ' hr' hmem
  have hbound := cusp_obstacle_rank_le hd he hb hδ' hr' hmem
  have hr1 : (1 : ℝ) ≤ δ'.r := by exact_mod_cast hr'
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  nlinarith [mul_le_mul_of_nonneg_right hr1 (le_of_lt (mul_pos hd' hp))]

/-- The rank and the first Chern class of a root are coprime: `rs - dc² = 1`. -/
lemma isCoprime_r_c {δ : MukaiVector ℤ} (hδ : IsRoot d δ) : IsCoprime δ.r δ.c := by
  rw [isRoot_iff] at hδ
  exact ⟨δ.s, -(d * δ.c), by linear_combination hδ⟩

/-- **A vertical sight line.** On the vertical through a cusp `c₀/e` in lowest terms, a root of
positive rank has rank `e`: its slope `c/r` is already in lowest terms. -/
theorem rank_eq_of_slope_eq {δ : MukaiVector ℤ} (hδ : IsRoot d δ) (hr : 0 < δ.r) {c₀ e : ℤ}
    (he : 0 < e) (hce : IsCoprime c₀ e) (h : δ.c * e = c₀ * δ.r) : δ.r = e := by
  have h1 : δ.r ∣ e := (isCoprime_r_c hδ).dvd_of_dvd_mul_left ⟨c₀, by linear_combination h⟩
  have h2 : e ∣ δ.r := hce.symm.dvd_of_dvd_mul_left ⟨δ.c, by linear_combination -h⟩
  exact Int.dvd_antisymm hr.le he.le h1 h2

/-! ### Examples -/

/-- `v(𝒪_X) = (1, 0, 1)` is a root at `d = 1`. -/
lemma isRoot_structureSheaf : IsRoot (1 : ℤ) ⟨1, 0, 1⟩ := by
  simp [IsRoot, pairing]

/-- `v(𝒪_X(H)) = (1, 1, 2)` is a root at `d = 1`. -/
lemma isRoot_lineBundle_one : IsRoot (1 : ℤ) ⟨1, 1, 2⟩ := by
  simp [IsRoot, pairing]

/-- **The opening example: the cusp of `T⁻¹𝒪_x`.** At `d = 1` and the point `b + 4i/3`, that is
`(b, b² + 16/9)`, with `0 < b ≤ 1/3`, the segment to the cusp `0` of `T⁻¹𝒪_x` is clear: its height
`16/9` beats `e|b - 0| = b`. -/
theorem opening_cuspClear {b : ℝ} (hb0 : 0 < b) (hb : b ≤ 1 / 3) :
    CuspClear 1 (b, b ^ 2 + 16 / 9) 0 := by
  have h := cuspClear_of_lt (d := 1) (p := (b, b ^ 2 + 16 / 9)) (c₀ := 0) (e := 1) one_pos
    (by simp [height]) one_pos (by simp; exact hb0.ne')
    (by simp [height, abs_of_pos hb0]; linarith)
  simpa using h

/-- In the opening example the base point is geometric (`16/9 > 1`), and the structure sheaf is
visible: the segment to its puncture `(0, 1)` has height above one except at the puncture. -/
theorem opening_rayClear_segmentClear (b : ℝ) :
    RayClear 1 (b, b ^ 2 + 16 / 9) ∧ SegmentClear 1 (b, b ^ 2 + 16 / 9) ⟨1, 0, 1⟩ := by
  have h : (1 : ℝ) < ((1 : ℤ) : ℝ) * height (b, b ^ 2 + 16 / 9) := by
    simp [height]; norm_num
  exact ⟨rayClear_of_one_lt one_pos h, segmentClear_of_one_lt one_pos isRoot_structureSheaf rfl h⟩

/-- **The rigid wall example.** At `d = 1` the punctures `(0, 1)` of `𝒪_X` and `(1, 2)` of
`𝒪_X(H)` are visible from the geometric point `(1/2, 3/2)`, whose height is `5/4 > 1`. -/
theorem rigid_segmentClear :
    RayClear 1 (1 / 2, 3 / 2) ∧ SegmentClear 1 (1 / 2, 3 / 2) ⟨1, 0, 1⟩ ∧
      SegmentClear 1 (1 / 2, 3 / 2) ⟨1, 1, 2⟩ := by
  have h : (1 : ℝ) < ((1 : ℤ) : ℝ) * height (1 / 2, 3 / 2) := by simp [height]; norm_num
  exact ⟨rayClear_of_one_lt one_pos h, segmentClear_of_one_lt one_pos isRoot_structureSheaf rfl h,
    segmentClear_of_one_lt one_pos isRoot_lineBundle_one rfl h⟩

/-! ### A decision procedure for rational points -/

/-- A point `x` of the plane lies on the segment from `p` to `q` exactly when it is on their line
and in their bounding box. -/
theorem mem_segment_iff_collinear (p q x : ℝ × ℝ) :
    x ∈ segment ℝ p q ↔ (q.1 - p.1) * (x.2 - p.2) = (q.2 - p.2) * (x.1 - p.1) ∧
      min p.1 q.1 ≤ x.1 ∧ x.1 ≤ max p.1 q.1 ∧ min p.2 q.2 ≤ x.2 ∧ x.2 ≤ max p.2 q.2 := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  obtain ⟨x1, x2⟩ := x
  simp only
  constructor
  · rintro ⟨a, b, ha, hb, hab, h⟩
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have ha' : a = 1 - b := by linarith
    subst ha'
    refine ⟨by ring, ?_, ?_, ?_, ?_⟩
    · nlinarith [min_le_left p1 q1, min_le_right p1 q1]
    · nlinarith [le_max_left p1 q1, le_max_right p1 q1]
    · nlinarith [min_le_left p2 q2, min_le_right p2 q2]
    · nlinarith [le_max_left p2 q2, le_max_right p2 q2]
  · rintro ⟨hcol, h1, h2, h3, h4⟩
    rw [segment_eq_image]
    -- the parameter `θ` along a coordinate in which `p` and `q` differ
    have key : ∀ (u v w : ℝ), u ≠ v → min u v ≤ w → w ≤ max u v →
        0 ≤ (w - u) / (v - u) ∧ (w - u) / (v - u) ≤ 1 := by
      intro u v w huv hmin hmax
      rcases lt_or_gt_of_ne huv with h | h
      · rw [min_eq_left h.le] at hmin
        rw [max_eq_right h.le] at hmax
        exact ⟨div_nonneg (by linarith) (by linarith),
          (div_le_one (by linarith)).mpr (by linarith)⟩
      · rw [min_eq_right h.le] at hmin
        rw [max_eq_left h.le] at hmax
        exact ⟨div_nonneg_of_nonpos (by linarith) (by linarith),
          (div_le_one_of_neg (by linarith)).mpr (by linarith)⟩
    by_cases hx : p1 = q1
    · subst hx
      rw [min_self] at h1
      rw [max_self] at h2
      have hx1 : x1 = p1 := le_antisymm h2 h1
      subst hx1
      by_cases hy : p2 = q2
      · subst hy
        rw [min_self] at h3
        rw [max_self] at h4
        have : x2 = p2 := le_antisymm h4 h3
        subst this
        exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simp⟩
      · have hy' : q2 - p2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
        refine ⟨(x2 - p2) / (q2 - p2), key p2 q2 x2 hy h3 h4, ?_⟩
        have hθ : (x2 - p2) / (q2 - p2) * (q2 - p2) = x2 - p2 := div_mul_cancel₀ _ hy'
        simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, Prod.mk.injEq]
        exact ⟨by ring, by linear_combination hθ⟩
    · have hx' : q1 - p1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
      refine ⟨(x1 - p1) / (q1 - p1), key p1 q1 x1 hx h1 h2, ?_⟩
      set θ := (x1 - p1) / (q1 - p1)
      have hθ1 : θ * (q1 - p1) = x1 - p1 := div_mul_cancel₀ _ hx'
      have hθ2 : θ * (q2 - p2) = x2 - p2 := by
        have : (q1 - p1) * (θ * (q2 - p2)) = (q1 - p1) * (x2 - p2) := by
          linear_combination (q2 - p2) * hθ1 - hcol
        exact mul_left_cancel₀ hx' this
      simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, Prod.mk.injEq]
      exact ⟨by linear_combination hθ1, by linear_combination hθ2⟩

/-- A rational point of the plane, as a real one. -/
def castPoint (p : ℚ × ℚ) : ℝ × ℝ := ((p.1 : ℝ), (p.2 : ℝ))

/-- The rational segment test: `x` is on the line of `p` and `q` and in their bounding box. -/
def OnSegment (p q x : ℚ × ℚ) : Prop :=
  (q.1 - p.1) * (x.2 - p.2) = (q.2 - p.2) * (x.1 - p.1) ∧
    min p.1 q.1 ≤ x.1 ∧ x.1 ≤ max p.1 q.1 ∧ min p.2 q.2 ≤ x.2 ∧ x.2 ≤ max p.2 q.2

instance (p q x : ℚ × ℚ) : Decidable (OnSegment p q x) := by
  unfold OnSegment; infer_instance

lemma castPoint_mem_segment_iff (p q x : ℚ × ℚ) :
    castPoint x ∈ segment ℝ (castPoint p) (castPoint q) ↔ OnSegment p q x := by
  rw [mem_segment_iff_collinear, OnSegment]
  simp only [castPoint]
  norm_cast

/-- The puncture of an integral class, as a rational point. -/
def punctureRat (d : ℤ) (δ : MukaiVector ℤ) : ℚ × ℚ := ((δ.c : ℚ) / δ.r, (δ.s : ℚ) / (d * δ.r))

lemma puncture_eq_castPoint (d : ℤ) (δ : MukaiVector ℤ) :
    puncture d δ = castPoint (punctureRat d δ) := by
  simp [puncture_eq, castPoint, punctureRat]

/-- The candidates of the finite search: the roots `(r, c, (dc² + 1)/r)` with `1 ≤ r ≤ R`,
`|c| ≤ C` and `r ∣ dc² + 1`. -/
def rootCandidates (d : ℤ) (R C : ℕ) : List (MukaiVector ℤ) :=
  (List.range R).flatMap fun i : ℕ => (List.range (2 * C + 1)).filterMap fun j : ℕ =>
    if (d * ((j : ℤ) - C) ^ 2 + 1) % ((i : ℤ) + 1) = 0 then
      some ⟨(i : ℤ) + 1, (j : ℤ) - C, (d * ((j : ℤ) - C) ^ 2 + 1) / ((i : ℤ) + 1)⟩
    else none

lemma isRoot_of_mem_rootCandidates {R C : ℕ} {δ : MukaiVector ℤ}
    (h : δ ∈ rootCandidates d R C) : IsRoot d δ ∧ 0 < δ.r := by
  simp only [rootCandidates, List.mem_flatMap, List.mem_range, List.mem_filterMap,
    Option.ite_none_right_eq_some, Option.some.injEq] at h
  obtain ⟨i, -, j, -, hdvd, rfl⟩ := h
  refine ⟨?_, show (0 : ℤ) < (i : ℤ) + 1 by omega⟩
  rw [isRoot_iff]
  simp only
  rw [Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hdvd)]

lemma mem_rootCandidates {R C : ℕ} {δ : MukaiVector ℤ} (hδ : IsRoot d δ) (hr : 0 < δ.r)
    (hR : δ.r ≤ R) (hC : |δ.c| ≤ C) : δ ∈ rootCandidates d R C := by
  rw [isRoot_iff] at hδ
  rw [abs_le] at hC
  simp only [rootCandidates, List.mem_flatMap, List.mem_range, List.mem_filterMap,
    Option.ite_none_right_eq_some, Option.some.injEq]
  refine ⟨(δ.r - 1).toNat, by omega, (δ.c + C).toNat, by omega, ?_, ?_⟩
  · have h1 : ((δ.r - 1).toNat : ℤ) + 1 = δ.r := by omega
    have h2 : ((δ.c + C).toNat : ℤ) - C = δ.c := by omega
    rw [h1, h2, ← hδ]
    exact Int.mul_emod_right _ _
  · have h1 : ((δ.r - 1).toNat : ℤ) + 1 = δ.r := by omega
    have h2 : ((δ.c + C).toNat : ℤ) - C = δ.c := by omega
    ext
    · exact h1
    · exact h2
    · simp only
      rw [h1, h2, ← hδ, Int.mul_ediv_cancel_left _ hr.ne']

/-- **The finite search, as a Boolean check.** Every candidate root other than `δ` has its
puncture off the segment from `p` to the puncture of `δ`. -/
def segmentClearCheck (d : ℤ) (p : ℚ × ℚ) (δ : MukaiVector ℤ) (R C : ℕ) : Bool :=
  (rootCandidates d R C).all fun δ' =>
    (δ'.r == δ.r && δ'.c == δ.c && δ'.s == δ.s) ||
      !decide (OnSegment p (punctureRat d δ) (punctureRat d δ'))

/-- **The decision procedure is correct.** For a rational point `p` above the parabola and bounds
`R ≥ max(r², 1/(dh))` and `C ≥ R max(|b|, |c/r|)` (those of `obstacle_rank_sq_le` and
`obstacle_abs_c_le`), the segment from `p` to the puncture of `δ` is clear exactly when the finite
search finds no obstacle. -/
theorem segmentClear_iff_check (hd : 0 < d) {p : ℚ × ℚ} (hp : p.1 ^ 2 < p.2)
    {δ : MukaiVector ℤ} (hδ : IsRoot d δ) (hr : 0 < δ.r) {R C : ℕ}
    (hR : max ((δ.r : ℚ) ^ 2) (1 / (d * (p.2 - p.1 ^ 2))) ≤ R)
    (hC : (R : ℚ) * max |p.1| |(δ.c : ℚ) / δ.r| ≤ C) :
    SegmentClear d (castPoint p) δ ↔ segmentClearCheck d p δ R C = true := by
  have hheight : height (castPoint p) = ((p.2 - p.1 ^ 2 : ℚ) : ℝ) := by
    simp [height, castPoint]
  have hpos : 0 < height (castPoint p) := by
    rw [hheight]; exact_mod_cast sub_pos.mpr hp
  have heq : ∀ δ' : MukaiVector ℤ,
      (δ'.r == δ.r && δ'.c == δ.c && δ'.s == δ.s) = true ↔ δ' = δ := by
    intro δ'
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => MukaiVector.ext h1 h2 h3, fun h => by subst h; simp⟩
  simp only [segmentClearCheck, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, heq]
  constructor
  · intro hclear δ' hδ'
    obtain ⟨hroot, hr'⟩ := isRoot_of_mem_rootCandidates hδ'
    by_cases hon : OnSegment p (punctureRat d δ) (punctureRat d δ')
    · left
      apply hclear δ' hroot hr'
      rw [puncture_eq_castPoint, puncture_eq_castPoint]
      have : castPoint p = castPoint p := rfl
      exact (castPoint_mem_segment_iff _ _ _).mpr hon
    · exact Or.inr hon
  · intro hcheck δ' hroot hr' hmem
    -- the obstacle is a candidate
    have hrank := obstacle_rank_sq_le hd hpos hδ hr.ne' hroot hr'.ne' hmem
    have hR' : (δ'.r : ℝ) ≤ R := by
      have hr1 : (1 : ℝ) ≤ δ'.r := by exact_mod_cast hr'
      have hRR : max ((δ.r : ℝ) ^ 2) (1 / (d * height (castPoint p))) ≤ R := by
        rw [hheight]; exact_mod_cast hR
      nlinarith
    have hc := obstacle_abs_c_le hr' hmem
    have hC' : |(δ'.c : ℝ)| ≤ C := by
      have hB : max |(castPoint p).1| |(puncture d δ).1| =
          ((max |p.1| |(δ.c : ℚ) / δ.r| : ℚ) : ℝ) := by
        simp [castPoint, puncture_eq]
      rw [hB] at hc
      have hC'' : ((R : ℚ) : ℝ) * ((max |p.1| |(δ.c : ℚ) / δ.r| : ℚ) : ℝ) ≤ ((C : ℚ) : ℝ) := by
        exact_mod_cast hC
      have hBnn : (0 : ℝ) ≤ ((max |p.1| |(δ.c : ℚ) / δ.r| : ℚ) : ℝ) := by
        exact_mod_cast le_max_of_le_left (abs_nonneg _)
      push_cast at hC''
      calc |(δ'.c : ℝ)| ≤ δ'.r * ((max |p.1| |(δ.c : ℚ) / δ.r| : ℚ) : ℝ) := hc
        _ ≤ R * ((max |p.1| |(δ.c : ℚ) / δ.r| : ℚ) : ℝ) := by gcongr
        _ ≤ C := by push_cast; linarith
    have hmemc := mem_rootCandidates hroot hr' (by exact_mod_cast hR')
      (by exact_mod_cast hC')
    rcases hcheck δ' hmemc with h | h
    · exact h
    · exfalso
      apply h
      rw [puncture_eq_castPoint, puncture_eq_castPoint] at hmem
      exact (castPoint_mem_segment_iff _ _ _).mp hmem

/-- **The finite search at work.** At `d = 1`, the segment from `(3/5, 2/5)` (height `1/25`) to
the puncture `(0, 1)` of `𝒪_X` is obstructed: the search over the `775` candidates allowed by the
bounds `r ≤ 25`, `|c| ≤ 15` finds the root `(2, 1, 1)` with puncture `(1/2, 1/2)`. -/
theorem not_segmentClear_example : ¬SegmentClear 1 (castPoint (3 / 5, 2 / 5)) ⟨1, 0, 1⟩ := by
  rw [segmentClear_iff_check (R := 25) (C := 15) one_pos (by norm_num) isRoot_structureSheaf
    one_pos (by norm_num) (by norm_num)]
  decide +kernel

/-- The rigid wall example by the finite search: the segment from `(1/2, 3/2)` to the puncture
of `𝒪_X(H)` is clear. -/
theorem rigid_segmentClear_by_search : SegmentClear 1 (castPoint (1 / 2, 3 / 2)) ⟨1, 1, 2⟩ := by
  rw [segmentClear_iff_check (R := 1) (C := 1) one_pos (by norm_num) isRoot_lineBundle_one
    one_pos (by norm_num) (by norm_num)]
  decide +kernel

/-! ### Sight lines to the cusp of an isotropic class -/

/-- The root `δ'` obstructs the sight line from `p` to the cusp of the isotropic class `w`:
`⟨δ', w⟩ < 0` and `Z_p(δ') ∈ ℝ_{≥0} Z_p(w)`. For `w = (0, 0, 1)` these are the punctures on the
upward ray (`cuspRayClear_point_iff`); for `w` of nonzero rank, the punctures on the segment from
`p` to the point `(c/r, (c/r)²)` of `w` on the parabola (`cuspRayClear_iff_cuspClear`). The
condition is read off the pairing and the central charge only, so an isometry of the Mukai lattice
that matches the charges at two points matches their sight lines
(`cuspRayClear_iff_of_isometry`). -/
def CuspObstacle (d : ℤ) (p : ℝ × ℝ) (w δ' : MukaiVector ℤ) : Prop :=
  IsRoot d δ' ∧ pairing d δ' w < 0 ∧
    ∃ m : ℝ, 0 ≤ m ∧ modelCharge d p δ'.toReal = m * modelCharge d p w.toReal

/-- **Visibility of the cusp of an isotropic class.** No root obstructs the sight line from `p`
to the cusp of `w`. -/
def CuspRayClear (d : ℤ) (p : ℝ × ℝ) (w : MukaiVector ℤ) : Prop :=
  ∀ δ' : MukaiVector ℤ, ¬CuspObstacle d p w δ'

lemma pairing_point_right (d : ℤ) (v : MukaiVector ℤ) : pairing d v point = -v.r := by
  simp [pairing, point]

lemma modelCharge_toReal_point (d : ℝ) (p : ℝ × ℝ) :
    modelCharge d p (point : MukaiVector ℤ).toReal = -1 := by
  simp [modelCharge, charge, map, point]

lemma toReal_neg (v : MukaiVector ℤ) : (-v).toReal = -v.toReal := by ext <;> simp

lemma toReal_smul (a : ℤ) (v : MukaiVector ℤ) : (a • v).toReal = (a : ℝ) • v.toReal := by
  ext <;> simp

/-- The cusp at infinity: the sight line to the cusp of the point class is the upward ray. -/
theorem cuspRayClear_point_iff (hd : 0 < d) {p : ℝ × ℝ} (hp : p.1 ^ 2 < p.2) :
    CuspRayClear d p point ↔ RayClear d p := by
  rw [rayClear_iff hd hp]
  constructor
  · intro h δ' hδ' hr x hx hZ
    refine h δ' ⟨hδ', by rw [pairing_point_right]; omega, -x, by linarith, ?_⟩
    rw [hZ, modelCharge_toReal_point]; push_cast; ring
  · rintro h δ' ⟨hδ', hpair, m, hm, hZ⟩
    rw [pairing_point_right] at hpair
    rw [modelCharge_toReal_point] at hZ
    exact h δ' hδ' (by omega) (-m) (by linarith) (by rw [hZ]; push_cast; ring)

lemma cuspObstacle_neg_iff {p : ℝ × ℝ} {w δ' : MukaiVector ℤ} :
    CuspObstacle d p (-w) (-δ') ↔ CuspObstacle d p w δ' := by
  unfold CuspObstacle IsRoot
  simp only [pairing_neg_left, pairing_neg_right, neg_neg, toReal_neg, modelCharge_neg]
  constructor
  · rintro ⟨h1, h2, m, hm, hZ⟩; exact ⟨h1, h2, m, hm, by linear_combination -hZ⟩
  · rintro ⟨h1, h2, m, hm, hZ⟩; exact ⟨h1, h2, m, hm, by linear_combination -hZ⟩

private lemma neg_neg_mukai (v : MukaiVector ℤ) : - -v = v := by ext <;> simp

/-- A cusp does not depend on the sign of its class. -/
theorem cuspRayClear_neg {p : ℝ × ℝ} {w : MukaiVector ℤ} :
    CuspRayClear d p (-w) ↔ CuspRayClear d p w := by
  constructor
  · intro h δ' hδ'
    exact h (-δ') (cuspObstacle_neg_iff.mpr hδ')
  · intro h δ' hδ'
    rw [← neg_neg_mukai δ'] at hδ'
    exact h (-δ') (cuspObstacle_neg_iff.mp hδ')

/-- ... nor on a positive integral multiple of its class. -/
theorem cuspRayClear_smul {p : ℝ × ℝ} {w : MukaiVector ℤ} {a : ℤ} (ha : 0 < a) :
    CuspRayClear d p (a • w) ↔ CuspRayClear d p w := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have key : ∀ δ', CuspObstacle d p (a • w) δ' ↔ CuspObstacle d p w δ' := by
    intro δ'
    unfold CuspObstacle
    rw [pairing_smul_right, toReal_smul, modelCharge_smul]
    constructor
    · rintro ⟨h1, h2, m, hm, hZ⟩
      exact ⟨h1, by nlinarith, m * a, by positivity, by rw [hZ]; push_cast; ring⟩
    · rintro ⟨h1, h2, m, hm, hZ⟩
      refine ⟨h1, by nlinarith, m / a, by positivity, ?_⟩
      have ha'' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
      rw [hZ]; push_cast; field_simp
  exact ⟨fun h δ' hδ' => h δ' ((key δ').mpr hδ'), fun h δ' hδ' => h δ' ((key δ').mp hδ')⟩

/-- The cusp of an isotropic class of rank zero is the cusp at infinity. -/
theorem cuspRayClear_iff_rayClear (hd : 0 < d) {p : ℝ × ℝ} (hp : p.1 ^ 2 < p.2)
    {w : MukaiVector ℤ} (hw : IsIsotropic d w) (hr : w.r = 0) (hw0 : w ≠ 0) :
    CuspRayClear d p w ↔ RayClear d p := by
  have hc : w.c = 0 := by
    unfold IsIsotropic pairing at hw
    rw [hr] at hw
    have : d * w.c ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff two_ne_zero |>.mp ((mul_eq_zero.mp this).resolve_left hd.ne')
  have hs : w.s ≠ 0 := fun hs => hw0 (MukaiVector.ext (by simp [hr]) (by simp [hc])
    (by simp [hs]))
  rw [← cuspRayClear_point_iff hd hp]
  rcases lt_or_gt_of_ne hs with hs | hs
  · have hw' : w = -((-w.s) • point) := by ext <;> simp [hr, hc, point]
    rw [hw', cuspRayClear_neg, cuspRayClear_smul (by omega)]
  · have hw' : w = w.s • point := by ext <;> simp [hr, hc, point]
    rw [hw', cuspRayClear_smul hs]

/-- **The cusp of an isotropic class of nonzero rank.** The sight line from `p` to the cusp of an
isotropic class `w` of rank `r ≠ 0` is clear exactly when the straight segment from `p` to its
point `(c/r, (c/r)²)` on the parabola meets no puncture. -/
theorem cuspRayClear_iff_cuspClear (hd : 0 < d) {p : ℝ × ℝ} (hp : p.1 ^ 2 < p.2)
    {w : MukaiVector ℤ} (hw : IsIsotropic d w) (hr : w.r ≠ 0) :
    CuspRayClear d p w ↔ CuspClear d p ((w.c : ℝ) / w.r) := by
  -- reduce to positive rank
  wlog hpos : 0 < w.r generalizing w
  · have h := this (w := -w) (by unfold IsIsotropic at hw ⊢; rw [pairing_neg_left,
      pairing_neg_right, neg_neg, hw]) (by simp; exact hr) (by simp; omega)
    rw [cuspRayClear_neg] at h
    rw [h]
    simp [neg_div_neg_eq]
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := hd'.ne'
  have hwr : (0 : ℝ) < w.r := by exact_mod_cast hpos
  -- the point of `w` is `(m, m²)`, and `⟨κ_p, w⟩ < 0`
  have hww : pairing (d : ℝ) w.toReal w.toReal = 0 := by
    rw [pairing_toReal]; exact_mod_cast hw
  have hcusp : toModel d w.toReal = ((w.c : ℝ) / w.r, ((w.c : ℝ) / w.r) ^ 2) := by
    have h := toModel_snd_sub_sq hd0 (v := w.toReal) (by simpa using hr)
    rw [hww, neg_zero, zero_div, sub_eq_zero] at h
    ext
    · rfl
    · exact h
  have hκw : pairing (d : ℝ) (kernelVector (d : ℝ) p) w.toReal < 0 :=
    pairing_neg_of_rank_pos hd' (by rw [pairing_kernelVector_self]; nlinarith) hww.le
      (by simp) (by simpa using hpos)
  have hseg : ∀ δ' : MukaiVector ℤ, 0 < δ'.r →
      (puncture d δ' ∈ segment ℝ p ((w.c : ℝ) / w.r, ((w.c : ℝ) / w.r) ^ 2) ↔
        ∃ l m : ℝ, 0 ≤ l ∧ 0 ≤ m ∧ δ'.toReal = l • kernelVector (d : ℝ) p + m • w.toReal) := by
    intro δ' hr'
    rw [← hcusp]
    have h := toModel_mem_segment_iff hd0 (u := δ'.toReal) (v := kernelVector (d : ℝ) p)
      (w := w.toReal) (by simpa using hr') (by simp) (by simpa using hpos)
    rwa [toModel_kernelVector hd0] at h
  constructor
  · intro h δ' hδ' hr' hmem
    obtain ⟨l, m, hl, hm, hdec⟩ := (hseg δ' hr').mp hmem
    apply h δ'
    refine ⟨hδ', ?_, m, hm, ?_⟩
    · -- `⟨δ', w⟩ = l ⟨κ_p, w⟩ < 0`, as `l > 0`: otherwise `δ' = m w` would be isotropic
      have hl0 : 0 < l := by
        rcases hl.lt_or_eq with hl | rfl
        · exact hl
        · exfalso
          have hroot := isRoot_toReal.mpr hδ'
          unfold IsRoot at hroot
          rw [hdec] at hroot
          simp only [pairing_add_left, pairing_add_right, pairing_smul_left, pairing_smul_right,
            hww, zero_mul, mul_zero, add_zero] at hroot
          norm_num at hroot
      have : ((pairing d δ' w : ℤ) : ℝ) =
          l * pairing (d : ℝ) (kernelVector (d : ℝ) p) w.toReal := by
        rw [← pairing_toReal, hdec, pairing_add_left, pairing_smul_left, pairing_smul_left, hww]
        ring
      have : ((pairing d δ' w : ℤ) : ℝ) < 0 := by
        rw [this]; exact mul_neg_of_pos_of_neg hl0 hκw
      exact_mod_cast this
    · rw [hdec, modelCharge_add, modelCharge_smul, modelCharge_smul,
        modelCharge_kernelVector _ hp.le, mul_zero, zero_add]
  · rintro h δ' ⟨hδ', hpair, m, hm, hZ⟩
    obtain ⟨t, ht⟩ := (modelCharge_eq_ofReal_mul_iff hd0 hp _ _ _).mp hZ
    -- `⟨δ', w⟩ = t ⟨κ_p, w⟩ < 0` forces `t > 0`
    have hpair' : ((pairing d δ' w : ℤ) : ℝ) =
        t * pairing (d : ℝ) (kernelVector (d : ℝ) p) w.toReal := by
      rw [← pairing_toReal, ht, pairing_add_left, pairing_smul_left, pairing_smul_left, hww]
      ring
    have hneg : ((pairing d δ' w : ℤ) : ℝ) < 0 := by exact_mod_cast hpair
    have ht0 : 0 < t := by
      by_contra ht0
      push Not at ht0
      have : 0 ≤ t * pairing (d : ℝ) (kernelVector (d : ℝ) p) w.toReal :=
        mul_nonneg_of_nonpos_of_nonpos ht0 hκw.le
      linarith
    have hr' : 0 < δ'.r := by
      have hrk := congrArg MukaiVector.r ht
      simp only [toReal_r, add_r, smul_r, kernelVector_r, mul_one] at hrk
      have : (0 : ℝ) < δ'.r := by rw [hrk]; positivity
      exact_mod_cast this
    exact h δ' hδ' hr' ((hseg δ' hr').mpr ⟨t, m, ht0.le, hm, by rw [ht]; ext <;> simp <;> ring⟩)

/-- **Transport of sight lines by an isometry.** Let `g` be a surjective isometry of the Mukai
lattice that matches real proportionality of central charges at `p` with that at `q`:
`Z_p(v) = m Z_p(u) ↔ Z_q(g v) = m Z_q(g u)`. Then the sight line from `p` to the cusp of `u` is
clear exactly when the sight line from `q` to the cusp of `g u` is. -/
theorem cuspRayClear_iff_of_isometry {p q : ℝ × ℝ} (g g' : MukaiVector ℤ → MukaiVector ℤ)
    (hg : ∀ v, g (g' v) = v) (hpair : ∀ v w, pairing d (g v) (g w) = pairing d v w)
    (hcharge : ∀ (v w : MukaiVector ℤ) (m : ℝ),
      modelCharge d p v.toReal = m * modelCharge d p w.toReal ↔
        modelCharge d q (g v).toReal = m * modelCharge d q (g w).toReal)
    (u : MukaiVector ℤ) :
    CuspRayClear d p u ↔ CuspRayClear d q (g u) := by
  have key : ∀ δ', CuspObstacle d p u δ' ↔ CuspObstacle d q (g u) (g δ') := by
    intro δ'
    unfold CuspObstacle IsRoot
    rw [hpair, hpair]
    constructor
    · rintro ⟨h1, h2, m, hm, hZ⟩; exact ⟨h1, h2, m, hm, (hcharge _ _ _).mp hZ⟩
    · rintro ⟨h1, h2, m, hm, hZ⟩; exact ⟨h1, h2, m, hm, (hcharge _ _ _).mpr hZ⟩
  constructor
  · intro h δ'' hδ''
    rw [← hg δ''] at hδ''
    exact h _ ((key _).mpr hδ'')
  · intro h δ' hδ'
    exact h _ ((key δ').mp hδ')

end AlgebraicGeometry.K3.PicardRankOne
