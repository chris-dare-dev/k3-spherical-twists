/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.Lattice.Mukai.PicardRankOne
import Mathlib.Analysis.Convex.Segment
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The projective model of the Mukai lattice of a K3 surface of Picard rank one

Let `X` be a K3 surface with `Pic X = ℤH` and `H² = 2d > 0`. On the real Mukai lattice
`ℝ ⊕ ℝH ⊕ ℝ` the Mukai form `⟨v, v⟩ = 2dc² - 2rs` has signature `(2, 1)`
(`pairing_self_eq`, `pairing_self_pos_of_pairing_structureSheaf_eq_zero`): it is negative on the
line of `v(𝒪_X) = (1, 0, 1)` and positive definite on its orthogonal complement.

A vector of negative square has nonzero rank, and the chart `v ↦ (c/r, s/(dr))` (`toModel`)
identifies the projectivized negative cone with the region `t > b²` of the `(b, t)`-plane
(`pairing_self_neg_iff`); the isotropic lines are the parabola `t = b²` and the line of the
point class `(0, 0, 1)`, the point at infinity (`isIsotropic_iff`). Over a point `p = (b, t)`
sits the kernel vector `κ_p = (1, b, dt)` (`kernelVector`), with `⟨κ_p, κ_q⟩ = -d B(p, q)` for
`B(p, q) = t_p + t_q - 2 b_p b_q`, the form of `UpperHalfPlane.cosh_dist_eq`. So this chart is
the projective model of the half-plane in which geodesics are straight
(`UpperHalfPlane.dist_add_dist_eq_iff`).

The cone spanned by two vectors of positive rank is the segment between their points
(`toModel_mem_segment_iff`), and the cone spanned by a kernel vector and the point class is the
vertical ray above its point (`toModel_mem_ray_iff`). The height of a point above the parabola
is `-⟨v, v⟩/(2dr²)` (`toModel_snd_sub_sq`), so the puncture of a root sits at height `1/(dr²)`,
and the height is concave along segments (`height_segment`).

Finally the reverse Cauchy–Schwarz inequality of a Lorentzian form: for `⟨v, v⟩ < 0`,
`⟨v, v⟩⟨w, w⟩ ≤ ⟨v, w⟩²` with equality only on the line of `v` (`mul_pairing_self_le_sq`,
`sq_pairing_eq_iff`), and two vectors of the closed negative cone with positive rank have negative
pairing (`pairing_neg_of_rank_pos`; Lemma 3.2 of Bayer–Bridgeland, arXiv:1310.8266). Two distinct
roots of positive rank therefore pair to at most `-3` (`pairing_le_neg_three`).
-/

namespace MukaiVector

/-! ### Kernel vectors -/

section CommRing

variable {R : Type*} [CommRing R]

/-- The kernel vector `κ_p = (1, b, dt)` over the point `p = (b, t)` of the projective model. At
`t = b² + a²` it spans the kernel of the central charge `Z_{b+ia}` on real classes. -/
def kernelVector (d : R) (p : R × R) : MukaiVector R := ⟨1, p.1, d * p.2⟩

@[simp] lemma kernelVector_r (d : R) (p : R × R) : (kernelVector d p).r = 1 := rfl
@[simp] lemma kernelVector_c (d : R) (p : R × R) : (kernelVector d p).c = p.1 := rfl
@[simp] lemma kernelVector_s (d : R) (p : R × R) : (kernelVector d p).s = d * p.2 := rfl

/-- `⟨κ_p, v⟩ = 2dbc - s - drt`. -/
lemma pairing_kernelVector_left (d : R) (p : R × R) (v : MukaiVector R) :
    pairing d (kernelVector d p) v = 2 * d * p.1 * v.c - v.s - d * p.2 * v.r := by
  simp only [pairing, kernelVector]; ring

/-- `⟨κ_p, κ_q⟩ = -d (t_p + t_q - 2 b_p b_q)`. -/
lemma pairing_kernelVector (d : R) (p q : R × R) :
    pairing d (kernelVector d p) (kernelVector d q) = -d * (p.2 + q.2 - 2 * p.1 * q.1) := by
  simp only [pairing, kernelVector]; ring

/-- `⟨κ_p, κ_p⟩ = -2d(t - b²)`: the kernel vector is negative exactly above the parabola. -/
lemma pairing_kernelVector_self (d : R) (p : R × R) :
    pairing d (kernelVector d p) (kernelVector d p) = -2 * d * (p.2 - p.1 ^ 2) := by
  simp only [pairing, kernelVector]; ring

/-- `⟨κ_p, (0, 0, 1)⟩ = -1`. -/
@[simp] lemma pairing_kernelVector_point (d : R) (p : R × R) :
    pairing d (kernelVector d p) point = -1 := by
  simp [pairing, kernelVector, point]

/-- Moving up the vertical through `p` adds multiples of the point class:
`κ_p + m (0, 0, 1) = κ_{(b, t + m/d)}`. -/
lemma kernelVector_add_smul_point {K : Type*} [Field K] {d : K} (hd : d ≠ 0) (p : K × K)
    (m : K) : kernelVector d p + m • point = kernelVector d (p.1, p.2 + m / d) := by
  ext <;> simp [kernelVector, point]
  field_simp

end CommRing

/-! ### The signature -/

section Real

variable {d : ℝ}

/-- `⟨v, v⟩ = 2dc² + (r - s)²/2 - (r + s)²/2`. -/
lemma pairing_self_eq (d : ℝ) (v : MukaiVector ℝ) :
    pairing d v v = 2 * d * v.c ^ 2 + (v.r - v.s) ^ 2 / 2 - (v.r + v.s) ^ 2 / 2 := by
  simp only [pairing]; ring

/-- The Mukai form is negative on the line of `v(𝒪_X) = (1, 0, 1)`. -/
lemma pairing_structureSheaf (d : ℝ) :
    pairing d (⟨1, 0, 1⟩ : MukaiVector ℝ) ⟨1, 0, 1⟩ = -2 := by
  simp [pairing]; norm_num

/-- **Signature `(2, 1)`.** For `d > 0` the Mukai form is positive definite on the orthogonal
complement of `v(𝒪_X) = (1, 0, 1)`, a plane, and negative on its line. -/
lemma pairing_self_pos_of_pairing_structureSheaf_eq_zero (hd : 0 < d) {v : MukaiVector ℝ}
    (hv : pairing d ⟨1, 0, 1⟩ v = 0) (hv0 : v ≠ 0) : 0 < pairing d v v := by
  simp only [pairing] at hv ⊢
  have hs : v.s = -v.r := by linarith
  rw [hs]
  by_contra h
  push Not at h
  have hc2 : v.c ^ 2 ≤ 0 := by
    by_contra hc
    push Not at hc
    nlinarith [mul_pos hd hc, sq_nonneg v.r]
  have hr2 : v.r ^ 2 ≤ 0 := by nlinarith [mul_nonneg hd.le (sq_nonneg v.c)]
  have hc : v.c = 0 := pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm hc2 (sq_nonneg _))
  have hr : v.r = 0 := pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm hr2 (sq_nonneg _))
  exact hv0 (MukaiVector.ext hr hc (by simp [hs, hr]))

/-! ### The negative cone and the isotropic lines -/

/-- A vector of negative square has nonzero rank: there is no negative vector of rank zero. -/
lemma r_ne_zero_of_pairing_self_neg (hd : 0 ≤ d) {v : MukaiVector ℝ} (hv : pairing d v v < 0) :
    v.r ≠ 0 := by
  intro hr
  simp only [pairing, hr] at hv
  nlinarith [sq_nonneg v.c, mul_nonneg hd (sq_nonneg v.c)]

/-- The point `(c/r, s/(dr))` of the projective model of a vector of nonzero rank. For a root
of positive rank this is its puncture. -/
noncomputable def toModel (d : ℝ) (v : MukaiVector ℝ) : ℝ × ℝ := (v.c / v.r, v.s / (d * v.r))

@[simp] lemma toModel_fst (d : ℝ) (v : MukaiVector ℝ) : (toModel d v).1 = v.c / v.r := rfl

@[simp] lemma toModel_snd (d : ℝ) (v : MukaiVector ℝ) : (toModel d v).2 = v.s / (d * v.r) := rfl

/-- The height of the point of `v` above the parabola is `-⟨v, v⟩/(2dr²)`. -/
lemma toModel_snd_sub_sq (hd : d ≠ 0) {v : MukaiVector ℝ} (hr : v.r ≠ 0) :
    (toModel d v).2 - (toModel d v).1 ^ 2 = -pairing d v v / (2 * d * v.r ^ 2) := by
  simp only [toModel, pairing]
  field_simp
  ring

/-- **The negative cone is the region above the parabola.** For `d > 0`, `⟨v, v⟩ < 0` exactly
when `v` has nonzero rank and its point `(c/r, s/(dr))` satisfies `t > b²`. -/
theorem pairing_self_neg_iff (hd : 0 < d) (v : MukaiVector ℝ) :
    pairing d v v < 0 ↔ v.r ≠ 0 ∧ (toModel d v).1 ^ 2 < (toModel d v).2 := by
  constructor
  · intro hv
    have hr := r_ne_zero_of_pairing_self_neg hd.le hv
    refine ⟨hr, ?_⟩
    rw [← sub_pos, toModel_snd_sub_sq hd.ne' hr]
    have : 0 < 2 * d * v.r ^ 2 := by positivity
    exact div_pos (neg_pos.mpr hv) this
  · rintro ⟨hr, h⟩
    rw [← sub_pos, toModel_snd_sub_sq hd.ne' hr] at h
    have : 0 < 2 * d * v.r ^ 2 := by positivity
    have := (div_pos_iff_of_pos_right this).mp h
    linarith

/-- **The isotropic lines.** For `d > 0`, `⟨v, v⟩ = 0` exactly when either `v` has nonzero rank
and its point lies on the parabola `t = b²`, or `v` is a multiple of the point class `(0, 0, 1)`,
the point at infinity of the model. -/
theorem isIsotropic_iff (hd : 0 < d) (v : MukaiVector ℝ) :
    IsIsotropic d v ↔
      (v.r ≠ 0 ∧ (toModel d v).2 = (toModel d v).1 ^ 2) ∨ ∃ s : ℝ, v = s • point := by
  unfold IsIsotropic
  by_cases hr : v.r = 0
  · have : pairing d v v = 2 * d * v.c ^ 2 := by simp only [pairing, hr]; ring
    rw [this]
    constructor
    · intro h
      right
      have hc : v.c = 0 := by
        have hc2 : v.c ^ 2 = 0 := by
          rcases mul_eq_zero.mp h with h' | h'
          · nlinarith
          · exact h'
        exact pow_eq_zero_iff two_ne_zero |>.mp hc2
      exact ⟨v.s, MukaiVector.ext (by simp [hr, point]) (by simp [hc, point])
        (by simp [point])⟩
    · rintro (⟨h, -⟩ | ⟨s, rfl⟩)
      · exact absurd hr h
      · simp [point]
  · rw [← sub_eq_zero (a := (toModel d v).2), toModel_snd_sub_sq hd.ne' hr]
    have : 2 * d * v.r ^ 2 ≠ 0 := by positivity
    constructor
    · intro h; left; exact ⟨hr, by rw [h, neg_zero, zero_div]⟩
    · rintro (⟨-, h⟩ | ⟨s, rfl⟩)
      · rw [div_eq_zero_iff, neg_eq_zero] at h
        exact h.resolve_right this
      · simp [point] at hr

/-! ### Points of the model -/

lemma toModel_kernelVector (hd : d ≠ 0) (p : ℝ × ℝ) : toModel d (kernelVector d p) = p := by
  ext <;> simp [toModel, kernelVector]
  field_simp

lemma toModel_smul {a : ℝ} (ha : a ≠ 0) (v : MukaiVector ℝ) : toModel d (a • v) = toModel d v := by
  ext <;> simp only [toModel, smul_c, smul_r, smul_s]
  · rw [mul_div_mul_left _ _ ha]
  · rw [mul_left_comm, mul_div_mul_left _ _ ha]

/-- A vector of nonzero rank is `r` times the kernel vector over its point. -/
lemma eq_smul_kernelVector_toModel (hd : d ≠ 0) {v : MukaiVector ℝ} (hr : v.r ≠ 0) :
    v = v.r • kernelVector d (toModel d v) := by
  ext <;> simp [toModel, kernelVector]
  · field_simp
  · field_simp

/-- Kernel vectors are affine in the point: `κ_{a p + b q} = a κ_p + b κ_q` for `a + b = 1`. -/
lemma kernelVector_affine (d : ℝ) (p q : ℝ × ℝ) {a b : ℝ} (hab : a + b = 1) :
    kernelVector d (a • p + b • q) = a • kernelVector d p + b • kernelVector d q := by
  ext <;> simp [kernelVector]
  · exact hab.symm
  · ring

/-- **The cone spanned by two vectors of positive rank is the segment between their points.** -/
theorem toModel_mem_segment_iff (hd : d ≠ 0) {u v w : MukaiVector ℝ} (hu : 0 < u.r)
    (hv : 0 < v.r) (hw : 0 < w.r) :
    toModel d u ∈ segment ℝ (toModel d v) (toModel d w) ↔
      ∃ l m : ℝ, 0 ≤ l ∧ 0 ≤ m ∧ u = l • v + m • w := by
  constructor
  · rintro ⟨a, b, ha, hb, hab, h⟩
    refine ⟨u.r * a / v.r, u.r * b / w.r, by positivity, by positivity, ?_⟩
    conv_lhs => rw [eq_smul_kernelVector_toModel hd hu.ne', ← h, kernelVector_affine d _ _ hab]
    conv_rhs => rw [eq_smul_kernelVector_toModel hd hv.ne' (v := v),
      eq_smul_kernelVector_toModel hd hw.ne' (v := w)]
    ext <;> simp only [add_r, add_c, add_s, smul_r, smul_c, smul_s, kernelVector_r,
      kernelVector_c, kernelVector_s] <;> field_simp
  · rintro ⟨l, m, hl, hm, rfl⟩
    have hr : (l • v + m • w).r = l * v.r + m * w.r := by simp
    rw [hr] at hu
    refine ⟨l * v.r / (l * v.r + m * w.r), m * w.r / (l * v.r + m * w.r), by positivity,
      by positivity, by field_simp, ?_⟩
    ext <;> simp [toModel] <;> field_simp

/-- **The cone spanned by a kernel vector and the point class is the vertical ray above its
point.** A vector `u` of positive rank lies in `{l κ_p + m (0, 0, 1) : l, m ≥ 0}` exactly when its
point lies on the upward ray from `p`. -/
theorem toModel_mem_ray_iff (hd : 0 < d) {u : MukaiVector ℝ} (hu : 0 < u.r) (p : ℝ × ℝ) :
    ((toModel d u).1 = p.1 ∧ p.2 ≤ (toModel d u).2) ↔
      ∃ l m : ℝ, 0 ≤ l ∧ 0 ≤ m ∧ u = l • kernelVector d p + m • point := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨u.r, d * u.r * ((toModel d u).2 - p.2), hu.le,
      mul_nonneg (mul_nonneg hd.le hu.le) (sub_nonneg.mpr h2), ?_⟩
    simp only [toModel_fst] at h1
    ext <;> simp [kernelVector, point]
    · rw [← h1]; field_simp
    · field_simp; ring
  · rintro ⟨l, m, hl, hm, rfl⟩
    have hr : (l • kernelVector d p + m • point).r = l := by simp [point]
    rw [hr] at hu
    refine ⟨by simp [point]; field_simp, ?_⟩
    simp [point]
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg hd.le hm]

/-! ### Heights -/

/-- The height `t - b²` of a point above the parabola. -/
def height (p : ℝ × ℝ) : ℝ := p.2 - p.1 ^ 2

/-- The height is concave along segments:
`h((1 - θ) p + θ q) = (1 - θ) h(p) + θ h(q) + θ(1 - θ)(b_p - b_q)²`. -/
lemma height_segment (p q : ℝ × ℝ) (θ : ℝ) :
    height ((1 - θ) • p + θ • q) =
      (1 - θ) * height p + θ * height q + θ * (1 - θ) * (p.1 - q.1) ^ 2 := by
  simp only [height, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- On a segment the height is at least its smaller value at the two ends. -/
lemma min_height_le_of_mem_segment {p q x : ℝ × ℝ} (hx : x ∈ segment ℝ p q) :
    min (height p) (height q) ≤ height x := by
  rw [segment_eq_image] at hx
  obtain ⟨θ, ⟨h0, h1⟩, rfl⟩ := hx
  rw [height_segment]
  have hm1 : min (height p) (height q) ≤ height p := min_le_left _ _
  have hm2 : min (height p) (height q) ≤ height q := min_le_right _ _
  have : 0 ≤ θ * (1 - θ) * (p.1 - q.1) ^ 2 := by
    have : 0 ≤ 1 - θ := by linarith
    positivity
  nlinarith

/-- The puncture of a root of nonzero rank is at height `1/(dr²)`. -/
lemma height_toModel_of_isRoot (hd : d ≠ 0) {v : MukaiVector ℝ} (hv : IsRoot d v)
    (hr : v.r ≠ 0) : height (toModel d v) = 1 / (d * v.r ^ 2) := by
  rw [height, toModel_snd_sub_sq hd hr, hv]
  field_simp

/-! ### The reverse Cauchy–Schwarz inequality -/

/-- For `⟨v, w⟩ = 0`: `rs ⟨w, w⟩ = 2dC²(rs - dc²) + (rS - Rs)²/2`. -/
private lemma rs_mul_pairing_self (d : ℝ) {v w : MukaiVector ℝ} (hvw : pairing d v w = 0) :
    v.r * v.s * pairing d w w =
      2 * d * w.c ^ 2 * (v.r * v.s - d * v.c ^ 2) + (v.r * w.s - w.r * v.s) ^ 2 / 2 := by
  simp only [pairing] at hvw ⊢
  linear_combination (1 / 2 * (v.r * w.s + w.r * v.s + 2 * d * v.c * w.c)) * hvw

/-- A negative vector has `rs > dc² ≥ 0`. -/
private lemma dc_sq_lt_rs {v : MukaiVector ℝ} (hv : pairing d v v < 0) :
    d * v.c ^ 2 < v.r * v.s := by
  simp only [pairing] at hv; nlinarith

/-- The orthogonal complement of a negative vector is positive semidefinite. -/
lemma pairing_self_nonneg_of_pairing_eq_zero (hd : 0 < d) {v w : MukaiVector ℝ}
    (hv : pairing d v v < 0) (hvw : pairing d v w = 0) : 0 ≤ pairing d w w := by
  have h1 := dc_sq_lt_rs hv
  have hrs : 0 < v.r * v.s := lt_of_le_of_lt (mul_nonneg hd.le (sq_nonneg _)) h1
  have key := rs_mul_pairing_self d hvw
  have : 0 ≤ v.r * v.s * pairing d w w := by
    rw [key]
    have : 0 ≤ v.r * v.s - d * v.c ^ 2 := by linarith
    positivity
  by_contra hneg
  push Not at hneg
  have := mul_neg_of_pos_of_neg hrs hneg
  linarith

/-- The orthogonal complement of a negative vector is positive definite. -/
lemma pairing_self_pos_of_pairing_eq_zero (hd : 0 < d) {v w : MukaiVector ℝ}
    (hv : pairing d v v < 0) (hvw : pairing d v w = 0) (hw : w ≠ 0) : 0 < pairing d w w := by
  rcases (pairing_self_nonneg_of_pairing_eq_zero hd hv hvw).lt_or_eq with h | h
  · exact h
  exfalso
  apply hw
  have h1 := dc_sq_lt_rs hv
  have hrs : 0 < v.r * v.s := lt_of_le_of_lt (mul_nonneg hd.le (sq_nonneg _)) h1
  have key := rs_mul_pairing_self d hvw
  rw [← h, mul_zero] at key
  have hA : 0 ≤ 2 * d * w.c ^ 2 * (v.r * v.s - d * v.c ^ 2) := by
    have : 0 ≤ v.r * v.s - d * v.c ^ 2 := by linarith
    positivity
  have hB : 0 ≤ (v.r * w.s - w.r * v.s) ^ 2 / 2 := by positivity
  have hA0 : w.c ^ 2 * (2 * d * (v.r * v.s - d * v.c ^ 2)) = 0 := by linarith
  have hpos : 0 < 2 * d * (v.r * v.s - d * v.c ^ 2) := by
    have : 0 < v.r * v.s - d * v.c ^ 2 := by linarith
    positivity
  have hc : w.c = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp ((mul_eq_zero.mp hA0).resolve_right hpos.ne')
  have hB' : v.r * w.s - w.r * v.s = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp (by linarith)
  have hvw' := hvw
  simp only [pairing, hc, mul_zero, zero_sub] at hvw'
  -- `rS = Rs` and `rS + Rs = 0`, with `r, s ≠ 0`
  have hrS : v.r * w.s = 0 := by linarith
  have hRs : w.r * v.s = 0 := by linarith
  have hr0 : v.r ≠ 0 := fun h0 => by rw [h0, zero_mul] at hrs; exact lt_irrefl 0 hrs
  have hs0 : v.s ≠ 0 := fun h0 => by rw [h0, mul_zero] at hrs; exact lt_irrefl 0 hrs
  exact MukaiVector.ext ((mul_eq_zero.mp hRs).resolve_right hs0) (by simp [hc])
    ((mul_eq_zero.mp hrS).resolve_left hr0)

/-- **Reverse Cauchy–Schwarz.** For `⟨v, v⟩ < 0`, `⟨v, v⟩⟨w, w⟩ ≤ ⟨v, w⟩²`. -/
theorem mul_pairing_self_le_sq (hd : 0 < d) {v : MukaiVector ℝ} (hv : pairing d v v < 0)
    (w : MukaiVector ℝ) : pairing d v v * pairing d w w ≤ pairing d v w ^ 2 := by
  -- `w' = ⟨v, v⟩ w - ⟨v, w⟩ v` is orthogonal to `v`, and `⟨w', w'⟩ = -⟨v, v⟩ (⟨v,w⟩² - v² w²)`.
  set n := pairing d v v
  set q := pairing d v w
  have horth : pairing d v (n • w - q • v) = 0 := by
    have : n • w - q • v = n • w + (-q) • v := by ext <;> simp <;> ring
    rw [this, pairing_add_right, pairing_smul_right, pairing_smul_right]
    ring
  have h := pairing_self_nonneg_of_pairing_eq_zero hd hv horth
  have hexp : pairing d (n • w - q • v) (n • w - q • v) =
      -n * (q ^ 2 - n * pairing d w w) := by
    have : n • w - q • v = n • w + (-q) • v := by ext <;> simp <;> ring
    rw [this, pairing_add_left, pairing_add_right, pairing_add_right, pairing_smul_left,
      pairing_smul_left, pairing_smul_left, pairing_smul_left, pairing_smul_right,
      pairing_smul_right, pairing_smul_right, pairing_smul_right, pairing_comm d w v]
    ring
  rw [hexp] at h
  nlinarith

/-- Equality in the reverse Cauchy–Schwarz inequality holds only on the line of `v`. -/
theorem sq_pairing_eq_iff (hd : 0 < d) {v : MukaiVector ℝ} (hv : pairing d v v < 0)
    (w : MukaiVector ℝ) :
    pairing d v w ^ 2 = pairing d v v * pairing d w w ↔ ∃ a : ℝ, w = a • v := by
  set n := pairing d v v
  set q := pairing d v w
  have hn : n ≠ 0 := hv.ne
  constructor
  · intro h
    have horth : pairing d v (n • w - q • v) = 0 := by
      have : n • w - q • v = n • w + (-q) • v := by ext <;> simp <;> ring
      rw [this, pairing_add_right, pairing_smul_right, pairing_smul_right]
      ring
    have hexp : pairing d (n • w - q • v) (n • w - q • v) =
        -n * (q ^ 2 - n * pairing d w w) := by
      have : n • w - q • v = n • w + (-q) • v := by ext <;> simp <;> ring
      rw [this, pairing_add_left, pairing_add_right, pairing_add_right, pairing_smul_left,
        pairing_smul_left, pairing_smul_left, pairing_smul_left, pairing_smul_right,
        pairing_smul_right, pairing_smul_right, pairing_smul_right, pairing_comm d w v]
      ring
    have h0 : n • w - q • v = 0 := by
      by_contra hne
      have := pairing_self_pos_of_pairing_eq_zero hd hv horth hne
      rw [hexp, h, sub_self, mul_zero] at this
      exact lt_irrefl 0 this
    refine ⟨q / n, ?_⟩
    ext <;> simp only [smul_r, smul_c, smul_s]
    · have := congrArg MukaiVector.r h0; simp at this; field_simp; linarith
    · have := congrArg MukaiVector.c h0; simp at this; field_simp; linarith
    · have := congrArg MukaiVector.s h0; simp at this; field_simp; linarith
  · rintro ⟨a, rfl⟩
    simp only [n, q, pairing_smul_right, pairing_smul_left]
    ring

/-- **Lemma 3.2 of Bayer–Bridgeland** (arXiv:1310.8266), for vectors of positive rank. If
`⟨v, v⟩ < 0`, `⟨w, w⟩ ≤ 0` and both have positive rank, then `⟨v, w⟩ < 0`. -/
theorem pairing_neg_of_rank_pos (hd : 0 < d) {v w : MukaiVector ℝ} (hv : pairing d v v < 0)
    (hw : pairing d w w ≤ 0) (hvr : 0 < v.r) (hwr : 0 < w.r) : pairing d v w < 0 := by
  simp only [pairing] at hv hw ⊢
  -- `rR⟨v, w⟩ ≤ 2dcCrR - r²dC² - R²rs < -d(rC - Rc)² ≤ 0`
  have hrR : 0 < v.r * w.r := mul_pos hvr hwr
  have h1 : d * w.c ^ 2 ≤ w.r * w.s := by linarith
  have h2 : d * v.c ^ 2 < v.r * v.s := by linarith
  have key : v.r * w.r * (2 * d * v.c * w.c - v.r * w.s - w.r * v.s) <
      -d * (v.r * w.c - w.r * v.c) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg v.r),
      mul_lt_mul_of_pos_left h2 (pow_pos hwr 2)]
  have : -d * (v.r * w.c - w.r * v.c) ^ 2 ≤ 0 := by
    have := mul_nonneg hd.le (sq_nonneg (v.r * w.c - w.r * v.c))
    linarith
  by_contra hcon
  push Not at hcon
  nlinarith

end Real

/-! ### Integral roots -/

/-- The real image of an integral Mukai vector. -/
abbrev toReal (v : MukaiVector ℤ) : MukaiVector ℝ := v.map (Int.castRingHom ℝ)

@[simp] lemma toReal_r (v : MukaiVector ℤ) : v.toReal.r = v.r := rfl
@[simp] lemma toReal_c (v : MukaiVector ℤ) : v.toReal.c = v.c := rfl
@[simp] lemma toReal_s (v : MukaiVector ℤ) : v.toReal.s = v.s := rfl

lemma toReal_injective : Function.Injective toReal := by
  intro v w h
  have hr := congrArg MukaiVector.r h
  have hc := congrArg MukaiVector.c h
  have hs := congrArg MukaiVector.s h
  simp only [toReal_r, toReal_c, toReal_s, Int.cast_inj] at hr hc hs
  exact MukaiVector.ext hr hc hs

lemma pairing_toReal (d : ℤ) (v w : MukaiVector ℤ) :
    pairing (d : ℝ) v.toReal w.toReal = pairing d v w := by
  simpa using pairing_map (Int.castRingHom ℝ) d v w

lemma isRoot_toReal {d : ℤ} {v : MukaiVector ℤ} : IsRoot (d : ℝ) v.toReal ↔ IsRoot d v := by
  unfold IsRoot
  rw [pairing_toReal]
  exact_mod_cast Iff.rfl

/-- Two roots of positive rank with the same point of the model are equal. -/
theorem eq_of_toModel_eq {d : ℤ} (hd : 0 < d) {δ δ' : MukaiVector ℤ} (hδ : IsRoot d δ)
    (hδ' : IsRoot d δ') (hr : 0 < δ.r) (hr' : 0 < δ'.r)
    (h : toModel d δ.toReal = toModel d δ'.toReal) : δ = δ' := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hr1 : (δ.r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hr2 : (δ'.r : ℝ) ≠ 0 := by exact_mod_cast hr'.ne'
  -- the heights `1/(dr²)` agree, so the ranks agree, and then the points give `c` and `s`
  have h1 := height_toModel_of_isRoot hd' (isRoot_toReal.mpr hδ) hr1
  have h2 := height_toModel_of_isRoot hd' (isRoot_toReal.mpr hδ') hr2
  rw [h, h2] at h1
  have hrr : (δ.r : ℝ) = δ'.r := by
    have hpos : (0 : ℝ) < δ.r := by exact_mod_cast hr
    have hpos' : (0 : ℝ) < δ'.r := by exact_mod_cast hr'
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
    simp only [toReal_r] at h1
    field_simp at h1
    exact (sq_eq_sq₀ hpos.le hpos'.le).mp h1
  have hc := congrArg Prod.fst h
  have hs := congrArg Prod.snd h
  simp only [toModel_fst, toModel_snd, toReal_r, toReal_c, toReal_s] at hc hs
  rw [hrr] at hc hs
  rw [div_left_inj₀ hr2] at hc
  rw [div_left_inj₀ (mul_ne_zero hd' hr2)] at hs
  exact MukaiVector.ext (by exact_mod_cast hrr) (by exact_mod_cast hc) (by exact_mod_cast hs)

/-- Two distinct roots of positive rank pair to at most `-3`: their pairing is negative by
`pairing_neg_of_rank_pos`, and its square exceeds `⟨δ, δ⟩⟨δ', δ'⟩ = 4` since they are not
proportional. -/
theorem pairing_le_neg_three {d : ℤ} (hd : 0 < d) {δ δ' : MukaiVector ℤ} (hδ : IsRoot d δ)
    (hδ' : IsRoot d δ') (hr : 0 < δ.r) (hr' : 0 < δ'.r) (hne : δ ≠ δ') :
    pairing d δ δ' ≤ -3 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hv : pairing (d : ℝ) δ.toReal δ.toReal = -2 := isRoot_toReal.mpr hδ
  have hv' : pairing (d : ℝ) δ'.toReal δ'.toReal = -2 := isRoot_toReal.mpr hδ'
  have hneg : pairing (d : ℝ) δ.toReal δ'.toReal < 0 :=
    pairing_neg_of_rank_pos hd' (by rw [hv]; norm_num) (by rw [hv']; norm_num)
      (by simpa using hr) (by simpa using hr')
  have hvneg : pairing (d : ℝ) δ.toReal δ.toReal < 0 := by rw [hv]; norm_num
  have hle := mul_pairing_self_le_sq hd' hvneg δ'.toReal
  have hne' : pairing (d : ℝ) δ.toReal δ'.toReal ^ 2 ≠
      pairing (d : ℝ) δ.toReal δ.toReal * pairing (d : ℝ) δ'.toReal δ'.toReal := by
    rw [Ne, sq_pairing_eq_iff hd' (by rw [hv]; norm_num)]
    rintro ⟨a, ha⟩
    -- `δ' = a δ` with both roots of positive rank forces `a = 1`
    have hrel : pairing (d : ℝ) δ'.toReal δ'.toReal =
        a ^ 2 * pairing (d : ℝ) δ.toReal δ.toReal := by
      rw [ha, pairing_smul_left, pairing_smul_right]; ring
    rw [hv, hv'] at hrel
    have ha2 : a ^ 2 = 1 := by linarith
    have hapos : 0 < a := by
      have := congrArg MukaiVector.r ha
      simp only [toReal_r, smul_r] at this
      have h1 : (0 : ℝ) < δ'.r := by exact_mod_cast hr'
      have h2 : (0 : ℝ) < δ.r := by exact_mod_cast hr
      rw [this] at h1
      exact pos_of_mul_pos_left h1 h2.le
    have ha1 : a = 1 := by nlinarith
    have : δ'.toReal = δ.toReal := by rw [ha, ha1]; ext <;> simp
    exact hne (toReal_injective this).symm
  rw [hv, hv'] at hle hne'
  rw [pairing_toReal] at hneg hle hne'
  have hlt : (4 : ℝ) < ((pairing d δ δ' : ℤ) : ℝ) ^ 2 := by
    rcases hle.lt_or_eq with h | h
    · linarith
    · exact absurd h.symm (by norm_num at hne' ⊢; exact hne')
  have hlt' : (4 : ℤ) < pairing d δ δ' ^ 2 := by exact_mod_cast hlt
  have hneg' : pairing d δ δ' < 0 := by exact_mod_cast hneg
  nlinarith

end MukaiVector
