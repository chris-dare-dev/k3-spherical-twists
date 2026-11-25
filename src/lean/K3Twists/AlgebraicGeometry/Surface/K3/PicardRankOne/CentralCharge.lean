/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.Lattice.Mukai.CentralCharge
import K3Twists.LinearAlgebra.Lattice.Mukai.PicardRankOne
import K3Twists.LinearAlgebra.Lattice.Mukai.Slice
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity

/-!
# Central charges and the half-turn of a twist

For `z = b + ia` in the upper half-plane the geometric stability condition `σ_z` of a K3 surface
with `Pic = ℤH`, `H² = 2d`, has central charge `Z_z(E) = ⟨exp(zH), v(E)⟩`, which in the
coordinates of `MukaiVector` is

  `Z_z(r, c, s) = 2dcz - s - drz²`.

This file proves the exact identities of the article's sections on a single point and on the
geometry of the next wall:

* `charge_kernel`: `Z_z` vanishes on the kernel line `κ = (1, b, d(b² + a²))`, which identifies
  the half-plane with the region `t > b²` of the projective model, `t = b² + a²`;
* `charge_eq_mukaiCharge`: `Z_z` is the Mukai charge `Mukai.charge` at the exponential point
  `e^{zH}` of the rank-one Mukai lattice, on the slice of `H`;
* `charge_halfTurn`: for a spherical class `δ = (r, c, s)` of slope `m = c/r` and
  `k = 1/(dr²)`, the twist `T_δ` and the base map `f(z) = m - k/(z - m)` satisfy
  `Z_{f(z)}(T_δ v) = -k Z_z(v)/(z - m)²`; `f` is an involution of the upper half-plane
  (`halfTurn_halfTurn`, `im_halfTurn`). The coordinate-free statement is
  `Mukai.charge_halfTurn_of_isometry`, for any isometry; `f(z)` is the coordinate of the image
  point `ρ_δ(e^{zH})` on the slice (`reflect_expSlice_halfTurn`);
* the opening example at `d = 1`, `z = (1 + 4i)/3`: `Z(𝒪_x) = -1`,
  `Z(𝒪_X[1]) = -2/3 + 8i/9`, so `m(T𝒪_x) = 19/9` and `m(T⁻¹𝒪_x) = 17/9`, and
  `m(Tⁿ𝒪_x) = 1 + 10n/9`;
* `opening_segment_clear`: no puncture lies on the segment from the cusp `0` of `T⁻¹𝒪_x` to the
  base point, which is the visibility check of the opening example.
-/

namespace AlgebraicGeometry.K3.PicardRankOne

open Complex

/-- The central charge `Z_z(v) = 2dcz - s - drz²` of the geometric stability condition at `z`,
that is `Z_z(E) = ⟨exp(zH), v(E)⟩` for `H² = 2d`. -/
def charge (d z : ℂ) (v : MukaiVector ℂ) : ℂ :=
  2 * d * v.c * z - v.s - d * v.r * z ^ 2

lemma charge_add (d z : ℂ) (v w : MukaiVector ℂ) :
    charge d z (v + w) = charge d z v + charge d z w := by
  simp only [charge, MukaiVector.add_r, MukaiVector.add_c, MukaiVector.add_s]; ring

lemma charge_neg (d z : ℂ) (v : MukaiVector ℂ) : charge d z (-v) = -charge d z v := by
  simp only [charge, MukaiVector.neg_r, MukaiVector.neg_c, MukaiVector.neg_s]; ring

lemma charge_smul (d z a : ℂ) (v : MukaiVector ℂ) : charge d z (a • v) = a * charge d z v := by
  simp only [charge, MukaiVector.smul_r, MukaiVector.smul_c, MukaiVector.smul_s]; ring

/-- **The charge of Picard rank one is a Mukai charge.** `Z_z(v) = ⟪e^{zH}, v⟫` in the Mukai
lattice `MukaiLattice ℂ ℂ` of the rank-one lattice `(ℂ, 2dxy)`, with `v` on the slice of `H`. -/
theorem charge_eq_mukaiCharge (d z : ℂ) (v : MukaiVector ℂ) :
    charge d z v =
      Mukai.charge (Mukai.rankOneForm d) (Mukai.expSlice 1 d z) (Mukai.slice 1 v) := by
  rw [Mukai.charge, Mukai.mukaiForm_expSlice_slice (Mukai.rankOneForm_one_one d), charge]

/-- A point has central charge `-1` at every `z`: `Z_z(𝒪_x) = -1`. -/
@[simp] lemma charge_point (d z : ℂ) : charge d z MukaiVector.point = -1 := by
  simp [charge, MukaiVector.point]

/-- The kernel line. At `z = b + ia` the central charge vanishes on `κ = (1, b, d(b² + a²))`.
In the coordinates `(b, t)`, `t = b² + a²`, the half-plane is the region `t > b²` above the
parabola of isotropic lines. -/
lemma charge_kernel (d b a : ℂ) : charge d (b + a * I) ⟨1, b, d * (b ^ 2 + a ^ 2)⟩ = 0 := by
  simp only [charge]
  linear_combination (-d * a ^ 2) * I_sq

/-! ### The half-turn of a twist -/

/-- The base map of a twist about a spherical object of class `δ = (r, c, s)`:
`z ↦ m - k/(z - m)` with slope `m = c/r` and `k = 1/(dr²)`. Both `T_δ` and `T_δ⁻¹` cover it;
their lifts to the universal cover are the two inverse half-turns about the puncture. -/
noncomputable def halfTurn (d : ℂ) (δ : MukaiVector ℂ) (z : ℂ) : ℂ :=
  δ.c / δ.r - 1 / (d * δ.r ^ 2) / (z - δ.c / δ.r)

/-- **The image point of the half-turn.** For a root `δ` with `r ≠ 0` and `z` off its slope `m`,
the reflection in the slice of `δ` sends `e^{zH}` to `-dr²(z - m)² · e^{f(z)H}`, where `f` is
`halfTurn`. So `f(z)` is the coordinate, on the slice, of the exponential chart point of
`ρ_δ(e^{zH})`, and `charge_halfTurn` is `Mukai.charge_halfTurn_of_isometry` read in this
coordinate. -/
theorem reflect_expSlice_halfTurn {d : ℂ} {δ : MukaiVector ℂ} (hδ : MukaiVector.IsRoot d δ)
    (hd : d ≠ 0) (hr : δ.r ≠ 0) {z : ℂ} (hz : z ≠ δ.c / δ.r) :
    Mukai.reflect (Mukai.rankOneForm d) (Mukai.slice 1 δ) (Mukai.expSlice 1 d z) =
      (-(d * δ.r ^ 2 * (z - δ.c / δ.r) ^ 2)) • Mukai.expSlice 1 d (halfTurn d δ z) :=
  Mukai.reflect_expSlice (Mukai.rankOneForm_one_one d) ((MukaiVector.isRoot_iff d δ).1 hδ) hr hd
    hz

/-- **The half-turn identity.** For a root `δ` with `r ≠ 0` and `z` off its slope,
`Z_{f(z)}(T_δ v) = -k · Z_z(v) / (z - m)²`, where `f` is `halfTurn`, `m = c/r` and
`k = 1/(dr²)`. So the twist carries the central charge at `z` to a rotated and rescaled central
charge at `f(z)`.

This is the explicit form, in the coordinate of the slice, of the coordinate-free half-turn
`Mukai.charge_halfTurn_of_isometry` (see `reflect_expSlice_halfTurn`); the direct computation
below is shorter than the route through the general statement. -/
theorem charge_halfTurn {d : ℂ} {δ : MukaiVector ℂ} (hδ : MukaiVector.IsRoot d δ) (hd : d ≠ 0)
    (hr : δ.r ≠ 0) {z : ℂ} (hz : z ≠ δ.c / δ.r) (v : MukaiVector ℂ) :
    charge d (halfTurn d δ z) (BilinearForm.reflect (MukaiVector.mukaiForm d) δ v) =
      -(1 / (d * δ.r ^ 2)) * charge d z v / (z - δ.c / δ.r) ^ 2 := by
  rw [MukaiVector.isRoot_iff] at hδ
  have hs : δ.s = (d * δ.c ^ 2 + 1) / δ.r := by
    field_simp
    linear_combination hδ
  obtain ⟨w, rfl⟩ : ∃ w, z = δ.c / δ.r + w := ⟨z - δ.c / δ.r, by ring⟩
  have hw : w ≠ 0 := by rintro rfl; exact hz (add_zero _)
  simp only [charge, halfTurn, MukaiVector.bilinearFormReflect_apply, MukaiVector.pairing,
    MukaiVector.add_r,
    MukaiVector.add_c, MukaiVector.add_s, MukaiVector.smul_r, MukaiVector.smul_c,
    MukaiVector.smul_s, hs, add_sub_cancel_left]
  field_simp
  ring

/-- The half-turn is an involution off the slope of its root. -/
theorem halfTurn_halfTurn {d : ℂ} {δ : MukaiVector ℂ} (hd : d ≠ 0) (hr : δ.r ≠ 0) {z : ℂ}
    (hz : z ≠ δ.c / δ.r) : halfTurn d δ (halfTurn d δ z) = z := by
  obtain ⟨w, rfl⟩ : ∃ w, z = δ.c / δ.r + w := ⟨z - δ.c / δ.r, by ring⟩
  have hw : w ≠ 0 := by rintro rfl; exact hz (add_zero _)
  simp only [halfTurn, add_sub_cancel_left, sub_sub_cancel_left]
  field_simp
  ring

/-- For real slope `m` and real `k`, the map `z ↦ m - k/(z - m)` has
`Im f(z) = k · Im z / |z - m|²`; for `k > 0` it preserves the upper half-plane. -/
theorem im_halfTurn (m k : ℝ) (z : ℂ) :
    ((m : ℂ) - k / (z - m)).im = k * z.im / normSq (z - m) := by
  simp [div_im]

theorem im_halfTurn_pos {m k : ℝ} (hk : 0 < k) {z : ℂ} (hz : 0 < z.im) :
    0 < ((m : ℂ) - k / (z - m)).im := by
  rw [im_halfTurn]
  have : 0 < normSq (z - m) := by
    rw [normSq_pos]
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  positivity

/-! ### The opening example: `d = 1`, `z = (1 + 4i)/3` -/

/-- The base point `z = (1 + 4i)/3` of the opening example. -/
noncomputable def ζ : ℂ := (1 + 4 * I) / 3

/-- `S = 𝒪_X[1]` has class `-v(𝒪_X) = -(1, 0, 1)`. -/
def classS : MukaiVector ℂ := -⟨1, 0, 1⟩

lemma opening_charge_S : charge 1 ζ classS = -2 / 3 + 8 / 9 * I := by
  simp only [charge, classS, ζ, MukaiVector.neg_r, MukaiVector.neg_c, MukaiVector.neg_s]
  linear_combination (16 / 9 : ℂ) * I_sq

lemma opening_norm_S : ‖charge 1 ζ classS‖ = 10 / 9 := by
  rw [opening_charge_S,
    show (-2 / 3 + 8 / 9 * I : ℂ) = ((-2 / 3 : ℝ) : ℂ) + ((8 / 9 : ℝ) : ℂ) * I by push_cast; ring,
    norm_add_mul_I, show ((-2 / 3 : ℝ)) ^ 2 + (8 / 9 : ℝ) ^ 2 = (10 / 9) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

/-- `m_z(T𝒪_x) = |Z(𝒪_x)| + |Z(𝒪_X[1])| = 19/9`: the filtration `𝒪_x ⊂ T𝒪_x` with quotient
`𝒪_X[1]` is the HN filtration on the side where the point has the larger phase. -/
lemma opening_mass_T : ‖charge 1 ζ MukaiVector.point‖ + ‖charge 1 ζ classS‖ = 19 / 9 := by
  rw [charge_point, norm_neg, norm_one, opening_norm_S]; norm_num

/-- `m_z(T⁻¹𝒪_x) = |Z(𝒪_x) + Z(𝒪_X[1])| = 17/9`: there `T⁻¹𝒪_x` is stable, and its mass is the
modulus of its central charge. Its Mukai vector equals that of `T𝒪_x`. -/
lemma opening_mass_Tinv : ‖charge 1 ζ MukaiVector.point + charge 1 ζ classS‖ = 17 / 9 := by
  rw [charge_point, opening_charge_S,
    show (-1 + (-2 / 3 + 8 / 9 * I) : ℂ) = ((-5 / 3 : ℝ) : ℂ) + ((8 / 9 : ℝ) : ℂ) * I by
      push_cast; ring,
    norm_add_mul_I, show ((-5 / 3 : ℝ)) ^ 2 + (8 / 9 : ℝ) ^ 2 = (17 / 9) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

/-- `T𝒪_x` and `T⁻¹𝒪_x` have the same Mukai vector, the reflection of `v(𝒪_x)` in `v(𝒪_X)`:
`v(𝒪_x) + v(𝒪_X[1]) = (-1, 0, 0)`. Only the direction of the extension tells them apart. -/
lemma opening_same_class :
    BilinearForm.reflect (MukaiVector.mukaiForm (1 : ℂ)) ⟨1, 0, 1⟩ MukaiVector.point =
        MukaiVector.point + classS ∧
      MukaiVector.point + classS = (⟨-1, 0, 0⟩ : MukaiVector ℂ) := by
  constructor <;> ext <;>
    simp [MukaiVector.bilinearFormReflect_apply, MukaiVector.pairing, MukaiVector.point, classS]

/-- `m_z(Tⁿ𝒪_x) = 1 + 10n/9`: the HN factors of `Tⁿ𝒪_x` at the base point are `𝒪_x` and the
`n` shifts `𝒪_X[1 - j]`, `0 ≤ j < n`, each of mass `|Z(𝒪_X)| = 10/9`. -/
lemma opening_mass_Tpow (n : ℕ) :
    ‖charge 1 ζ MukaiVector.point‖ + n * ‖charge 1 ζ classS‖ = 1 + 10 * n / 9 := by
  rw [charge_point, norm_neg, norm_one, opening_norm_S]; ring

/-- **Visibility in the opening example.** Take `d = 1` and the base point `b + 4i/3` with
`0 < b ≤ 1/3`, which is `(b, b² + 16/9)` in the coordinates `(b, t)`. The cusp of `T⁻¹𝒪_x` is
`0`. Every puncture `(c/r, s/r)` of a root of positive rank whose abscissa lies in `(0, b]` is
strictly below the segment from `0` to the base point, so it does not obstruct the segment: the
slope of the segment is at least `16/3` and the slope of the puncture is `c/r + 1/(cr) ≤ 4/3`. -/
theorem opening_segment_clear {b : ℝ} (hb0 : 0 < b) (hb : b ≤ 1 / 3) {r c s : ℤ} (hr : 0 < r)
    (hroot : r * s = c ^ 2 + 1) (hy0 : 0 < (c : ℝ) / r) (hyb : (c : ℝ) / r ≤ b) :
    (s : ℝ) / r < (b ^ 2 + 16 / 9) / b * ((c : ℝ) / r) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hc' : (0 : ℝ) < c := by
    have := mul_pos hy0 hr'
    rwa [div_mul_cancel₀ _ hr'.ne'] at this
  have hc1 : (1 : ℝ) ≤ c := by
    have : (0 : ℤ) < c := by exact_mod_cast hc'
    exact_mod_cast this
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hroot' : (r : ℝ) * s = c ^ 2 + 1 := by exact_mod_cast hroot
  set y := (c : ℝ) / r with hy
  -- the slope of the segment is at least `16/3`
  have hslope : 16 / 3 ≤ (b ^ 2 + 16 / 9) / b := by
    rw [le_div_iff₀ hb0]
    nlinarith
  -- the puncture is at `t = y (y + 1/(cr))` with `y + 1/(cr) ≤ 4/3`
  have hs : (s : ℝ) / r = y * (y + 1 / (c * r)) := by
    rw [hy]
    field_simp
    linear_combination hroot'
  have hcr : 1 / ((c : ℝ) * r) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  rw [hs]
  have hy13 : y ≤ 1 / 3 := hyb.trans hb
  calc y * (y + 1 / (c * r)) ≤ y * (4 / 3) := by
        apply mul_le_mul_of_nonneg_left _ hy0.le; linarith
    _ < (16 / 3) * y := by linarith
    _ ≤ (b ^ 2 + 16 / 9) / b * y := by
        apply mul_le_mul_of_nonneg_right hslope hy0.le

end AlgebraicGeometry.K3.PicardRankOne
