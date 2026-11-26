/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.PicardRankOne.CentralCharge
import K3Twists.AlgebraicGeometry.Surface.K3.PicardRankOne.EulerMass
import K3Twists.CategoryTheory.MassProfile.LargeVolume

/-!
# The large-volume limit on the classes of Picard rank one

This file builds `LargeVolumeHypotheses` from the classes of a K3 surface `X` with `Pic X = ℤH`,
`H² = 2d`, `d > 0`:

* objects are formal direct sums of Mukai vectors (`ClassSum`), on which the isometries of the
  Mukai lattice act summand by summand;
* a point of the space is a charge `Z` on classes, the isometries acting by `(g • Z)(x) = Z(g⁻¹ x)`,
  and the mass of a sum is `Σ |Z(x)|` over its summands: the mass of a direct sum of semistable
  objects of those classes;
* the ray is the geometric charge at `z = it`,
  `Z_t(r, c, s) = 2dc(it) - s - dr(it)² = d r t² - s + 2dct i` (`charge d (t * I)`), with scale
  `d t²`;
* `R` is the sum of the absolute ranks of the summands.

Then `Z_t(x) / (d t²) → rk x` (`tendsto_charge_div`), so the field `tendsto_mass` holds, and `R` is
additive on the generator `𝒪_X ⊕ 𝒪_X(H) ⊕ 𝒪_X(2H)` (`lineGenerator`). With
`LargeVolumeHypotheses.tendsto_mass_generator_smul` this gives, on classes,
`m_{Wσ_t}(G) / (d t²) → Σ_i |rk(W⁻¹ v(𝒪_X(iH)))|`.

**What is not geometric.** The masses here are those of direct sums of semistable objects of the
given classes. For an arbitrary object of `D^b(X)` the limit is the field `tendsto_mass` itself,
whose inputs are the derived category of `X` and its stability conditions, which Mathlib does not
have.

## Main definitions

* `AlgebraicGeometry.K3.PicardRankOne.ClassCharge`: charges on classes, with the isometries acting.
* `AlgebraicGeometry.K3.PicardRankOne.largeVolume d hd`: the instance of `LargeVolumeHypotheses`.
-/

noncomputable section

open Filter Topology Complex
open scoped NNReal

namespace AlgebraicGeometry.K3.PicardRankOne

open MukaiVector ClassSum

variable (d : ℤ)

/-- Charges on the integral Mukai vectors. -/
def ClassCharge : Type := MukaiVector ℤ → ℂ

/-- The isometries act on charges by `(g • Z)(x) = Z(g⁻¹ x)`. -/
instance : MulAction (mukaiIsometries d) ClassCharge := arrowAction

/-- The complex class of an integral Mukai vector. -/
def toComplex (x : MukaiVector ℤ) : MukaiVector ℂ := ⟨x.r, x.c, x.s⟩

/-- The mass of a direct sum of semistable objects of the classes of `U` at the charge `Z`:
`Σ |Z(x)|` over the summands. -/
def sumMass (Z : ClassCharge) (U : ClassSum) : ℝ≥0 :=
  (U.toMultiset.map fun x ↦ ‖Z x‖₊).sum

/-- The sum of the absolute ranks of the summands. -/
def sumRank (U : ClassSum) : ℝ≥0 :=
  (U.toMultiset.map fun x ↦ ((x.r.natAbs : ℕ) : ℝ≥0)).sum

/-- The geometric charge at `z = it`: `Z_t(r, c, s) = d r t² - s + 2dct i`. -/
def rayCharge (t : ℝ) : ClassCharge := fun x ↦ charge (d : ℂ) (t * I) (toComplex x)

lemma rayCharge_apply (t : ℝ) (x : MukaiVector ℤ) :
    rayCharge d t x = (d : ℂ) * x.r * t ^ 2 - x.s + 2 * d * x.c * t * I := by
  simp only [rayCharge, charge, toComplex]
  linear_combination (-(d : ℂ) * x.r * t ^ 2) * I_sq

/-- **The charge at large volume.** `Z_t(x) / (d t²) → rk x` as `t → ∞`. -/
theorem tendsto_charge_div (hd : 0 < d) (x : MukaiVector ℤ) :
    Tendsto (fun t : ℝ ↦ rayCharge d t x / ((d : ℂ) * t ^ 2)) atTop (𝓝 (x.r : ℂ)) := by
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hinv : Tendsto (fun t : ℝ ↦ ((t : ℂ))⁻¹) atTop (𝓝 0) := by
    have := (continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
    simpa [Function.comp_def] using this
  have hlim : Tendsto (fun t : ℝ ↦ (x.r : ℂ) - x.s / d * ((t : ℂ))⁻¹ ^ 2 +
      2 * x.c * I * ((t : ℂ))⁻¹) atTop (𝓝 ((x.r : ℂ) - x.s / d * 0 ^ 2 + 2 * x.c * I * 0)) :=
    (tendsto_const_nhds.sub (tendsto_const_nhds.mul (hinv.pow 2))).add
      (tendsto_const_nhds.mul hinv)
  simp only [zero_pow two_ne_zero, mul_zero, sub_zero, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  rw [rayCharge_apply]
  field_simp

/-- The scale `d t²` of the ray. -/
def rayScale (t : ℝ) : ℝ≥0 := Real.toNNReal (d * t ^ 2)

/-- `|Z_t(x)| / (d t²) → |rk x|`. -/
theorem tendsto_norm_charge_div (hd : 0 < d) (x : MukaiVector ℤ) :
    Tendsto (fun t : ℝ ↦ (rayScale d t)⁻¹ * ‖rayCharge d t x‖₊) atTop
      (𝓝 ((x.r.natAbs : ℕ) : ℝ≥0)) := by
  rw [← NNReal.tendsto_coe]
  have h := (tendsto_charge_div d hd x).norm
  have hr : ‖(x.r : ℂ)‖ = (((x.r.natAbs : ℕ) : ℝ≥0) : ℝ) := by
    rw [Complex.norm_intCast, NNReal.coe_natCast, Nat.cast_natAbs, Int.cast_abs]
  rw [hr] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have hpos : (0 : ℝ) < d * t ^ 2 := by positivity
  rw [norm_div, norm_mul, Complex.norm_intCast, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by exact_mod_cast hd : (0 : ℝ) < d), sq_abs, NNReal.coe_mul, NNReal.coe_inv,
    rayScale, Real.coe_toNNReal _ hpos.le, coe_nnNorm, div_eq_inv_mul]

/-- **The large-volume instance on classes.** -/
def largeVolume (hd : 0 < d) :
    LargeVolumeHypotheses ClassSum (mukaiIsometries d) ClassCharge (Fin 3) where
  mass := fun Z ↦ Profile.ofFun (sumMass Z)
  mass_smul g Z := Profile.ext fun U ↦ by
    change sumMass (g • Z) U = sumMass Z (g⁻¹ • U)
    simp only [sumMass, smul_toMultiset, Multiset.map_map, Function.comp_def]
    rfl
  ray := rayCharge d
  scale := rayScale d
  rank := Profile.ofFun sumRank
  tendsto_mass U := by
    change Tendsto (fun t ↦ (rayScale d t)⁻¹ * sumMass (rayCharge d t) U) atTop (𝓝 (sumRank U))
    simp only [sumMass, sumRank]
    induction U.toMultiset using Multiset.induction_on with
    | empty => simp
    | cons x s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, mul_add]
      exact (tendsto_norm_charge_div d hd x).add ih
  G := lineGenerator d
  S i := single (lineTriple d i)
  rank_smul_G g := by
    change sumRank (g • lineGenerator d) = ∑ i, sumRank (g • single (lineTriple d i))
    simp [sumRank, lineGenerator, smul_toMultiset, single, Fin.sum_univ_three, add_assoc]

end AlgebraicGeometry.K3.PicardRankOne
