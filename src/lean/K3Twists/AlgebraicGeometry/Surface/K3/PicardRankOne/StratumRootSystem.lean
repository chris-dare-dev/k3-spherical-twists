/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.PicardRankOne.SupportProperty
import K3Twists.LinearAlgebra.RootSystem.Stratum

/-!
# The root systems of the strata in Picard rank one

Let `X` be a K3 surface with `Pic X = ℤH`, `H² = 2d > 0`, and let `p = (b, t)` lie above the
parabola `b² < t` of the projective model, where the central charge `Z_p` vanishes exactly on the
real line of the kernel vector `κ_p = (1, b, dt)` (`modelCharge_eq_zero_iff`). On integral
classes `Z_p` is an additive map `modelChargeInt d p`, and the Mukai form is negative on the
nonzero integral points of its kernel (`negDef_ker_modelChargeInt`): `κ_p` has square
`-2d(t - b²) < 0`. So every point above the parabola has a kernel root system over `ℤ` and over
`ℚ` (`RootPairing.kernelRootPairing`, `RootPairing.kernelRootSystem`).

**Every stratum is `A₁`.** If a root `δ` has `Z_p(δ) = 0`, the kernel roots are exactly `±δ`
(`kernelRoots_modelChargeInt`, from `eq_or_eq_neg_of_modelCharge_eq_zero`), so

* `stratumRootPairingBase`: `{δ}` is a base of the kernel root pairing over `ℤ`, with Cartan matrix
  `(2)` (`cartanMatrix_stratumRootPairingBase`);
* `stratumRootSystemBase`: `{1 ⊗ δ}` is a base of the root system of the stratum over `ℚ`, a Mathlib
  `IsRootSystem`.

These are lattice statements: that `Z_p` is the central charge of a stability condition is not
formalized.
-/

namespace AlgebraicGeometry.K3.PicardRankOne

open Mukai MukaiVector RootPairing

/-- The integral Mukai vectors form a free `ℤ`-module, through the coordinates `(r, c, s)`. -/
instance instModuleFreeIntMukaiVector : Module.Free ℤ (MukaiVector ℤ) :=
  Module.Free.of_equiv (MukaiVector.toMukaiLatticeEquiv (R := ℤ)).symm

/-- The integral Mukai vectors form a finitely generated `ℤ`-module. -/
instance instModuleFiniteIntMukaiVector : Module.Finite ℤ (MukaiVector ℤ) :=
  Module.Finite.equiv (MukaiVector.toMukaiLatticeEquiv (R := ℤ)).symm

lemma toReal_add (v w : MukaiVector ℤ) : (v + w).toReal = v.toReal + w.toReal := by
  ext <;> simp

/-- The central charge `Z_p` on integral classes, as an additive map. -/
noncomputable def modelChargeInt (d : ℝ) (p : ℝ × ℝ) : MukaiVector ℤ →+ ℂ where
  toFun v := modelCharge d p v.toReal
  map_zero' := by
    have : (0 : MukaiVector ℤ).toReal = 0 := by ext <;> simp
    rw [this, show (0 : MukaiVector ℝ) = (0 : ℝ) • (0 : MukaiVector ℝ) by simp, modelCharge_smul,
      Complex.ofReal_zero, zero_mul]
  map_add' v w := by rw [toReal_add, modelCharge_add]

@[simp]
lemma modelChargeInt_apply (d : ℝ) (p : ℝ × ℝ) (v : MukaiVector ℤ) :
    modelChargeInt d p v = modelCharge d p v.toReal :=
  rfl

/-- **The Mukai form is negative on the integral points of the kernel** above the parabola: a
nonzero integral `v` with `Z_p(v) = 0` is `r κ_p` with `r ≠ 0`, of square `-2dr²(t - b²)`. -/
theorem negDef_ker_modelChargeInt {d : ℤ} (hd : 0 < d) {p : ℝ × ℝ} (hp : p.1 ^ 2 < p.2)
    (v : MukaiVector ℤ) (hv : modelChargeInt d p v = 0) (hv0 : v ≠ 0) :
    mukaiForm d v v < 0 := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hκ := (modelCharge_eq_zero_iff hd' hp v.toReal).mp hv
  have hr : (v.r : ℝ) ≠ 0 := by
    intro h0
    apply hv0
    apply toReal_injective
    rw [hκ, toReal_r, h0, zero_smul]
    ext <;> simp
  have hsq : ((MukaiVector.pairing d v v : ℤ) : ℝ) =
      (v.r : ℝ) ^ 2 * (-2 * d * (p.2 - p.1 ^ 2)) := by
    rw [← MukaiVector.pairing_toReal, hκ, toReal_r, MukaiVector.pairing_smul_left,
      MukaiVector.pairing_smul_right, MukaiVector.pairing_kernelVector_self]
    ring
  have hneg : (v.r : ℝ) ^ 2 * (-2 * d * (p.2 - p.1 ^ 2)) < 0 := by
    have h1 : 0 < (v.r : ℝ) ^ 2 := by positivity
    have h2 : (0 : ℝ) < d := by exact_mod_cast hd
    have h3 : 0 < p.2 - p.1 ^ 2 := by linarith
    have h4 : 0 < (v.r : ℝ) ^ 2 * ((d : ℝ) * (p.2 - p.1 ^ 2)) := mul_pos h1 (mul_pos h2 h3)
    have : (v.r : ℝ) ^ 2 * (-2 * d * (p.2 - p.1 ^ 2)) =
        -2 * ((v.r : ℝ) ^ 2 * ((d : ℝ) * (p.2 - p.1 ^ 2))) := by ring
    rw [this]
    linarith
  rw [MukaiVector.mukaiForm_apply]
  have : ((MukaiVector.pairing d v v : ℤ) : ℝ) < 0 := hsq ▸ hneg
  exact_mod_cast this

/-- **Every stratum is `A₁`**: if a root `δ` has `Z_p(δ) = 0` above the parabola, the kernel roots
are exactly `±δ`. -/
theorem kernelRoots_modelChargeInt {d : ℤ} (hd : 0 < d) {p : ℝ × ℝ} (hp : p.1 ^ 2 < p.2)
    {δ : MukaiVector ℤ} (hδ : IsRoot d δ) (hZ : modelCharge d p δ.toReal = 0) :
    kernelRoots (mukaiForm d) (modelChargeInt d p) = {δ, -δ} := by
  ext v
  constructor
  · rintro ⟨hv, hZv⟩
    exact eq_or_eq_neg_of_modelCharge_eq_zero hd hp hδ hv hZ hZv
  · rintro (rfl | rfl)
    · exact ⟨hδ, hZ⟩
    · refine ⟨?_, ?_⟩
      · change MukaiVector.pairing d (-δ) (-δ) = -2
        rw [MukaiVector.pairing_neg_left, MukaiVector.pairing_neg_right, neg_neg]
        exact hδ
      · rw [map_neg, modelChargeInt_apply, hZ, neg_zero]

/-- **The base of a stratum over `ℤ`**: `{δ}`. -/
noncomputable def stratumRootPairingBase {d : ℤ} (hd : 0 < d) {p : ℝ × ℝ} (hp : p.1 ^ 2 < p.2)
    {δ : MukaiVector ℤ} (hδ : IsRoot d δ) (hZ : modelCharge d p δ.toReal = 0) :
    (kernelRootPairing (mukaiForm_comm d) (negDef_ker_modelChargeInt hd hp)).Base :=
  kernelRootPairingBaseOfEq _ _ (kernelRoots_modelChargeInt hd hp hδ hZ)

/-- **The Cartan matrix of a stratum is `(2)`**: type `A₁`. -/
theorem cartanMatrix_stratumRootPairingBase {d : ℤ} (hd : 0 < d) {p : ℝ × ℝ}
    (hp : p.1 ^ 2 < p.2) {δ : MukaiVector ℤ} (hδ : IsRoot d δ)
    (hZ : modelCharge d p δ.toReal = 0) (i j : (stratumRootPairingBase hd hp hδ hZ).support) :
    (stratumRootPairingBase hd hp hδ hZ).cartanMatrix i j = 2 :=
  cartanMatrix_kernelRootPairingBaseOfEq _ _ _ i j

/-- **The base of a stratum over `ℚ`**: `{1 ⊗ δ}`, in the Mathlib root system of the stratum. -/
noncomputable def stratumRootSystemBase {d : ℤ} (hd : 0 < d) {p : ℝ × ℝ} (hp : p.1 ^ 2 < p.2)
    {δ : MukaiVector ℤ} (hδ : IsRoot d δ) (hZ : modelCharge d p δ.toReal = 0) :
    (kernelRootSystem (mukaiForm_comm d) (negDef_ker_modelChargeInt hd hp)).Base :=
  kernelRootSystemBaseOfEq _ _ (kernelRoots_modelChargeInt hd hp hδ hZ)

/-- The structure sheaf gives a stratum: `Z_p(𝒪_X) = 0` at `p = (0, 1/d)`, above the parabola. -/
theorem modelCharge_lineBundle_zero {d : ℤ} (hd : 0 < d) :
    modelCharge d (0, 1 / d) (lineBundle d 0 : MukaiVector ℤ).toReal = 0 := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hp : ((0 : ℝ) , 1 / (d : ℝ)).1 ^ 2 < ((0 : ℝ), 1 / (d : ℝ)).2 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity
  rw [modelCharge_eq_zero_iff hd' hp]
  ext <;> simp [lineBundle_zero, kernelVector, hd']

end AlgebraicGeometry.K3.PicardRankOne
