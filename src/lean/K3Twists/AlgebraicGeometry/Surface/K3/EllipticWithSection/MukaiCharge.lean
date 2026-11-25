/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.EllipticWithSection.CurveWall
import K3Twists.LinearAlgebra.Lattice.Mukai.CentralCharge

/-!
# The charge of the curve wall as a Mukai charge

The central charge `charge` of the curve wall (`EllipticWithSection/CurveWall.lean`), the charge
of Tramel and Xia (arXiv:1702.06252) at `H = C + 2F`, `β = -C/4`, `z = 2 - i`, is a central
charge `Z_Ω = ⟪Ω, ·⟫` of the Mukai lattice in the sense of `Lattice/Mukai/CentralCharge.lean`:
on the complexified lattice `MukaiLattice ℂ (NS ⊗ ℂ)`,

```
Z(v) = ⟪Ω, v⟫,   Ω = (1, β + iH, -3 + i)        (charge_eq_mukaiCharge).
```

The class `Ω` has `Ω² = 31/8 - 2i ≠ 0` (`selfPairing_chargeClass`), so this charge is not of the
exponential form `⟪exp(B + iω), ·⟫`, whose classes are isotropic. It is a `GL₂⁺(ℝ)`-translate of
one (`mukaiCharge_expClass`): with `B = C/4 + F` and `ω = (√43/4) H`,

```
⟪exp(B + iω), v⟫ = Re Z(v) + (1/2 + i √43/4) Im Z(v),
```

that is `Z_{exp(B+iω)} = g ∘ Z` for the real-linear map `g` of matrix `[[1, 1/2], [0, √43/4]]`,
of determinant `√43/4 > 0`. The two charges span the same real plane of classes,
`Re Ω' = Re Ω + Im Ω/2` and `Im Ω' = (√43/4) Im Ω`. This is the form in which the geometric
charges of a K3 surface are classified: up to the action of `GL₂⁺(ℝ)`, a charge `⟪exp(B + iω), ·⟫`
with `ω` ample (Bridgeland, *Stability conditions on K3 surfaces*, arXiv:math/0307164).

The base change from `MukaiLattice ℤ NS` to the complexified lattice is written out in
coordinates (`toComplex`).
-/

namespace AlgebraicGeometry.K3.EllipticWithSection

open Complex Mukai

/-! ### The complexified Mukai lattice -/

/-- The intersection form on `NS ⊗ ℂ = ℂC ⊕ ℂF`: `(a, b)·(a', b') = -2aa' + ab' + a'b`. -/
noncomputable def intersectionComplex : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun x y => -2 * x.1 * y.1 + x.1 * y.2 + x.2 * y.1)
    (fun x y z => by simp only [Prod.fst_add, Prod.snd_add]; ring)
    (fun c x y => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)
    (fun x y z => by simp only [Prod.fst_add, Prod.snd_add]; ring)
    (fun c x y => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)

@[simp]
lemma intersectionComplex_apply (x y : ℂ × ℂ) :
    intersectionComplex x y = -2 * x.1 * y.1 + x.1 * y.2 + x.2 * y.1 :=
  rfl

/-- An integral Mukai vector as a vector of the complexified Mukai lattice. -/
def toComplex (v : MukaiLattice ℤ NS) : MukaiLattice ℂ (ℂ × ℂ) :=
  ((v.1 : ℂ), ((v.2.1.1 : ℂ), (v.2.1.2 : ℂ)), (v.2.2 : ℂ))

/-- The base change preserves the Mukai form. -/
lemma mukaiForm_toComplex (v w : MukaiLattice ℤ NS) :
    mukaiForm intersectionComplex (toComplex v) (toComplex w) =
      ((pairing intersection v w : ℤ) : ℂ) := by
  simp [toComplex, pairing]

/-! ### The charge of the curve wall -/

/-- The class `Ω = (1, β + iH, -3 + i)` with `β = -C/4` and `H = C + 2F`, that is
`β + iH = (-1/4 + i)C + 2i F`. -/
noncomputable def chargeClass : MukaiLattice ℂ (ℂ × ℂ) := (1, (-1 / 4 + I, 2 * I), -3 + I)

/-- **The curve-wall charge is a Mukai charge**: `Z(v) = ⟪Ω, v⟫`. -/
theorem charge_eq_mukaiCharge (v : MukaiLattice ℤ NS) :
    charge v = Mukai.charge intersectionComplex chargeClass (toComplex v) := by
  obtain ⟨r, ⟨a, b⟩, s⟩ := v
  simp [charge_apply, chargeClass, toComplex, pairing, curve, polarization]
  ring

/-- `Ω² = 31/8 - 2i`: the charge class is not isotropic, so the charge is not of exponential
form. -/
theorem selfPairing_chargeClass : selfPairing intersectionComplex chargeClass = 31 / 8 - 2 * I := by
  simp only [chargeClass, selfPairing_mk, intersectionComplex_apply]
  ring_nf
  rw [I_sq]
  ring

theorem not_isIsotropic_chargeClass : ¬IsIsotropic intersectionComplex chargeClass := by
  rw [IsIsotropic, selfPairing_chargeClass]
  intro h
  have := congrArg Complex.im h
  norm_num at this

/-! ### An exponential charge in its `GL₂⁺(ℝ)`-orbit -/

/-- `√43/4`, the multiple of `H` in `ω`. -/
noncomputable def omegaScale : ℝ := √43 / 4

lemma omegaScale_pos : 0 < omegaScale := by
  unfold omegaScale
  positivity

lemma omegaScale_sq : (omegaScale : ℂ) ^ 2 = 43 / 16 := by
  have h : omegaScale ^ 2 = 43 / 16 := by
    rw [omegaScale, div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [← ofReal_pow, h]
  push_cast
  ring

/-- `B + iω` with `B = C/4 + F` and `ω = (√43/4) H`, `H = C + 2F`. -/
noncomputable def expCoord : ℂ × ℂ := (1 / 4 + I * omegaScale, 1 + 2 * I * omegaScale)

/-- The exponential class `exp(B + iω) = (1, B + iω, (B + iω)²/2)`. -/
noncomputable def expClass : MukaiLattice ℂ (ℂ × ℂ) :=
  (1, expCoord, intersectionComplex expCoord expCoord / 2)

theorem isIsotropic_expClass : IsIsotropic intersectionComplex expClass := by
  simp only [IsIsotropic, expClass, selfPairing_mk]
  ring

/-- **The curve-wall charge is a `GL₂⁺(ℝ)`-translate of an exponential charge.** With
`B = C/4 + F` and `ω = (√43/4) H`,
`⟪exp(B + iω), v⟫ = Re Z(v) + (1/2 + i √43/4) Im Z(v)`: the real-linear map
`x + iy ↦ x + y/2 + i (√43/4) y`, of determinant `√43/4 > 0` (`omegaScale_pos`), carries `Z` to
the exponential charge. -/
theorem mukaiCharge_expClass (v : MukaiLattice ℤ NS) :
    Mukai.charge intersectionComplex expClass (toComplex v) =
      (charge v).re + (1 / 2 + I * omegaScale) * (charge v).im := by
  rw [re_charge, im_charge]
  obtain ⟨r, ⟨a, b⟩, s⟩ := v
  simp [expClass, expCoord, toComplex, pairing, curve, polarization]
  linear_combination (r : ℂ) * omegaScale_sq - (omegaScale : ℂ) ^ 2 * r * I_sq

end AlgebraicGeometry.K3.EllipticWithSection
