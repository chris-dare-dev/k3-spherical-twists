/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.Lattice.Mukai.Reflection

/-!
# Central charges on the Mukai lattice and the half-turn of an isometry

For a class `Ω` of the Mukai lattice `MukaiLattice R N`, the **central charge** at `Ω` is the
linear form

```
Z_Ω(v) = ⟪Ω, v⟫.
```

**Sign convention.** The charge is `+⟪Ω, v⟫`, with the Mukai form
`⟪(r, c, s), (r', c', s')⟫ = b c c' - r s' - r' s`. At an exponential point `Ω = (1, x, t)` the
class of a point `(0, 0, 1)` has charge `Z_Ω(0, 0, 1) = -1` (`charge_corankUnit`), and in Picard
rank one `Z_{e^{zH}}(r, c, s) = 2dcz - s - drz²` (`Mukai.mukaiForm_expSlice_slice`). With
`χ(E, F) = -⟪v(E), v(F)⟫` on a K3 surface, this is the charge `Z(E) = ⟨exp(zH), v(E)⟩` of
Bridgeland's geometric stability conditions (Bridgeland, arXiv:math/0307164, §6).

## The half-turn of an isometry

An isometry `ρ` of the Mukai lattice moves charges by `Z_Ω ∘ ρ = Z_{ρ⁻¹Ω}`, and the useful form
of that statement needs neither an inverse nor an involution (`mul_charge_of_apply_eq_smul`): if
a linear map `ρ` preserves the form and `ρ Ω = f • Ω'`, then `f · Z_{Ω'}(ρ v) = Z_Ω(v)`.

Over a field, a class of nonzero rank `r` is `r` times the point `expChart v = (1, x/r, t/r)`
(`eq_fst_smul_expChart`), which is an exponential point `(1, x', b(x', x')/2)` exactly when `v` is
isotropic (`two_mul_expChart_snd_snd`). Together these give the **coordinate-free half-turn**
(`charge_halfTurn_of_isometry`): for every linear isometry `ρ` and every isotropic `Ω` with
`ρ Ω` of nonzero rank,

```
(ρ Ω).rank · Z_{expChart(ρ Ω)}(ρ v) = Z_Ω(v).
```

No symmetry of `b`, no inverse and no Picard-rank hypothesis enter. In Picard rank one the image
point is again on the slice of the polarization, and its coordinate is the Möbius map of the
explicit half-turn identity `AlgebraicGeometry.K3.PicardRankOne.charge_halfTurn`; in higher Picard
rank the image leaves the slice, and only this statement carries over.

## Main results

* `charge` — `Z_Ω = ⟪Ω, ·⟫` as a linear form.
* `mul_charge_of_apply_eq_smul` — the rescaled master lemma.
* `charge_reflect` — `Z_Ω ∘ ρ_s = Z_{ρ_s Ω}` for a spherical `s` and symmetric `b`.
* `eq_fst_smul_expChart`, `isIsotropic_expChart` — the exponential chart of the isotropic quadric.
* `charge_halfTurn_of_isometry` — the coordinate-free half-turn.
-/

namespace Mukai

section CommRing

variable {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N]
variable (b : N →ₗ[R] N →ₗ[R] R)

/-- The central charge `Z_Ω(v) = ⟪Ω, v⟫` at a class `Ω` of the Mukai lattice. -/
def charge (Ω : MukaiLattice R N) : MukaiLattice R N →ₗ[R] R :=
  mukaiForm b Ω

@[simp]
theorem charge_apply (Ω v : MukaiLattice R N) : charge b Ω v = pairing b Ω v :=
  rfl

/-- `Z_Ω(0, 0, 1) = -Ω.rank`: a point has charge `-1` at every point of rank one. -/
theorem charge_corankUnit (Ω : MukaiLattice R N) : charge b Ω corankUnit = -Ω.1 := by
  simp [corankUnit, pairing]

/-- **The rescaled master lemma.** If a linear map `ρ` preserves the Mukai form and sends `Ω` to
`f • Ω'`, then `f · Z_{Ω'}(ρ v) = Z_Ω(v)`. No inverse, involution or symmetry is needed. -/
theorem mul_charge_of_apply_eq_smul (ρ : MukaiLattice R N →ₗ[R] MukaiLattice R N)
    (hρ : ∀ x y, mukaiForm b (ρ x) (ρ y) = mukaiForm b x y) {Ω Ω' : MukaiLattice R N} {f : R}
    (hf : ρ Ω = f • Ω') (v : MukaiLattice R N) :
    f * charge b Ω' (ρ v) = charge b Ω v := by
  rw [charge, charge, ← hρ Ω v, hf, map_smul, LinearMap.smul_apply, smul_eq_mul]

/-- **The master lemma.** For an isometric automorphism `ρ`, `Z_Ω ∘ ρ = Z_{ρ⁻¹ Ω}`. -/
theorem charge_comp_linearEquiv (ρ : MukaiLattice R N ≃ₗ[R] MukaiLattice R N)
    (hρ : ∀ x y, mukaiForm b (ρ x) (ρ y) = mukaiForm b x y) (Ω v : MukaiLattice R N) :
    charge b Ω (ρ v) = charge b (ρ.symm Ω) v := by
  rw [charge, charge, ← hρ (ρ.symm Ω) v, LinearEquiv.apply_symm_apply]

/-- For a reflection, `ρ_s⁻¹ = ρ_s`: `Z_Ω ∘ ρ_s = Z_{ρ_s Ω}`. -/
theorem charge_reflect (hb : ∀ x y : N, b x y = b y x) (s : MukaiLattice R N)
    (hs : IsSpherical b s) (Ω v : MukaiLattice R N) :
    charge b Ω (reflect b s v) = charge b (reflect b s Ω) v := by
  rw [charge_apply, charge_apply, ← pairing_reflect_reflect b hb s hs (reflect b s Ω) v,
    reflect_reflect b s hs]

end CommRing

section Field

variable {K N : Type*} [Field K] [AddCommGroup N] [Module K N]
variable {b : N →ₗ[K] N →ₗ[K] K}

/-- The exponential chart: the point `(1, x/r, t/r)` of rank one on the line of `v = (r, x, t)`. -/
def expChart (v : MukaiLattice K N) : MukaiLattice K N :=
  (1, v.1⁻¹ • v.2.1, v.1⁻¹ * v.2.2)

@[simp]
theorem expChart_fst (v : MukaiLattice K N) : (expChart v).1 = 1 :=
  rfl

/-- A class of nonzero rank is its rank times its exponential chart point. -/
theorem eq_fst_smul_expChart {v : MukaiLattice K N} (hr : v.1 ≠ 0) : v = v.1 • expChart v := by
  obtain ⟨r, c, s⟩ := v
  simp only at hr
  simp only [expChart, Prod.smul_mk, smul_eq_mul, mul_one, smul_smul, mul_inv_cancel₀ hr, one_smul,
    ← mul_assoc, one_mul]

/-- The chart point of a class `v` of nonzero rank `r` has square `⟪v, v⟫/r²`. -/
theorem selfPairing_expChart {v : MukaiLattice K N} (hr : v.1 ≠ 0) :
    selfPairing b (expChart v) = selfPairing b v / v.1 ^ 2 := by
  obtain ⟨r, c, s⟩ := v
  simp only at hr
  simp only [expChart, selfPairing_mk, map_smul, LinearMap.smul_apply, smul_eq_mul]
  field_simp

/-- **The exponential chart of the isotropic quadric.** An isotropic class of nonzero rank is its
rank times an exponential point `(1, x, t)` with `2t = b(x, x)`. -/
theorem isIsotropic_expChart {v : MukaiLattice K N} (hv : IsIsotropic b v) (hr : v.1 ≠ 0) :
    IsIsotropic b (expChart v) := by
  rw [IsIsotropic, selfPairing_expChart hr, hv, zero_div]

/-- The last coordinate of the chart point of an isotropic class is `b(x, x)/2`. -/
theorem two_mul_expChart_snd_snd {v : MukaiLattice K N} (hv : IsIsotropic b v) (hr : v.1 ≠ 0) :
    2 * (expChart v).2.2 = b (expChart v).2.1 (expChart v).2.1 := by
  have h := isIsotropic_expChart hv hr
  rw [IsIsotropic, selfPairing] at h
  simp only [pairing, expChart_fst, one_mul] at h
  linear_combination -h

/-- **The coordinate-free half-turn.** Let `ρ` be a linear map preserving the Mukai form and `Ω`
an isotropic class with `ρ Ω` of nonzero rank. Then `ρ Ω` is its rank times the exponential point
`expChart (ρ Ω)`, which is isotropic, and the charges are related by

`(ρ Ω).rank · Z_{expChart (ρ Ω)}(ρ v) = Z_Ω(v)`.

No symmetry of `b`, no inverse of `ρ` and no Picard-rank hypothesis are used. -/
theorem charge_halfTurn_of_isometry (ρ : MukaiLattice K N →ₗ[K] MukaiLattice K N)
    (hρ : ∀ x y, mukaiForm b (ρ x) (ρ y) = mukaiForm b x y) {Ω : MukaiLattice K N}
    (hΩ : IsIsotropic b Ω) (hr : (ρ Ω).1 ≠ 0) :
    IsIsotropic b (expChart (ρ Ω)) ∧
      ∀ v, (ρ Ω).1 * charge b (expChart (ρ Ω)) (ρ v) = charge b Ω v := by
  have hiso : IsIsotropic b (ρ Ω) := by
    rw [IsIsotropic, selfPairing_eq_pairing, ← mukaiForm_apply, hρ]
    exact hΩ
  exact ⟨isIsotropic_expChart hiso hr,
    fun v => mul_charge_of_apply_eq_smul b ρ hρ (eq_fst_smul_expChart hr) v⟩

end Field

end Mukai
