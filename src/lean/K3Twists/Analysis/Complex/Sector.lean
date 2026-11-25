/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The sector budget

Phases are measured in units of `π`, as for Bridgeland's slicings: the ray of phase `φ` is
`ℝ_{≥0} e^{iπφ}`. For `0 ≤ b`, the closed **sector** of phase `φ` and half-width `b` is

```
sector φ b = {ρ e^{iπψ} : ρ ≥ 0, |ψ - φ| ≤ b},
```

and the **projection** onto the ray of phase `φ` is the real-linear form
`p_φ(z) = Re(z e^{-iπφ})`.

## The sector budget

For a closed convex cone `K` of a finite-dimensional real normed space and a continuous linear
form `ℓ` positive on `K ∖ 0`, there is `κ_K > 0` with `κ_K ‖z‖ ≤ ℓ(z)` on `K`
(`exists_pos_mul_norm_le_of_isClosed`), so that for any finitely many `z_j ∈ K`

```
κ_K Σ ‖z_j‖ ≤ ℓ(Σ z_j)                                  (sum_norm_mul_le).
```

For the Euclidean sector of half-width `b ≤ 1/2` and `ℓ = p_φ`, the constant is `κ = cos(πb)`
(`norm_mul_cos_le_phaseProj`):

```
cos(πb) Σ |z_j| ≤ p_φ(Σ z_j) ≤ |Σ z_j|                  (sum_norm_mul_cos_le_phaseProj).
```

This is the budget of the stable constituents of an object whose charges lie in one strict
sector (`b < 1/2`): their charges cannot cancel, so their total length is at most
`|Z(E)|/cos(πb)`. Its lattice consequence, the bound on the number of constituents, is
`Mukai.card_mul_cos_le_of_sector` in `LinearAlgebra/Lattice/Mukai/Support.lean`.
-/

open Real

namespace Complex

/-! ### The projection onto a ray -/

/-- The projection `p_φ(z) = Re(z e^{-iπφ})` onto the ray of phase `φ`, a real-linear form. -/
noncomputable def phaseProj (φ : ℝ) : ℂ →ₗ[ℝ] ℝ where
  toFun z := (z * exp (-(π * φ : ℝ) * I)).re
  map_add' z w := by rw [add_mul, add_re]
  map_smul' a z := by
    simp only [Complex.real_smul, mul_assoc, re_ofReal_mul, RingHom.id_apply, smul_eq_mul]

theorem phaseProj_apply (φ : ℝ) (z : ℂ) : phaseProj φ z = (z * exp (-(π * φ : ℝ) * I)).re :=
  rfl

/-- The projection is `1`-Lipschitz: `p_φ(z) ≤ |z|`. -/
theorem phaseProj_le_norm (φ : ℝ) (z : ℂ) : phaseProj φ z ≤ ‖z‖ := by
  rw [phaseProj_apply]
  refine (re_le_norm _).trans_eq ?_
  rw [norm_mul, ← ofReal_neg, norm_exp_ofReal_mul_I, mul_one]

theorem phaseProj_sum {ι : Type*} (φ : ℝ) (s : Finset ι) (z : ι → ℂ) :
    phaseProj φ (∑ j ∈ s, z j) = ∑ j ∈ s, phaseProj φ (z j) :=
  map_sum _ _ _

/-! ### Sectors -/

/-- The closed sector `{ρ e^{iπψ} : ρ ≥ 0, |ψ - φ| ≤ b}` of phase `φ` and half-width `b`. -/
def sector (φ b : ℝ) : Set ℂ :=
  {z | ∃ ρ : ℝ, 0 ≤ ρ ∧ ∃ ψ : ℝ, |ψ - φ| ≤ b ∧ z = ρ * exp ((π * ψ : ℝ) * I)}

/-- **The Euclidean sector constant.** On the sector of half-width `b ≤ 1`, the projection onto
the central ray is at least `cos(πb)` times the modulus. -/
theorem norm_mul_cos_le_phaseProj {φ b : ℝ} (hb : b ≤ 1) {z : ℂ} (hz : z ∈ sector φ b) :
    ‖z‖ * Real.cos (π * b) ≤ phaseProj φ z := by
  obtain ⟨ρ, hρ, ψ, hψ, rfl⟩ := hz
  have hexp : (ρ : ℂ) * exp ((π * ψ : ℝ) * I) * exp (-(π * φ : ℝ) * I) =
      ρ * exp ((π * (ψ - φ) : ℝ) * I) := by
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [phaseProj_apply, hexp, re_ofReal_mul, exp_ofReal_mul_I_re, norm_mul, norm_real,
    Real.norm_of_nonneg hρ, norm_exp_ofReal_mul_I, mul_one]
  gcongr
  rw [← Real.cos_abs (π * (ψ - φ)), abs_mul, abs_of_pos Real.pi_pos]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
    (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])

/-! ### The sector budget -/

section Cone

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The sector budget**, for any cone: if `κ ‖z‖ ≤ ℓ(z)` for every `z ∈ K`, then
`κ Σ ‖z_j‖ ≤ ℓ(Σ z_j)` for any finitely many `z_j ∈ K`. -/
theorem sum_norm_mul_le {K : Set E} (ℓ : E →ₗ[ℝ] ℝ) {κ : ℝ}
    (hK : ∀ z ∈ K, κ * ‖z‖ ≤ ℓ z) {ι : Type*} (s : Finset ι) {z : ι → E}
    (hz : ∀ j ∈ s, z j ∈ K) :
    κ * ∑ j ∈ s, ‖z j‖ ≤ ℓ (∑ j ∈ s, z j) := by
  rw [Finset.mul_sum, map_sum]
  exact Finset.sum_le_sum fun j hj => hK _ (hz j hj)

/-- **The constant `κ_K` of a closed cone in an open half-space.** For a closed cone `K` of a
finite-dimensional real normed space and a continuous linear form `ℓ` positive on `K ∖ 0`, there
is `κ > 0` with `κ ‖z‖ ≤ ℓ(z)` on `K`: the minimum of `ℓ` on the compact set of unit vectors of
`K`. -/
theorem exists_pos_mul_norm_le_of_isClosed [FiniteDimensional ℝ E] {K : Set E}
    (hKc : IsClosed K) (hK : ∀ z ∈ K, ∀ t : ℝ, 0 < t → t • z ∈ K) (ℓ : E →L[ℝ] ℝ)
    (hℓ : ∀ z ∈ K, z ≠ 0 → 0 < ℓ z) :
    ∃ κ > 0, ∀ z ∈ K, κ * ‖z‖ ≤ ℓ z := by
  set S := K ∩ Metric.sphere (0 : E) 1
  have hS : IsCompact S := (isCompact_sphere 0 1).inter_left hKc
  have hunit : ∀ z ∈ K, z ≠ 0 → ‖z‖⁻¹ • z ∈ S := fun z hz hz0 =>
    ⟨hK z hz _ (inv_pos.mpr (norm_pos_iff.mpr hz0)), by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz0)]⟩
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · refine ⟨1, one_pos, fun z hz => ?_⟩
    by_cases hz0 : z = 0
    · simp [hz0]
    · have := hunit z hz hz0
      rw [hSe] at this
      exact absurd this (Set.notMem_empty _)
  · obtain ⟨z₀, hz₀, hmin⟩ := hS.exists_isMinOn hSne ℓ.continuous.continuousOn
    have hz₀0 : z₀ ≠ 0 := by
      intro h
      have := hz₀.2
      rw [h, mem_sphere_zero_iff_norm, norm_zero] at this
      exact zero_ne_one this
    refine ⟨ℓ z₀, hℓ z₀ hz₀.1 hz₀0, fun z hz => ?_⟩
    by_cases hz0 : z = 0
    · simp [hz0]
    · have h1 := hmin (hunit z hz hz0)
      change ℓ z₀ ≤ ℓ (‖z‖⁻¹ • z) at h1
      rw [map_smul, smul_eq_mul] at h1
      have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
      rw [le_inv_mul_iff₀ hn] at h1
      linarith [mul_comm (ℓ z₀) ‖z‖]

end Cone

/-- **The Euclidean sector budget.** If the complex numbers `z_j` lie in the sector of phase `φ`
and half-width `b ≤ 1`, then `cos(πb) Σ |z_j| ≤ p_φ(Σ z_j) ≤ |Σ z_j|`. -/
theorem sum_norm_mul_cos_le_phaseProj {φ b : ℝ} (hb : b ≤ 1) {ι : Type*} (s : Finset ι)
    {z : ι → ℂ} (hz : ∀ j ∈ s, z j ∈ sector φ b) :
    Real.cos (π * b) * ∑ j ∈ s, ‖z j‖ ≤ phaseProj φ (∑ j ∈ s, z j) :=
  sum_norm_mul_le (phaseProj φ)
    (fun z hz => by rw [mul_comm]; exact norm_mul_cos_le_phaseProj hb hz) s hz

/-- The sector budget against the modulus of the sum: for `b < 1/2`,
`Σ |z_j| ≤ |Σ z_j| / cos(πb)`. -/
theorem sum_norm_le_norm_sum_div_cos {φ b : ℝ} (hb0 : 0 ≤ b) (hb : b < 1 / 2) {ι : Type*}
    (s : Finset ι) {z : ι → ℂ} (hz : ∀ j ∈ s, z j ∈ sector φ b) :
    ∑ j ∈ s, ‖z j‖ ≤ ‖∑ j ∈ s, z j‖ / Real.cos (π * b) := by
  have hcos : 0 < Real.cos (π * b) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_pos]
  rw [le_div_iff₀ hcos, mul_comm]
  exact (sum_norm_mul_cos_le_phaseProj (by linarith) s hz).trans (phaseProj_le_norm φ _)

end Complex
