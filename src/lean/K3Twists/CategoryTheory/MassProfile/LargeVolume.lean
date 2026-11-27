/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.MassProfile.Basic

/-!
# The large-volume limit and the cusp point

Let a group `Γ` act on a type `Obj` of objects and on a space `Stab` of stability conditions, with
equivariant mass profiles `m_{gσ} = g • m_σ`. Along the large-volume ray `σ_t = σ_{β, tω}` of a K3
surface (`β` real, `ω` ample) the mass of every fixed object grows like `t²`:

  `m_{σ_t}(E) / (ω² t² / 2) → R(E)`,     `R(E) = Σ_j rk 𝓗^j(E)`,

the sum of the generic ranks of the cohomology sheaves (`LargeVolumeHypotheses.tendsto_mass`). The
limit `[R]` of the projectivized masses is the **cusp point** of the mass boundary. From this field
and equivariance alone:

* `LargeVolumeHypotheses.tendsto_normalized_mass`: the profiles `(ω²t²/2)⁻¹ m_{σ_t}` converge to
  `R`;
* `LargeVolumeHypotheses.tendsto_normalized_mass_smul`: along the moved ray they converge to
  `g • R`, for every `g`;
* `LargeVolumeHypotheses.tendsto_mass_generator_smul`: for a split generator `G = ⊕ S_i`, on which
  `R` is additive, `(ω²t²/2)⁻¹ m_{Wσ_t}(G) → p(W) = Σ_i R(W⁻¹ S_i)`: the point measurement `p(W)` is
  the value of the cusp point on the translates of the summands. The convergence is not uniform in
  `W`;
* `LargeVolumeHypotheses.tendsto_normalize`: if `R(G) > 0`, the masses normalized by their value on
  `G` converge to `R` normalized by `R(G)`.

## The field

`tendsto_mass` holds in every Picard rank, along every ray `σ_{β, tω}` with `β` real and `ω` a
rational ample class, for real `t → ∞`. It has no published proof and no human review. Related
published results: Bridgeland, arXiv:math/0307164, Proposition 14.2 (the semistable objects of
positive rank at large volume), and Bayer, arXiv:0712.1083, Proposition 4.1 and Lemma 4.2 (along
the integer multiples `m ω` the HN filtration of a fixed object is eventually the polynomial one,
which gives the limit along integer `t`).

## Real objects

`AlgebraicGeometry/Surface/K3/PicardRankOne/LargeVolume.lean` builds an instance on the formal
direct sums of Mukai vectors of a K3 surface of Picard rank one, with the isometries of the Mukai
lattice acting, the masses of direct sums of semistable objects of those classes for the geometric
charges of the large-volume ray, and `R` the absolute rank of the summands. That `R` is the rank
functional of objects of the derived category needs that category, which Mathlib does not have.

## Main definitions

* `LargeVolumeHypotheses Obj Γ Stab κ`: equivariant masses, the large-volume ray with its scale,
  the rank functional and a split generator.
* `LargeVolumeHypotheses.pointRank I W`: `p(W) = Σ_i R(W⁻¹ S_i)`.
-/

open Filter Topology
open scoped NNReal

/-- **The large-volume interface.** Equivariant mass profiles on a space `Stab` acted on by `Γ`, the
large-volume ray `t ↦ σ_t` with its scale `ω² t² / 2`, the rank functional `R` with its limit
`tendsto_mass`, and a split generator `G = ⊕ S_i` on which `R` is additive. -/
structure LargeVolumeHypotheses (Obj Γ Stab κ : Type*) [Group Γ] [MulAction Γ Obj]
    [MulAction Γ Stab] [Fintype κ] where
  /-- The mass profile `m_σ` of a stability condition. -/
  mass : Stab → Profile Obj
  /-- Equivariance: `m_{gσ} = g • m_σ`, that is `m_{gσ}(g E) = m_σ(E)`. -/
  mass_smul : ∀ (g : Γ) (σ : Stab), mass (g • σ) = g • mass σ
  /-- The large-volume ray `t ↦ σ_{β, tω}`. -/
  ray : ℝ → Stab
  /-- The scale `ω² t² / 2` of the ray (`d t²` for `ω = H`, `H² = 2d`). -/
  scale : ℝ → ℝ≥0
  /-- The rank functional `R(E) = Σ_j rk 𝓗^j(E)`. -/
  rank : Profile Obj
  /-- **The large-volume limit** `m_{σ_t}(E) / (ω² t² / 2) → R(E)` for every object, in every
  Picard rank. No published proof and no human review; see the module docstring for the related
  published results (Bridgeland, arXiv:math/0307164, Proposition 14.2; Bayer, arXiv:0712.1083,
  Proposition 4.1). -/
  tendsto_mass : ∀ E, Tendsto (fun t ↦ (scale t)⁻¹ * mass (ray t) E) atTop (𝓝 (rank E))
  /-- The split generator `G`. -/
  G : Obj
  /-- Its summands `S_i`. -/
  S : κ → Obj
  /-- `R` is additive on direct sums: `R(g G) = Σ_i R(g S_i)`. -/
  rank_smul_G : ∀ g : Γ, rank (g • G) = ∑ i, rank (g • S i)

namespace LargeVolumeHypotheses

variable {Obj Γ Stab κ : Type*} [Group Γ] [MulAction Γ Obj] [MulAction Γ Stab] [Fintype κ]
  (I : LargeVolumeHypotheses Obj Γ Stab κ)

/-- The point measurement `p(W) = Σ_i R(W⁻¹ S_i)`. -/
def pointRank (W : Γ) : ℝ≥0 := ∑ i, I.rank (W⁻¹ • I.S i)

/-- `p(W) = R(W⁻¹ G)`. -/
lemma pointRank_eq (W : Γ) : I.pointRank W = I.rank (W⁻¹ • I.G) :=
  (I.rank_smul_G W⁻¹).symm

/-- The normalized masses along the large-volume ray converge to the rank functional. -/
theorem tendsto_normalized_mass :
    Tendsto (fun t ↦ (I.scale t)⁻¹ • I.mass (I.ray t)) atTop (𝓝 I.rank) :=
  Profile.tendsto_nhds_iff.2 fun E ↦ I.tendsto_mass E

/-- Along a moved ray the normalized masses converge to the moved rank functional:
`(ω²t²/2)⁻¹ m_{gσ_t} → g • R`. -/
theorem tendsto_normalized_mass_smul (g : Γ) :
    Tendsto (fun t ↦ (I.scale t)⁻¹ • I.mass (g • I.ray t)) atTop (𝓝 (g • I.rank)) :=
  Profile.tendsto_normalized_of_equivariant I.mass_smul g I.tendsto_normalized_mass

/-- **The point measurement as a value of the cusp point.** For every `W`,
`m_{Wσ_t}(G) / (ω²t²/2) → p(W) = Σ_i R(W⁻¹ S_i)`. -/
theorem tendsto_mass_generator_smul (W : Γ) :
    Tendsto (fun t ↦ (I.scale t)⁻¹ * I.mass (W • I.ray t) I.G) atTop (𝓝 (I.pointRank W)) := by
  have h := Profile.tendsto_nhds_iff.1 (I.tendsto_normalized_mass_smul W) I.G
  rw [Profile.smul_apply, ← I.pointRank_eq] at h
  exact h

/-- **Projective convergence to the cusp point.** If `R(G) ≠ 0`, the masses normalized by their
value on `G` converge to `R / R(G)`. -/
theorem tendsto_normalize (hG : I.rank I.G ≠ 0) :
    Tendsto (fun t ↦ Profile.normalize (I.mass (I.ray t)) I.G) atTop
      (𝓝 (Profile.normalize I.rank I.G)) := by
  have hN := I.tendsto_normalized_mass
  have hG' : Tendsto (fun t ↦ (I.scale t)⁻¹ * I.mass (I.ray t) I.G) atTop (𝓝 (I.rank I.G)) :=
    I.tendsto_mass I.G
  have hinv := hG'.inv₀ hG
  have hev : ∀ᶠ t in atTop, (I.scale t)⁻¹ * I.mass (I.ray t) I.G ≠ 0 :=
    hG'.eventually_ne hG
  refine (hinv.smul hN).congr' ?_
  filter_upwards [hev] with t ht
  have hs : I.scale t ≠ 0 := by
    intro h
    rw [h, inv_zero, zero_mul] at ht
    exact ht rfl
  ext E
  simp only [Profile.nnreal_smul_apply, Profile.normalize_apply, mul_inv, inv_inv]
  congr 1
  calc I.scale t * (I.mass (I.ray t) I.G)⁻¹ * ((I.scale t)⁻¹ * I.mass (I.ray t) E)
      = (I.scale t * (I.scale t)⁻¹) * ((I.mass (I.ray t) I.G)⁻¹ * I.mass (I.ray t) E) := by
        ring
    _ = _ := by rw [mul_inv_cancel₀ hs, one_mul]

end LargeVolumeHypotheses
