/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.PicardRankOne.LargeVolume

/-!
# The large-volume interface on the classes of Picard rank one

`LargeVolumeHypotheses` has an instance on the classes of a K3 surface of Picard rank one
(`AlgebraicGeometry.K3.PicardRankOne.largeVolume`). Here its consequences run on that instance at
`d = 1`: the rank functional is `3` on the generator `𝒪_X ⊕ 𝒪_X(H) ⊕ 𝒪_X(2H)`, the normalized mass
of a moved generator converges to the point measurement, and the masses normalized by the
generator converge to the cusp point.

Built by `lake test`.
-/

namespace AlgebraicGeometry.K3.PicardRankOne.LargeVolumeModel

open Filter Topology

/-- The instance at `d = 1`. -/
noncomputable abbrev I := largeVolume 1 one_pos

/-- `R` is `3` on the generator: three line bundles of rank one. -/
theorem rank_generator : I.rank (lineGenerator 1) = 3 := by
  change sumRank (lineGenerator 1) = 3
  simp [sumRank, lineGenerator, lineTriple, MukaiVector.lineBundle]
  norm_num

/-- The point measurement as the limit of normalized masses along a moved ray. -/
example (W : mukaiIsometries 1) :
    Tendsto (fun t ↦ (I.scale t)⁻¹ * I.mass (W • I.ray t) I.G) atTop (𝓝 (I.pointRank W)) :=
  I.tendsto_mass_generator_smul W

/-- The masses normalized by the generator converge to the cusp point. -/
example :
    Tendsto (fun t ↦ Profile.normalize (I.mass (I.ray t)) I.G) atTop
      (𝓝 (Profile.normalize I.rank I.G)) :=
  I.tendsto_normalize (by rw [show I.G = lineGenerator 1 from rfl, rank_generator]; norm_num)

end AlgebraicGeometry.K3.PicardRankOne.LargeVolumeModel
