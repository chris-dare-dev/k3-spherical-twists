/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.EllipticWithSection.KernelRootSystem
import K3Twists.LinearAlgebra.Lattice.Arrangement.Lorentzian

/-!
# Two roots with pairing `-3` on the elliptic K3 surface

On the real Mukai lattice of the elliptic K3 surface with a section, of signature `(2, 2)`
(`sigPos_mukaiForm`), the Mukai vectors `v(𝒪_X) = (1, 0, 1)` and `v(𝒪(H)) = (1, H, 2)` of the
line bundles `𝒪_X` and `𝒪(H)`, `H = C + 2F`, `H² = 2`, are roots that pair to `-3`. This is the
indefinite case of the stratum trichotomy (`LinearAlgebra/Lattice/Arrangement/Lorentzian.lean`) on
this lattice: for `W` their span,

* `sigPos_orthogonal_lineBundle_pair`, `sigNeg_orthogonal_lineBundle_pair`: `W^⊥` has signature
  `(1, 1)`, the signature `(1, ρ - 1)` with `ρ = 2`;
* `exists_neg_of_le_orthogonal_lineBundle_pair`: `W^⊥` contains no positive semidefinite plane, so
  no positive period, and no limit of positive periods, is orthogonal to both roots.

These are lattice statements: that the charges are those of stability conditions is not
formalized.
-/

namespace AlgebraicGeometry.K3.EllipticWithSection

open Mukai Module

lemma realModel_lineBundle_zero : realModel toRealNS (lineBundle 0) = (1, (0, 0), 1) := by
  simp [lineBundle, realModel]

lemma realModel_lineBundle_polarization :
    realModel toRealNS (lineBundle (1, 2)) = (1, (1, 2), 2) := by
  simp [lineBundle, realModel, toRealNS]

lemma mukaiForm_lineBundle_zero :
    mukaiForm intersectionReal (realModel toRealNS (lineBundle 0))
      (realModel toRealNS (lineBundle 0)) = -2 := by
  rw [realModel_lineBundle_zero]
  norm_num [Mukai.pairing]

lemma mukaiForm_lineBundle_polarization :
    mukaiForm intersectionReal (realModel toRealNS (lineBundle (1, 2)))
      (realModel toRealNS (lineBundle (1, 2))) = -2 := by
  rw [realModel_lineBundle_polarization]
  norm_num [Mukai.pairing]

lemma mukaiForm_lineBundle_zero_polarization :
    mukaiForm intersectionReal (realModel toRealNS (lineBundle 0))
      (realModel toRealNS (lineBundle (1, 2))) = -3 := by
  rw [realModel_lineBundle_zero, realModel_lineBundle_polarization]
  norm_num [Mukai.pairing]

lemma four_lt_mukaiForm_lineBundle_pair_sq :
    4 < mukaiForm intersectionReal (realModel toRealNS (lineBundle 0))
      (realModel toRealNS (lineBundle (1, 2))) ^ 2 := by
  rw [mukaiForm_lineBundle_zero_polarization]
  norm_num

/-- **The orthogonal complement of `v(𝒪_X)` and `v(𝒪(H))` has one positive direction.** -/
theorem sigPos_orthogonal_lineBundle_pair :
    sigPos ((mukaiForm intersectionReal).restrict ((mukaiForm intersectionReal).orthogonal
      (Submodule.span ℝ {realModel toRealNS (lineBundle 0),
        realModel toRealNS (lineBundle (1, 2))}))).toQuadraticMap = 1 :=
  sigPos_orthogonal_pair_eq_one _ mukaiForm_real_comm mukaiForm_real_separating sigPos_mukaiForm
    mukaiForm_lineBundle_zero mukaiForm_lineBundle_polarization
    four_lt_mukaiForm_lineBundle_pair_sq

/-- **The orthogonal complement of `v(𝒪_X)` and `v(𝒪(H))` has one negative direction**: with
`sigPos_orthogonal_lineBundle_pair`, its signature is `(1, 1)`. -/
theorem sigNeg_orthogonal_lineBundle_pair :
    sigNeg ((mukaiForm intersectionReal).restrict ((mukaiForm intersectionReal).orthogonal
      (Submodule.span ℝ {realModel toRealNS (lineBundle 0),
        realModel toRealNS (lineBundle (1, 2))}))).toQuadraticMap = 1 := by
  have h := sigNeg_orthogonal_pair _ mukaiForm_real_comm mukaiForm_real_separating
    sigPos_mukaiForm mukaiForm_lineBundle_zero mukaiForm_lineBundle_polarization
    four_lt_mukaiForm_lineBundle_pair_sq
  have hV := QuadraticForm.sigPos_add_sigNeg_add_radical
    (Q := (mukaiForm intersectionReal).toQuadraticMap)
  rw [QuadraticForm.radical_toQuadraticMap_eq_bot _ mukaiForm_real_comm
    mukaiForm_real_separating, finrank_bot, add_zero, sigPos_mukaiForm] at hV
  have hdim : finrank ℝ (MukaiLattice ℝ (ℝ × ℝ)) = 4 := by
    simp [Module.finrank_prod]
  omega

/-- **No positive semidefinite plane is orthogonal to `v(𝒪_X)` and `v(𝒪(H))`**: every subspace of
dimension at least two of the orthogonal complement contains a vector of negative square. -/
theorem exists_neg_of_le_orthogonal_lineBundle_pair {P : Submodule ℝ (MukaiLattice ℝ (ℝ × ℝ))}
    (hP : P ≤ (mukaiForm intersectionReal).orthogonal (Submodule.span ℝ
      {realModel toRealNS (lineBundle 0), realModel toRealNS (lineBundle (1, 2))}))
    (hPdim : 2 ≤ finrank ℝ P) : ∃ x ∈ P, mukaiForm intersectionReal x x < 0 :=
  exists_neg_of_le_orthogonal_pair _ mukaiForm_real_comm mukaiForm_real_separating
    sigPos_mukaiForm mukaiForm_lineBundle_zero mukaiForm_lineBundle_polarization
    four_lt_mukaiForm_lineBundle_pair_sq hP hPdim

end AlgebraicGeometry.K3.EllipticWithSection
