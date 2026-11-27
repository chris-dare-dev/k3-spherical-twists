/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.Lattice.Mukai.AffineWeyl.Index
import K3Twists.LinearAlgebra.Lattice.Mukai.AffineWeyl.SeveralFibres

/-!
# The translation lattices of several fibres and their index bounds

For a single connected exceptional fibre `F` with Cartan matrix `A`, the degrees `L ↦ (L·Cᵢ)ᵢ` give
`Aℤ^l ⊆ Λ_H ⊆ Λ ⊆ ℤ^l` with `[ℤ^l : Aℤ^l] = |det A|` (`AffineWeyl/Index.lean`). This file treats a
finite family of mutually orthogonal fibres `F a` (the setting of `AffineWeyl/SeveralFibres.lean`),
with the degrees of all fibres at once, `L ↦ ((L·Cᵢᵃ)ᵢ)ₐ ∈ ∏ₐ ℤ^{lₐ}`
(`FundamentalCycle.sumDegree`):

* `Λ`, the degrees of all classes (`FundamentalCycle.sumDegreeLattice`), and `Λ_H`, the degrees
  of the classes orthogonal to a class `H` (`FundamentalCycle.sumPolarizedDegreeLattice`);
* `Q^∨ = ∏ₐ Aₐℤ^{lₐ}`, the coroot lattice of the configuration
  (`FundamentalCycle.sumCorootLattice`). For orthogonal fibres the Cartan matrix of all the
  curves is the direct sum of the `Aₐ`, and `Q^∨` is its image in these coordinates.

**`Q^∨ ⊆ Λ_H ⊆ Λ ⊆ ∏ₐ ℤ^{lₐ}`** for `H` orthogonal to every curve
(`sumCorootLattice_le_sumPolarizedDegreeLattice`, `sumPolarizedDegreeLattice_le_sumDegreeLattice`):
the class `Σₐ Σᵢ dᵢᵃ Cᵢᵃ` has degree `-Aₐdᵃ` on the fibre `F a`, because the curves of the other
fibres are orthogonal to it. And `[∏ₐ ℤ^{lₐ} : Q^∨] = ∏ₐ |det Aₐ|` (`index_sumCorootLattice`), so
the indices `[∏ₐ ℤ^{lₐ} : Λ]`, `[∏ₐ ℤ^{lₐ} : Λ_H]` and `[Λ : Q^∨]`, `[Λ_H : Q^∨]` divide
`∏ₐ |det Aₐ|` (`index_sumDegreeLattice_dvd`, `index_sumPolarizedDegreeLattice_dvd`,
`relIndex_sumCorootLattice_dvd`, `relIndex_sumCorootLattice_polarized_dvd`).

## Main definitions

* `FundamentalCycle.sumDegree`: the degree map of several fibres.
* `FundamentalCycle.sumDegreeLattice`, `FundamentalCycle.sumPolarizedDegreeLattice`,
  `FundamentalCycle.sumCorootLattice`: the lattices `Λ`, `Λ_H` and `Q^∨` of several fibres.

## Main results

* `sumCorootLattice_le_sumPolarizedDegreeLattice`: `Q^∨ ⊆ Λ_H`.
* `index_sumCorootLattice`: `[∏ₐ ℤ^{lₐ} : Q^∨] = ∏ₐ |det Aₐ|`.
* `index_sumDegreeLattice_dvd`, `index_sumPolarizedDegreeLattice_dvd`,
  `relIndex_sumCorootLattice_dvd`: the indices divide `∏ₐ |det Aₐ|`.

## References

* N. Bourbaki, *Groupes et algèbres de Lie*, Ch. VI, §1.10 and §4.
-/

open Matrix

namespace Mukai.FundamentalCycle

variable {N : Type*} [AddCommGroup N] {b : N →ₗ[ℤ] N →ₗ[ℤ] ℤ} {A : Type*}
  {ι : A → Type*} [∀ a, Fintype (ι a)]

/-- **The degree map of several fibres**: `L ↦ ((L·Cᵢᵃ)ᵢ)ₐ`. -/
def sumDegree (F : ∀ a, FundamentalCycle b (ι a)) : N →ₗ[ℤ] ∀ a, ι a → ℤ :=
  LinearMap.pi fun a => (F a).degree

@[simp]
theorem sumDegree_apply (F : ∀ a, FundamentalCycle b (ι a)) (L : N) (a : A) :
    sumDegree F L a = (F a).degree L :=
  rfl

/-- `Λ` for several fibres: the degrees of all classes. -/
def sumDegreeLattice (F : ∀ a, FundamentalCycle b (ι a)) : Submodule ℤ (∀ a, ι a → ℤ) :=
  LinearMap.range (sumDegree F)

/-- `Λ_H` for several fibres: the degrees of the classes orthogonal to `H`. -/
def sumPolarizedDegreeLattice (F : ∀ a, FundamentalCycle b (ι a)) (H : N) :
    Submodule ℤ (∀ a, ι a → ℤ) :=
  (LinearMap.ker (b.flip H)).map (sumDegree F)

theorem sumPolarizedDegreeLattice_le_sumDegreeLattice (F : ∀ a, FundamentalCycle b (ι a))
    (H : N) : sumPolarizedDegreeLattice F H ≤ sumDegreeLattice F :=
  LinearMap.map_le_range

/-- A class supported on the fibre `F a'` has degree zero on a fibre `F a` orthogonal to it. -/
theorem degree_eq_zero_of_mem_rootLattice (F : ∀ a, FundamentalCycle b (ι a)) {a a' : A}
    (horth : ∀ i j, b ((F a').curve i) ((F a).curve j) = 0) {c : N}
    (hc : c ∈ (F a').rootLattice) : (F a).degree c = 0 := by
  classical
  ext i
  exact apply_eq_zero_of_mem_rootLattice F horth hc ⟨Pi.single i 1, by simp [combination]⟩

variable [∀ a, DecidableEq (ι a)]

/-- `Q^∨` for several fibres: `∏ₐ Aₐℤ^{lₐ}`, the image of the Cartan matrix of the configuration,
the direct sum of the `Aₐ` for orthogonal fibres. -/
def sumCorootLattice (F : ∀ a, FundamentalCycle b (ι a)) : Submodule ℤ (∀ a, ι a → ℤ) :=
  Submodule.pi Set.univ fun a => (F a).corootLattice

theorem mem_sumCorootLattice (F : ∀ a, FundamentalCycle b (ι a)) {x : ∀ a, ι a → ℤ} :
    x ∈ sumCorootLattice F ↔ ∀ a, x a ∈ (F a).corootLattice := by
  simp [sumCorootLattice]

variable [Fintype A]

/-- **`Q^∨ ⊆ Λ_H` for mutually orthogonal fibres**: `(Aₐdᵃ)ₐ` is the degree of
`Σₐ Σᵢ (-dᵢᵃ) Cᵢᵃ`, which is orthogonal to `H`. -/
theorem sumCorootLattice_le_sumPolarizedDegreeLattice (hb : ∀ x y, b x y = b y x)
    (F : ∀ a, FundamentalCycle b (ι a))
    (horth : ∀ a a', a ≠ a' → ∀ i j, b ((F a).curve i) ((F a').curve j) = 0) {H : N}
    (hH : ∀ a i, b ((F a).curve i) H = 0) :
    sumCorootLattice F ≤ sumPolarizedDegreeLattice F H := by
  classical
  intro x hx
  choose d hd using (mem_sumCorootLattice F).mp hx
  refine ⟨∑ a, (F a).combination (-d a), ?_, ?_⟩
  · simp [map_sum, combination_apply, hH]
  · funext a
    rw [sumDegree_apply, map_sum, Finset.sum_eq_single a]
    · rw [combination_apply, (F a).degree_combination hb, Matrix.mulVec_neg, neg_neg, ← hd a,
        Matrix.toLin'_apply]
    · intro a' _ ha'
      exact degree_eq_zero_of_mem_rootLattice F (horth a' a ha') ⟨-d a', rfl⟩
    · simp

theorem sumCorootLattice_le_sumDegreeLattice (hb : ∀ x y, b x y = b y x)
    (F : ∀ a, FundamentalCycle b (ι a))
    (horth : ∀ a a', a ≠ a' → ∀ i j, b ((F a).curve i) ((F a').curve j) = 0) :
    sumCorootLattice F ≤ sumDegreeLattice F :=
  (sumCorootLattice_le_sumPolarizedDegreeLattice hb F horth (H := 0) fun _ _ => by simp).trans
    (sumPolarizedDegreeLattice_le_sumDegreeLattice F 0)

/-- **`[∏ₐ ℤ^{lₐ} : Q^∨] = ∏ₐ |det Aₐ|`**: the quotient is `∏ₐ ℤ^{lₐ}/Aₐℤ^{lₐ}`
(`Submodule.quotientPi`), and `[ℤ^{lₐ} : Aₐℤ^{lₐ}] = |det Aₐ|` (`index_corootLattice`). -/
theorem index_sumCorootLattice (F : ∀ a, FundamentalCycle b (ι a)) :
    (sumCorootLattice F).toAddSubgroup.index = ∏ a, (F a).cartan.det.natAbs := by
  classical
  rw [AddSubgroup.index_eq_card]
  change Nat.card ((∀ a, ι a → ℤ) ⧸ sumCorootLattice F) = _
  rw [sumCorootLattice, Nat.card_congr (Submodule.quotientPi _).toEquiv, Nat.card_pi]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← (F a).index_corootLattice, AddSubgroup.index_eq_card]
  rfl

/-- **`[∏ₐ ℤ^{lₐ} : Λ]` divides `∏ₐ |det Aₐ|`** for mutually orthogonal fibres. -/
theorem index_sumDegreeLattice_dvd (hb : ∀ x y, b x y = b y x)
    (F : ∀ a, FundamentalCycle b (ι a))
    (horth : ∀ a a', a ≠ a' → ∀ i j, b ((F a).curve i) ((F a').curve j) = 0) :
    (sumDegreeLattice F).toAddSubgroup.index ∣ ∏ a, (F a).cartan.det.natAbs := by
  rw [← index_sumCorootLattice F]
  exact AddSubgroup.index_dvd_of_le (sumCorootLattice_le_sumDegreeLattice hb F horth)

/-- **`[∏ₐ ℤ^{lₐ} : Λ_H]` divides `∏ₐ |det Aₐ|`** for mutually orthogonal fibres and `H`
orthogonal to every curve. -/
theorem index_sumPolarizedDegreeLattice_dvd (hb : ∀ x y, b x y = b y x)
    (F : ∀ a, FundamentalCycle b (ι a))
    (horth : ∀ a a', a ≠ a' → ∀ i j, b ((F a).curve i) ((F a').curve j) = 0) {H : N}
    (hH : ∀ a i, b ((F a).curve i) H = 0) :
    (sumPolarizedDegreeLattice F H).toAddSubgroup.index ∣ ∏ a, (F a).cartan.det.natAbs := by
  rw [← index_sumCorootLattice F]
  exact AddSubgroup.index_dvd_of_le (sumCorootLattice_le_sumPolarizedDegreeLattice hb F horth hH)

/-- **`[Λ : Q^∨]` divides `∏ₐ |det Aₐ|`** for mutually orthogonal fibres. -/
theorem relIndex_sumCorootLattice_dvd (hb : ∀ x y, b x y = b y x)
    (F : ∀ a, FundamentalCycle b (ι a))
    (horth : ∀ a a', a ≠ a' → ∀ i j, b ((F a).curve i) ((F a').curve j) = 0) :
    (sumCorootLattice F).toAddSubgroup.relIndex (sumDegreeLattice F).toAddSubgroup ∣
      ∏ a, (F a).cartan.det.natAbs := by
  rw [← index_sumCorootLattice F]
  exact AddSubgroup.relIndex_dvd_index_of_le (sumCorootLattice_le_sumDegreeLattice hb F horth)

/-- **`[Λ_H : Q^∨]` divides `∏ₐ |det Aₐ|`** for mutually orthogonal fibres and `H` orthogonal to
every curve. -/
theorem relIndex_sumCorootLattice_polarized_dvd (hb : ∀ x y, b x y = b y x)
    (F : ∀ a, FundamentalCycle b (ι a))
    (horth : ∀ a a', a ≠ a' → ∀ i j, b ((F a).curve i) ((F a').curve j) = 0) {H : N}
    (hH : ∀ a i, b ((F a).curve i) H = 0) :
    (sumCorootLattice F).toAddSubgroup.relIndex (sumPolarizedDegreeLattice F H).toAddSubgroup ∣
      ∏ a, (F a).cartan.det.natAbs := by
  rw [← index_sumCorootLattice F]
  exact AddSubgroup.relIndex_dvd_index_of_le
    (sumCorootLattice_le_sumPolarizedDegreeLattice hb F horth hH)

end Mukai.FundamentalCycle
