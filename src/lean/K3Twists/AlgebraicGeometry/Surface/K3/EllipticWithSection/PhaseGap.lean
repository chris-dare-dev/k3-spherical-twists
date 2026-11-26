/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.EllipticWithSection.SupportProperty
import K3Twists.Analysis.Complex.PhaseGap

/-!
# The lattice gap at the curve wall of the elliptic K3 surface

At the charge of Tramel and Xia on the elliptic K3 surface with a section
(`EllipticWithSection/SupportProperty.lean`), the support property holds on the integral classes
of square at least `-2` (`exists_supportProperty_charge`). So only finitely many of them have
charge of modulus at most `R` (`finite_classes_charge_le`), and for finitely many phases there is a
phase gap for their charges (`exists_latticeGap_charge`): the choice of neighbourhood in the lemma
on intersecting ordinary walls, at this charge.

This is a lattice statement: that `Z` is the central charge of a stability condition is the cited
theorem of Tramel and Xia (arXiv:1702.06252).
-/

open Mukai Real Complex

namespace AlgebraicGeometry.K3.EllipticWithSection

/-- **Finitely many classes of bounded charge** at the curve wall: the integral classes of square
at least `-2` with `|Z(v)| ≤ R`. -/
theorem finite_classes_charge_le (R : ℝ) :
    {v : MukaiLattice ℤ NS | -2 ≤ selfPairing intersection v ∧ ‖charge v‖ ≤ R}.Finite := by
  obtain ⟨D, hD⟩ := exists_supportProperty_charge
  refine (finite_realModel_norm_le finite_toRealNS_norm_le (max D 0 * R)).subset
    fun v ⟨h2, hR⟩ => ?_
  calc ‖realModel toRealNS v‖ ≤ D * ‖charge v‖ := hD v h2
    _ ≤ max D 0 * ‖charge v‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    _ ≤ max D 0 * R := mul_le_mul_of_nonneg_left hR (le_max_right _ _)

/-- **The lattice gap at the curve wall.** For every bound `R` and finitely many phases `Φ` there
is `ε ∈ (0, 1/8)` such that an integral class of square at least `-2` with `|Z(v)| ≤ R` whose
charge lies on a ray of phase `ψ` within `2ε` of some `φ ∈ Φ` has `ψ = φ`, and distinct phases of
`Φ` are more than `2ε` apart. -/
theorem exists_latticeGap_charge (R : ℝ) (Φ : Finset ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 8 ∧
      (∀ v : MukaiLattice ℤ NS, -2 ≤ selfPairing intersection v → ‖charge v‖ ≤ R →
        ∀ φ ∈ Φ, ∀ m ψ : ℝ, 0 < m → charge v = (m : ℂ) * exp ((π * ψ : ℝ) * I) →
          |ψ - φ| < 2 * ε → ψ = φ) ∧
      ∀ φ ∈ Φ, ∀ φ' ∈ Φ, φ ≠ φ' → 2 * ε < |φ - φ'| := by
  obtain ⟨ε, hε, hε8, hgap, hsep⟩ := exists_phaseGap
    (charge '' {v | -2 ≤ selfPairing intersection v ∧ ‖charge v‖ ≤ R})
    ((finite_classes_charge_le R).image _) Φ
  exact ⟨ε, hε, hε8, fun v h2 hR φ hφ m ψ hm hv hlt =>
    hgap _ ⟨v, ⟨h2, hR⟩, rfl⟩ φ hφ m ψ hm hv hlt, hsep⟩

end AlgebraicGeometry.K3.EllipticWithSection
