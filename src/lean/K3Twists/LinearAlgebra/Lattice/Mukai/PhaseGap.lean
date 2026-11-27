/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Analysis.Complex.PhaseGap
import K3Twists.LinearAlgebra.Lattice.Mukai.Support

/-!
# The lattice-gap lemma

Let `V` be a finite-dimensional real normed space with a bilinear form `B`, `Z : V → ℂ` a charge
whose kernel is negative definite and contains no class of square at least `-2`, and `Γ ⊆ V` a set
of classes with finitely many points in every ball (the image of an integral Mukai lattice). This
is the situation at a stability condition off the root hyperplanes, at a point where several
ordinary marginal walls meet.

* `Mukai.finite_classes_of_negDef`: the classes of `Γ` with square at least `-2` and
  `‖Z v‖ ≤ R` are finitely many (the support property, `Mukai.exists_supportProperty`, with
  `Mukai.SupportProperty.finite_norm_le`).
* `Mukai.exists_latticeGap`: **the lattice-gap lemma.** For finitely many phases `φ_i` there is
  `ε ∈ (0, 1/8)` such that the charge of such a class lies on no ray of phase within `2ε` of a
  `φ_i` other than `φ_i` itself, and distinct `φ_i` are more than `2ε` apart
  (`Complex.exists_phaseGap`).

With `R = 2 max |Z(B_i)|` for the HN factors `B_i` of an object at the intersection, this is the
lattice form of the neighbourhood in the lemma on intersecting ordinary walls
(`CategoryTheory/Triangulated/StabilityCondition/IntersectingWalls.lean`). The theorems there do not
pass through stable constituents. They take a phase gap for the phases of `σ`-semistable objects of
bounded charge (`PreStabilityCondition.WithClassMap.IsPhaseGap`), which holds when the charges of
those objects are finitely many, for instance under the support property, and through it they bound
the `σ`-HN factors of each new HN factor: every new HN factor of `B_i` lies in `P_σ(φ_i)`.
-/

open Complex Real

namespace Mukai

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Finitely many classes of bounded charge.** If the kernel of `Z` is negative definite and
holds no class of square at least `-2`, only finitely many classes of `Γ` have square at least
`-2` and `‖Z v‖ ≤ R`. -/
theorem finite_classes_of_negDef (B : LinearMap.BilinForm ℝ V) (Z : V →ₗ[ℝ] ℂ)
    (hB : ∀ v, Z v = 0 → v ≠ 0 → B v v < 0) {Γ : Set V}
    (hΓ : ∀ R : ℝ, {v | v ∈ Γ ∧ ‖v‖ ≤ R}.Finite)
    (hZ : ∀ v ∈ Γ, v ≠ 0 → -2 ≤ B v v → Z v ≠ 0) (R : ℝ) :
    {v | v ∈ Γ ∧ -2 ≤ B v v ∧ ‖Z v‖ ≤ R}.Finite := by
  obtain ⟨D, hD⟩ := exists_supportProperty B Z hB hΓ hZ
  refine (hD.finite_norm_le (fun v hv => hv.1) hΓ R).subset fun v ⟨hv, h2, hR⟩ => ?_
  exact ⟨⟨hv, h2⟩, hR⟩

/-- **The lattice-gap lemma.** In the setting of `Mukai.finite_classes_of_negDef`, for finitely
many phases `Φ` there is `ε ∈ (0, 1/8)` such that a class of `Γ` with square at least `-2` and
`‖Z v‖ ≤ R` whose charge lies on the ray of phase `ψ` with `|ψ - φ| < 2ε` for some `φ ∈ Φ` has
`ψ = φ`, and distinct phases of `Φ` are more than `2ε` apart. -/
theorem exists_latticeGap (B : LinearMap.BilinForm ℝ V) (Z : V →ₗ[ℝ] ℂ)
    (hB : ∀ v, Z v = 0 → v ≠ 0 → B v v < 0) {Γ : Set V}
    (hΓ : ∀ R : ℝ, {v | v ∈ Γ ∧ ‖v‖ ≤ R}.Finite)
    (hZ : ∀ v ∈ Γ, v ≠ 0 → -2 ≤ B v v → Z v ≠ 0) (R : ℝ) (Φ : Finset ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 8 ∧
      (∀ v ∈ Γ, -2 ≤ B v v → ‖Z v‖ ≤ R → ∀ φ ∈ Φ, ∀ m ψ : ℝ, 0 < m →
        Z v = (m : ℂ) * exp ((π * ψ : ℝ) * I) → |ψ - φ| < 2 * ε → ψ = φ) ∧
      ∀ φ ∈ Φ, ∀ φ' ∈ Φ, φ ≠ φ' → 2 * ε < |φ - φ'| := by
  obtain ⟨ε, hε, hε8, hgap, hsep⟩ := exists_phaseGap (Z '' {v | v ∈ Γ ∧ -2 ≤ B v v ∧ ‖Z v‖ ≤ R})
    ((finite_classes_of_negDef B Z hB hΓ hZ R).image _) Φ
  exact ⟨ε, hε, hε8, fun v hv h2 hR φ hφ m ψ hm hZv hlt =>
    hgap _ ⟨v, ⟨hv, h2, hR⟩, rfl⟩ φ hφ m ψ hm hZv hlt, hsep⟩

end Mukai
