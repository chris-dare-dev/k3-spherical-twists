/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.EllipticWithSection.Lattice
import K3Twists.GroupTheory.Coxeter.ArtinGroup

/-!
# An `A₂` configuration on the elliptic K3 surface, on classes

On an elliptic K3 surface `X` with a section `C`, the objects `x₀ = 𝒪_X[1]` and `x₁ = 𝒪_C` form an
`A₂` configuration of spherical objects: `Hom^•(𝒪_X, 𝒪_C) = H^•(𝒪_C)` is one-dimensional, so the
Seidel–Thomas Coxeter matrix has `m = 3` (`CoxeterMatrix.ofExt`). Its object identities in
`D^b(X)` are `T_{𝒪_C} T_{𝒪_X} 𝒪_C ≅ 𝒪_X[1]`: `T_{𝒪_X} 𝒪_C` is the cone of the restriction
`𝒪_X → 𝒪_C`, that is `𝒪_X(-C)[1]`, and `T_{𝒪_C}(𝒪_X(-C)[1]) ≅ 𝒪_X[1]` because
`Ext¹(𝒪_C, 𝒪_X(-C))` is one-dimensional and its nonsplit extension is `0 → 𝒪_X(-C) → 𝒪_X → 𝒪_C → 0`.
Mathlib has no twist functors, so these identities are not formalized; this file proves their
images on the Mukai lattice.

On classes, `T_S` acts by the reflection `ρ_{v(S)}` in the Mukai vector of `S`, and an exact
autoequivalence acts by an isometry. The reflection map is a conjugation-equivariant map from
roots to isometries, `ρ_{g δ} = g ρ_δ g⁻¹` (`reflection_smul`), so
`CoxeterMatrix.isBraidLiftable_of_equivariant` applies with the classes of `x₀, x₁` and the
lattice form of the object identities, `ρ_{x₁} ρ_{x₀} x₁ = x₀` and `ρ_{x₀} ρ_{x₁} x₀ = x₁`. This
gives the homomorphism `Art(A₂) →* O(Λ)`, `σ_i ↦ ρ_{v(x_i)}`, from real classes and a nonvacuous
edge identity (`a2Hom`). Its generators are involutions, so it factors through the Coxeter group
`W(A₂) = S₃` and kills the pure Artin group (`exists_factor_a2Hom`,
`a2Hom_eq_one_of_mem_pureArtinGroup`): the classes of twisted objects cannot tell elements of
the pure braid group apart.

Of the configurations elsewhere in the library, none has an edge with `m = 2` or `m = 3`: in
Picard rank one, distinct roots of positive rank pair to at most `-3`
(`MukaiVector.pairing_le_neg_three`), so their total Ext is at least `3`, and the two simples of a
wall of pairing two have total Ext `2`. Both give `m = ∞`, with no braid relation.

## Main definitions

* `isometries`: the isometries of the Mukai lattice `Λ = ℤ ⊕ NS(X) ⊕ ℤ`.
* `Root`: the spherical classes, on which `isometries` acts.
* `reflection`: the reflection in a root, as an isometry.
* `a2`: the classes `v(𝒪_X[1]) = -(1, 0, 1)` and `v(𝒪_C) = (0, C, 1)`.
* `a2Hom`: the homomorphism `Art(A₂) →* isometries`.
-/

namespace AlgebraicGeometry.K3.EllipticWithSection

open Mukai CoxeterSystem CoxeterMatrix

/-! ### Isometries and reflections -/

/-- The isometries of the Mukai lattice of `X`. -/
def isometries : Subgroup (MukaiLattice NS ≃ₗ[ℤ] MukaiLattice NS) where
  carrier := {g | ∀ v w, pairing intersection (g v) (g w) = pairing intersection v w}
  one_mem' _ _ := rfl
  mul_mem' {g h} hg hh v w := (hg (h v) (h w)).trans (hh v w)
  inv_mem' {g} hg v w := by
    have h := hg (g⁻¹ v) (g⁻¹ w)
    simp only [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] at h ⊢
    exact h.symm

theorem isometries_pairing (g : isometries) (v w : MukaiLattice NS) :
    pairing intersection (g.1 v) (g.1 w) = pairing intersection v w :=
  g.2 v w

/-- The spherical classes `δ² = -2` of the Mukai lattice of `X`. -/
abbrev Root : Type := {v : MukaiLattice NS // IsSpherical intersection v}

/-- Isometries act on roots. -/
instance : MulAction isometries Root where
  smul g δ := ⟨g.1 δ.1, by
    rw [isSpherical_iff, selfPairing_eq_pairing, isometries_pairing, ← selfPairing_eq_pairing]
    exact δ.2⟩
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp] theorem coe_smul (g : isometries) (δ : Root) : (g • δ).1 = g.1 δ.1 := rfl

/-- The reflection `ρ_δ(v) = v + ⟨v, δ⟩ δ` in a root, as an isometry; on classes it is the action
of the twist `T_S` of a spherical object of class `δ`. -/
def reflection (δ : Root) : isometries :=
  ⟨reflectEquiv intersection δ.1 δ.2,
    fun v w => pairing_reflect_reflect intersection intersection_comm δ.1 δ.2 v w⟩

@[simp] theorem reflection_apply (δ : Root) (v : MukaiLattice NS) :
    (reflection δ).1 v = v + pairing intersection v δ.1 • δ.1 := rfl

theorem reflection_sq (δ : Root) : reflection δ ^ 2 = 1 := by
  rw [sq]
  ext v : 2
  exact reflect_reflect intersection δ.1 δ.2 v

/-- **Reflections are conjugation-equivariant**: `ρ_{g δ} = g ρ_δ g⁻¹` for every isometry `g`.
It is the lattice image of `T_{Φ S} ≅ Φ T_S Φ⁻¹`. -/
theorem reflection_smul (g : isometries) (δ : Root) :
    reflection (g • δ) = g * reflection δ * g⁻¹ := by
  ext v : 2
  have hg : g.1 (g.1⁻¹ v) = v := by simp
  have hp : pairing intersection (g.1⁻¹ v) δ.1 = pairing intersection v (g.1 δ.1) := by
    rw [← isometries_pairing g, hg]
  change v + pairing intersection v (g.1 δ.1) • g.1 δ.1 = g.1 ((reflection δ).1 (g.1⁻¹ v))
  rw [reflection_apply, map_add, map_zsmul, hg, hp]

/-! ### The configuration -/

/-- `v(𝒪_X[1]) = -(1, 0, 1)` and `v(𝒪_C) = (0, C, 1)`. -/
def a2 : Fin 2 → Root :=
  ![⟨-lineBundle 0, (isSpherical_lineBundle 0).neg⟩, ⟨curveSheaf 0, isSpherical_curveSheaf 0⟩]

/-- `⟨v(𝒪_X[1]), v(𝒪_C)⟩ = 1`, i.e. `χ(𝒪_X, 𝒪_C) = 1`: the total Ext is one. -/
theorem pairing_a2 : pairing intersection (a2 0).1 (a2 1).1 = 1 := by
  simp [a2, curve]

/-- The Seidel–Thomas Coxeter matrix of the configuration is `A₂`. -/
theorem a2_eq_ofExt :
    CoxeterMatrix.A 2 = ofExt (fun i j : Fin 2 => if i = j then 2 else 1)
      (fun i j => by simp [eq_comm]) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- **The object identities of the configuration, on classes.** `ρ_{x₁} ρ_{x₀} x₁ = x₀` and
`ρ_{x₀} ρ_{x₁} x₀ = x₁`: the images of `T_{𝒪_C} T_{𝒪_X} 𝒪_C ≅ 𝒪_X[1]` and its mirror. -/
theorem a2_edge (i i' : Fin 2) (hii : i ≠ i') :
    ((alternatingWord i' i (CoxeterMatrix.A 2 i i' - 1)).map (reflection ∘ a2)).prod • a2 i' =
      a2 (if Even (CoxeterMatrix.A 2 i i' - 1) then i else i') := by
  fin_cases i <;> fin_cases i'
  all_goals first
    | exact absurd rfl hii
    | apply Subtype.ext
      simp [CoxeterMatrix.A, alternatingWord, a2, curve, mul_smul, coe_smul, reflection_apply]

/-- **The braid relation of the `A₂` configuration on classes**, from the equivariant criterion:
`ρ_{x₀} ρ_{x₁} ρ_{x₀} = ρ_{x₁} ρ_{x₀} ρ_{x₁}`. -/
theorem isBraidLiftable_a2 : (CoxeterMatrix.A 2).IsBraidLiftable (reflection ∘ a2) :=
  (CoxeterMatrix.A 2).isBraidLiftable_of_equivariant reflection a2
    (fun g i => reflection_smul g (a2 i)) fun i i' hii _ => a2_edge i i' hii

/-- **The Artin group of the configuration acts on the Mukai lattice**, `σ_i ↦ ρ_{v(x_i)}`. -/
def a2Hom : (CoxeterMatrix.A 2).ArtinGroup →* isometries :=
  ArtinGroup.lift _ isBraidLiftable_a2

@[simp] theorem a2Hom_of (i : Fin 2) :
    a2Hom ((CoxeterMatrix.A 2).artinGen i) = reflection (a2 i) :=
  ArtinGroup.lift_of _ _ i

/-- The action on the Mukai lattice factors through the Coxeter group `W(A₂)`. -/
theorem exists_factor_a2Hom :
    ∃ ψ : (CoxeterMatrix.A 2).Group →* isometries,
      ψ.comp (CoxeterMatrix.A 2).toCoxeterGroup = a2Hom :=
  (CoxeterMatrix.A 2).exists_factor_of_sq a2Hom fun i => by
    rw [a2Hom_of]; exact reflection_sq _

/-- **Classes cannot see pure braids**: every element of the pure Artin group of the
configuration acts trivially on the Mukai lattice. -/
theorem a2Hom_eq_one_of_mem_pureArtinGroup {g : (CoxeterMatrix.A 2).ArtinGroup}
    (hg : g ∈ (CoxeterMatrix.A 2).pureArtinGroup) : a2Hom g = 1 :=
  (CoxeterMatrix.A 2).pure_mem_ker_of_sq a2Hom
    (fun i => by rw [a2Hom_of]; exact reflection_sq _) hg

end AlgebraicGeometry.K3.EllipticWithSection
