/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.Lattice.Mukai.AffineWeyl.Group

/-!
# Length-zero elements: isometries permuting the affine simple roots

In the extended affine Weyl group `W ⋉ P^∨` the elements of length zero are those that permute the
affine simple roots; they act on the extended Dynkin diagram, and their permutations form a group
isomorphic to `P^∨/Q^∨` (Iwahori–Matsumoto, *On some Bruhat decomposition and the structure of
the Hecke rings of 𝔭-adic Chevalley groups*, 1965; Bourbaki, *Groupes et algèbres de Lie*,
Ch. VI, §2.3). On the Mukai lattice, for a minuscule node `j` and a class `Mⱼ` with
`Mⱼ·Cᵢ = δᵢⱼ`, the isometry `⊗𝒪(Mⱼ) ∘ ρ_{w₀^{(j)} w₀}` permutes `α₀, …, α_l`, sending `α₀` to `αⱼ`.

This file proves the class-level statements that need no weight lattice and no longest element:

* `FundamentalCycle.affineRootStabilizer`: the automorphisms of the Mukai lattice that permute the
  affine simple roots, a subgroup; `FundamentalCycle.affineRootPerm` is the homomorphism to the
  permutations of the nodes, well defined because the affine simple roots are distinct
  (`affineRoot_injective`). **The induced permutations form a group**, its range. The isometries
  themselves are not determined by their permutation: `⊗𝒪(L)` with `L ⊥ Cᵢ` for all `i` fixes
  every affine root (`tensorLine_fixes_affineRoot_iff`). So a choice of one isometry per
  permutation need not be closed under composition; on the elliptic K3 surface with a section the
  length-zero element of the curve wall squares to `⊗𝒪(H) ≠ 1`.
* **An isometry permuting the affine simple roots preserves the extended Dynkin matrix and the
  marks** (`affineCartan_perm`, `nullMult_perm`), and fixes the class of a point
  (`apply_corankUnit_of_perm`). So the image of `α₀` is a node of mark one
  (`nullMult_perm_none`): `α₀` itself or a node with `zⱼ = 1`. The proof: the image of
  `δ = Σ zₖ αₖ` is isotropic and supported on the affine roots, hence a multiple of `δ` by the
  description of the isotropic vectors of the extended Dynkin matrix, and the multiple is one
  because a permutation preserves the sum of the coordinates.

The identification of the permutation group with `P^∨/Q^∨`, and the existence of a length-zero
element for every minuscule node, need the weight lattice and the longest elements of `W` and are
not formalized here; the `A₁` case on the elliptic K3 surface with a section is checked by hand
in `AlgebraicGeometry/Surface/K3/EllipticWithSection/AffineWeyl.lean`.
-/

open Matrix

namespace Mukai

variable {N : Type*} [AddCommGroup N]

/-- Automorphisms of the Mukai lattice. -/
local notation "Aut(Λ)" => MukaiLattice ℤ N ≃ₗ[ℤ] MukaiLattice ℤ N

namespace FundamentalCycle

variable {b : N →ₗ[ℤ] N →ₗ[ℤ] ℤ} {ι : Type*} [Fintype ι] (F : FundamentalCycle b ι)

/-- **The affine simple roots are distinct.** -/
theorem affineRoot_injective : Function.Injective F.affineRoot := by
  intro k l h
  cases k with
  | none =>
    cases l with
    | none => rfl
    | some j => simpa using congrArg (fun v : MukaiLattice ℤ N => v.2.2) h
  | some i =>
    cases l with
    | none => simpa using congrArg (fun v : MukaiLattice ℤ N => v.2.2) h
    | some j =>
      have hij : F.curve i = F.curve j := by
        simpa using congrArg (fun v : MukaiLattice ℤ N => v.2.1) h
      by_contra hne
      have := F.curve_nonneg i j fun e => hne (congrArg some e)
      rw [← hij, F.curve_self] at this
      norm_num at this

/-- **The stabilizer of the affine simple roots**: the automorphisms of the Mukai lattice that
permute `α₀, …, α_l`. -/
def affineRootStabilizer : Subgroup Aut(Λ) where
  carrier := {g | ∃ σ : Equiv.Perm (Option ι), ∀ k, g (F.affineRoot k) = F.affineRoot (σ k)}
  one_mem' := ⟨1, fun _ => rfl⟩
  mul_mem' := by
    rintro g h ⟨σ, hσ⟩ ⟨τ, hτ⟩
    exact ⟨σ * τ, fun k => by rw [mul_apply_eq_comp, hτ, hσ, Equiv.Perm.mul_apply]⟩
  inv_mem' := by
    rintro g ⟨σ, hσ⟩
    exact ⟨σ⁻¹, fun k => by
      rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_eq, hσ]
      simp⟩

theorem exists_perm_of_mem_affineRootStabilizer {g : Aut(Λ)} (hg : g ∈ F.affineRootStabilizer) :
    ∃ σ : Equiv.Perm (Option ι), ∀ k, g (F.affineRoot k) = F.affineRoot (σ k) :=
  hg

/-- **The permutation of the nodes** induced by an automorphism permuting the affine simple
roots, as a group homomorphism. -/
noncomputable def affineRootPerm : F.affineRootStabilizer →* Equiv.Perm (Option ι) where
  toFun g := Classical.choose g.2
  map_one' := by
    refine Equiv.ext fun k => ?_
    apply F.affineRoot_injective
    rw [← Classical.choose_spec (1 : F.affineRootStabilizer).2 k]
    rfl
  map_mul' g h := by
    refine Equiv.ext fun k => ?_
    apply F.affineRoot_injective
    rw [← Classical.choose_spec (g * h).2 k, Equiv.Perm.mul_apply,
      ← Classical.choose_spec g.2, ← Classical.choose_spec h.2]
    rfl

/-- `g αₖ = α_{σ(k)}` for the induced permutation `σ`. -/
theorem apply_affineRoot (g : F.affineRootStabilizer) (k : Option ι) :
    (g : Aut(Λ)) (F.affineRoot k) = F.affineRoot (F.affineRootPerm g k) :=
  Classical.choose_spec g.2 k

/-- The induced permutation is the only permutation that `g` realizes. -/
theorem affineRootPerm_eq (g : F.affineRootStabilizer) {σ : Equiv.Perm (Option ι)}
    (hσ : ∀ k, (g : Aut(Λ)) (F.affineRoot k) = F.affineRoot (σ k)) :
    F.affineRootPerm g = σ := by
  refine Equiv.ext fun k => ?_
  apply F.affineRoot_injective
  rw [← apply_affineRoot, hσ]

/-- **The permutations of the nodes induced by the automorphisms permuting the affine simple
roots form a group**, the range of `affineRootPerm`. -/
noncomputable def affineRootPermGroup : Subgroup (Equiv.Perm (Option ι)) :=
  F.affineRootPerm.range

/-! ### Marks and the extended Dynkin matrix -/

variable {F}

/-- An isometry permuting the affine simple roots preserves the extended Dynkin matrix. -/
theorem affineCartan_perm {g : Aut(Λ)} (hg : g ∈ orthogonalGroup b) {σ : Equiv.Perm (Option ι)}
    (hσ : ∀ k, g (F.affineRoot k) = F.affineRoot (σ k)) (k l : Option ι) :
    F.affineCartan (σ k) (σ l) = F.affineCartan k l := by
  simp only [affineCartan, LinearMap.BilinForm.wallMatrix_apply, ← hσ, hg _ _]

/-- **An isometry permuting the affine simple roots preserves the marks**: `z_{σ(k)} = z_k`. -/
theorem nullMult_perm {g : Aut(Λ)} (hg : g ∈ orthogonalGroup b) {σ : Equiv.Perm (Option ι)}
    (hσ : ∀ k, g (F.affineRoot k) = F.affineRoot (σ k)) (k : Option ι) :
    F.nullMult (σ k) = F.nullMult k := by
  set x : Option ι → ℤ := fun l => F.nullMult (σ.symm l) with hx
  -- `Σ xₗ αₗ = g δ`
  have hsum : ∑ l, x l • F.affineRoot l = g corankUnit := by
    rw [← F.sum_nullMult_smul_affineRoot, map_sum]
    rw [← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [hx, hσ]
  -- `x` is isotropic, hence a multiple of the marks
  have hiso : x ⬝ᵥ F.affineCartan *ᵥ x = 0 := by
    have h := LinearMap.BilinForm.apply_sum_smul_self (mukaiForm b) F.affineRoot x
    rw [hsum, hg, show mukaiForm b corankUnit corankUnit = 0 by simp [corankUnit]] at h
    rw [affineCartan]
    linarith
  have hx' := F.eq_smul_nullMult_of_isotropic hiso
  -- the multiple is one: a permutation preserves the sum of the coordinates
  have hsumx : ∑ l, x l = ∑ l, F.nullMult l := by
    rw [hx]
    exact Equiv.sum_comp σ.symm F.nullMult
  have hpos : 0 < ∑ l, F.nullMult l :=
    Finset.sum_pos (fun l _ => F.nullMult_pos l) Finset.univ_nonempty
  have h1 : x none = 1 := by
    have : ∑ l, x l = x none * ∑ l, F.nullMult l := by
      conv_lhs => rw [hx']
      simp only [Fintype.sum_option, Pi.smul_apply, smul_eq_mul, nullMult_none, nullMult_some]
      rw [mul_add, mul_one, Finset.mul_sum]
    rw [hsumx] at this
    nlinarith
  have := congrFun hx' (σ k)
  rw [h1, one_smul] at this
  simpa [hx] using this.symm

/-- **The image of `α₀` has mark one.** -/
theorem nullMult_perm_none {g : Aut(Λ)} (hg : g ∈ orthogonalGroup b)
    {σ : Equiv.Perm (Option ι)} (hσ : ∀ k, g (F.affineRoot k) = F.affineRoot (σ k)) :
    F.nullMult (σ none) = 1 := by
  rw [nullMult_perm hg hσ, nullMult_none]

/-- An isometry permuting the affine simple roots fixes the class `δ` of a point. -/
theorem apply_corankUnit_of_perm {g : Aut(Λ)} (hg : g ∈ orthogonalGroup b)
    {σ : Equiv.Perm (Option ι)} (hσ : ∀ k, g (F.affineRoot k) = F.affineRoot (σ k)) :
    g corankUnit = corankUnit := by
  rw [← F.sum_nullMult_smul_affineRoot, map_sum]
  conv_rhs => rw [← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [hσ, nullMult_perm hg hσ]

end FundamentalCycle

end Mukai
