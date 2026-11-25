/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.EllipticWithSection.Lattice
import K3Twists.LinearAlgebra.Lattice.Mukai.AffineWeyl.Index
import K3Twists.LinearAlgebra.Lattice.Mukai.AffineWeyl.LengthZero

/-!
# The affine Weyl group of the curve wall

On the elliptic K3 surface `X` with a section `C` and fibre class `F` of
`EllipticWithSection/Lattice.lean`, `NS(X) = ℤC ⊕ ℤF`, the polarization `H = C + 2F` has `H·C = 0`
and contracts the section. The exceptional fibre of that contraction is the single curve `C`, of
type `A₁`, with fundamental cycle `Θ = C` (`sectionFibre`): a `Mukai.FundamentalCycle` built from
the classes of the lattice, with every field checked on `NS(X)`. Its affine simple roots are the
classes of the two spherical simples of the curve wall,

```
α₀ = v(𝒪_C) = (0, C, 1) = wallA,   α₁ = v(𝒪_C(-1)[1]) = (0, -C, 0) = wallB,
```

with `α₀ + α₁ = v(𝒪_x)` (`sectionFibre_affineRoot_none`, `sectionFibre_affineRoot_some`).

* **The Riemann–Roch membership field holds on `NS(X)`** (`sectionFibre_riemannRochMembership`):
  the classes orthogonal to `H` are the multiples of `C`. So the fundamental-alcove theorem
  applies with no field left: for `0 < β·C < 1`, no rank-zero root `(0, c, s)` with `H·c = 0` has
  `β·c = s` (`fibreCharge_ne_zero_of_mem_alcove`).
* **`W_aff = E(Q) ⋊ W(A₁)`** for the curve wall, with `ρ_{wallA}` and `ρ_{wallB}` in `W_aff`
  (`affineWeyl_sectionFibre_eq_sup`, `reflectEquiv_wallA_mem_affineWeyl`,
  `reflectEquiv_wallB_mem_affineWeyl`).
* **The translation lattices** (`degreeLattice_sectionFibre`,
  `polarizedDegreeLattice_sectionFibre`, `index_corootLattice_sectionFibre`): line bundles act on
  the affine roots through `L ↦ L·C`, which is onto `ℤ` (`F·C = 1`), while the classes orthogonal
  to `H` give `Λ_H = 2ℤ = Q^∨`, of index `2 = det A₁`. So `Λ/Q^∨ = P^∨/Q^∨ = ℤ/2`.
* **The length-zero element** `π = ⊗𝒪(F) ∘ ρ_{wallB}` swaps `wallA` and `wallB` and fixes
  `v(𝒪_x)` (`lengthZero_wallA`, `lengthZero_wallB`, `lengthZero_point`): it permutes the affine
  simple roots by the nontrivial automorphism of the extended diagram `Ã₁`
  (`affineRootPerm_lengthZero`). Its square is `⊗𝒪(H)` (`lengthZero_mul_self`), which fixes the
  affine roots but is not the identity (`lengthZero_mul_self_ne_one`): the permutations form the
  group `ℤ/2`, the isometries realizing them do not.

**Fields.** The structure `Mukai.FundamentalCycle` and the Riemann–Roch membership field are
lattice-level statements, and both are checked here on the lattice `NS(X)` of the curve wall
rather than assumed. That `C` is the exceptional fibre of the contraction by `H`, and that the
simple objects of the wall are `𝒪_C` and `𝒪_C(-1)[1]`, are geometry and are not formalized.
-/

namespace AlgebraicGeometry.K3.EllipticWithSection

open Mukai Mukai.FundamentalCycle

/-! ### The fibre -/

/-- **The exceptional fibre of the contraction of the section** `C` by `H = C + 2F`: the curve `C`,
of type `A₁`, with fundamental cycle `Θ = C`. -/
def sectionFibre : FundamentalCycle intersection Unit where
  curve _ := curve
  mult _ := 1
  curve_self _ := by simp [curve]
  curve_nonneg i j h := absurd (Subsingleton.elim i j) h
  negDef d hd := by
    have h0 : d () ≠ 0 := fun h0 => hd (funext fun u => by cases u; exact h0)
    have : 0 < d () ^ 2 := by positivity
    simp [curve]
    nlinarith
  connected := by
    rw [Matrix.isIndecomposable_iff_reflTransGen]
    intro i j
    rw [Subsingleton.elim i j]
  mult_nonneg _ := zero_le_one
  cycle_self := by simp [curve]
  cycle_curve_nonpos _ := by simp [curve]

@[simp] theorem sectionFibre_curve (u : Unit) : sectionFibre.curve u = curve := rfl

@[simp] theorem sectionFibre_mult (u : Unit) : sectionFibre.mult u = 1 := rfl

theorem sectionFibre_cycle : sectionFibre.cycle = curve := by
  simp [cycle]

/-- `α₀ = v(𝒪_C) = wallA`. -/
theorem sectionFibre_affineRoot_none : sectionFibre.affineRoot none = wallA := by
  simp [sectionFibre_cycle, wallA]

/-- `α₁ = v(𝒪_C(-1)[1]) = wallB`. -/
theorem sectionFibre_affineRoot_some (u : Unit) : sectionFibre.affineRoot (some u) = wallB := by
  simp [wallB]

/-! ### The fundamental-alcove theorem on the curve wall -/

/-- **The Riemann–Roch membership field holds on `NS(X)`**: every class orthogonal to `H` is a
multiple of `C`. -/
theorem sectionFibre_riemannRochMembership :
    sectionFibre.RiemannRochMembership polarization where
  mem c hcH _ := by
    obtain ⟨a, b'⟩ := c
    have hb' : b' = 0 := by simp at hcH; linarith
    subst hb'
    exact ⟨fun _ => a, by ext <;> simp [combination_apply, curve]⟩

/-- **The fundamental-alcove theorem on the curve wall.** For `0 < β·C < 1`, no rank-zero root
`(0, c, s)` with `H·c = 0` has `Z = β·c - s = 0`. -/
theorem fibreCharge_ne_zero_of_mem_alcove {β : NS →+ ℝ} (h0 : 0 < β curve) (h1 : β curve < 1)
    {c : NS} (hcH : intersection c polarization = 0) (hc : intersection c c = -2) (s : ℤ) :
    β c - s ≠ 0 := by
  have hβ : sectionFibre.IsInFundamentalAlcove β :=
    ⟨fun _ => h0, by rwa [sectionFibre_cycle]⟩
  simpa using sectionFibre.fibreCharge_ne_zero_of_riemannRochMembership intersection_comm
    sectionFibre_riemannRochMembership hβ hcH hc s

/-! ### The affine Weyl group -/

/-- `W_aff = E(Q) ⊔ W(A₁)` for the curve wall. -/
theorem affineWeyl_sectionFibre_eq_sup :
    sectionFibre.affineWeyl = sectionFibre.translations ⊔ sectionFibre.finiteWeyl :=
  sectionFibre.affineWeyl_eq_sup intersection_comm

theorem curve_mem_rootLattice : curve ∈ sectionFibre.rootLattice :=
  ⟨fun _ => 1, by simp [combination_apply]⟩

/-- The twist by `𝒪_C` acts in the affine Weyl group of the curve wall. -/
theorem reflectEquiv_wallA_mem_affineWeyl :
    reflectEquiv intersection wallA isSpherical_wallA ∈ sectionFibre.affineWeyl :=
  Subgroup.subset_closure ⟨curve, curve_mem_rootLattice, 1, isSpherical_wallA, rfl⟩

/-- The twist by `𝒪_C(-1)[1]` acts in the affine Weyl group of the curve wall. -/
theorem reflectEquiv_wallB_mem_affineWeyl :
    reflectEquiv intersection wallB isSpherical_wallB ∈ sectionFibre.affineWeyl := by
  have h : wallB = ((0 : ℤ), -curve, (0 : ℤ)) := by ext <;> simp [wallB]
  have hs : IsSpherical intersection ((0 : ℤ), -curve, (0 : ℤ)) := by
    simp [IsSpherical, curve]
  have : reflectEquiv intersection wallB isSpherical_wallB =
      reflectEquiv intersection (0, -curve, 0) hs :=
    LinearEquiv.ext fun v => by simp only [reflectEquiv_apply, h]
  rw [this]
  exact Subgroup.subset_closure ⟨-curve, neg_mem curve_mem_rootLattice, 0, hs, rfl⟩

/-! ### The translation lattices -/

/-- `Λ = ℤ`: `F·C = 1`. -/
theorem degreeLattice_sectionFibre : sectionFibre.degreeLattice = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ⟨x () • fibre, ?_⟩
  ext u
  simp [fibre, curve]

/-- `Λ_H = Q^∨ = 2ℤ`: the classes orthogonal to `H` are the multiples of `C`, of degree `-2`. -/
theorem polarizedDegreeLattice_sectionFibre :
    sectionFibre.polarizedDegreeLattice polarization = sectionFibre.corootLattice := by
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨a, b'⟩ := c
    have hb' : b' = 0 := by simp at hc; linarith
    subst hb'
    refine ⟨fun _ => -a, ?_⟩
    ext u
    simp [Matrix.mulVec, dotProduct, curve]
  · rintro ⟨d, rfl⟩
    refine ⟨(-d (), 0), by simp; ring, ?_⟩
    ext u
    simp [Matrix.mulVec, dotProduct, curve]

/-- `det A₁ = 2`. -/
theorem det_cartan_sectionFibre : sectionFibre.cartan.det = 2 := by
  simp [Matrix.det_unique, curve]

/-- **`[Λ : Q^∨] = 2`**: `Λ/Q^∨ = P^∨/Q^∨ = ℤ/2`. -/
theorem index_corootLattice_sectionFibre :
    sectionFibre.corootLattice.toAddSubgroup.index = 2 := by
  rw [index_corootLattice, det_cartan_sectionFibre]
  rfl

/-! ### The length-zero element -/

theorem two_mul_zero_eq_fibre : 2 * (0 : ℤ) = intersection fibre fibre := by
  simp [fibre]

/-- **The length-zero element of the curve wall**, `π = ⊗𝒪(F) ∘ ρ_{wallB}`. -/
def lengthZero : MukaiLattice ℤ NS ≃ₗ[ℤ] MukaiLattice ℤ NS :=
  tensorLineEquiv intersection_comm fibre two_mul_zero_eq_fibre *
    reflectEquiv intersection wallB isSpherical_wallB

/-- `π (r, (x, y), s) = (r, (y - x, y + r), s + y - x)`. -/
theorem lengthZero_apply (r x y s : ℤ) :
    lengthZero ((r, (x, y), s) : MukaiLattice ℤ NS) = (r, (y - x, y + r), s + y - x) := by
  simp only [lengthZero, mul_apply_eq_comp, tensorLineEquiv_apply, reflectEquiv_apply,
    reflect_apply]
  ext <;> simp [wallB, fibre, curve] <;> ring

/-- `π wallA = wallB`. -/
theorem lengthZero_wallA : lengthZero wallA = wallB := by
  ext <;> simp [show wallA = ((0 : ℤ), ((1 : ℤ), (0 : ℤ)), (1 : ℤ)) from rfl, lengthZero_apply,
    wallB, curve]

/-- `π wallB = wallA`. -/
theorem lengthZero_wallB : lengthZero wallB = wallA := by
  have : wallB = ((0 : ℤ), ((-1 : ℤ), (0 : ℤ)), (0 : ℤ)) := by ext <;> simp [wallB, curve]
  rw [this, lengthZero_apply]
  ext <;> simp [wallA, curve]

/-- `π v(𝒪_x) = v(𝒪_x)`. -/
theorem lengthZero_point : lengthZero point = point := by
  rw [show point = ((0 : ℤ), ((0 : ℤ), (0 : ℤ)), (1 : ℤ)) from rfl, lengthZero_apply]
  rfl

theorem lengthZero_mem_orthogonalGroup : lengthZero ∈ orthogonalGroup intersection :=
  mul_mem (tensorLineEquiv_mem_orthogonalGroup _ _ _)
    (reflectEquiv_mem_orthogonalGroup intersection_comm _ _)

theorem lengthZero_perm (k : Option Unit) :
    lengthZero (sectionFibre.affineRoot k) =
      sectionFibre.affineRoot (Equiv.swap none (some ()) k) := by
  rcases k with _ | ⟨⟨⟩⟩
  · rw [Equiv.swap_apply_left, sectionFibre_affineRoot_none, sectionFibre_affineRoot_some,
      lengthZero_wallA]
  · rw [Equiv.swap_apply_right, sectionFibre_affineRoot_none, sectionFibre_affineRoot_some,
      lengthZero_wallB]

theorem lengthZero_mem_affineRootStabilizer :
    lengthZero ∈ sectionFibre.affineRootStabilizer :=
  ⟨_, lengthZero_perm⟩

/-- **`π` permutes the affine simple roots by the automorphism of `Ã₁`.** -/
theorem affineRootPerm_lengthZero :
    sectionFibre.affineRootPerm ⟨lengthZero, lengthZero_mem_affineRootStabilizer⟩ =
      Equiv.swap none (some ()) :=
  sectionFibre.affineRootPerm_eq _ lengthZero_perm

theorem two_mul_one_eq_polarization : 2 * (1 : ℤ) = intersection polarization polarization := by
  simp [polarization]

/-- **`π² = ⊗𝒪(H)`.** -/
theorem lengthZero_mul_self :
    lengthZero * lengthZero =
      tensorLineEquiv intersection_comm polarization two_mul_one_eq_polarization := by
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨r, ⟨x, y⟩, s⟩ := v
  rw [mul_apply_eq_comp, lengthZero_apply, lengthZero_apply, tensorLineEquiv_apply]
  ext <;> simp [polarization] <;> ring

/-- **`π² ≠ 1`**: the length-zero isometry has infinite order, although its permutation of the
affine roots has order two. -/
theorem lengthZero_mul_self_ne_one : lengthZero * lengthZero ≠ 1 := by
  intro h
  have := congrArg (fun g : MukaiLattice ℤ NS ≃ₗ[ℤ] MukaiLattice ℤ NS =>
    (g ((1 : ℤ), ((0 : ℤ), (0 : ℤ)), (0 : ℤ))).2.1.1) h
  simp [lengthZero_mul_self, polarization] at this

end AlgebraicGeometry.K3.EllipticWithSection
