/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.RootSystem.Spherical
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.RingTheory.Localization.BaseChange

/-!
# The root system of a stratum over `ℚ`, and bases of `A₁` strata

At a period `Z : N →+ W` of a lattice `N` with a symmetric form `B`, the kernel root system
(`RootPairing.kernelRootPairing`) is the spherical pairing of the lattice `ker Z ∩ N` over `ℤ`.
Over `ℤ` it is not a Mathlib root system in general (its coroots need not span the dual). This
file builds the rational one and the bases of the strata of type `A₁`.

* `RootPairing.kernelRootSystem`: **the root system of a stratum over `ℚ`**, on the span of the
  roots in the rational kernel space `V = ℚ ⊗ (ker Z ∩ N)` (`RootPairing.kernelSpace`), with the
  base change of the form (`RootPairing.kernelFormRat`). It is `RootPairing.latticeRootSystem`
  for the lattice `ker Z ∩ N ⊆ V`, so it is a finite `IsRootSystem`. Definiteness is needed only on
  the lattice points of `ker Z`: it passes to `V` because every vector of `V` has a nonzero
  integer multiple in the lattice (`RootPairing.kernelFormRat_neg`).
* `RootPairing.mem_latticeRoots_kernelLatticeRat_iff`: its roots are the vectors `1 ⊗ δ` for the
  kernel roots `δ`.
* `RootPairing.baseOfEqOrNeg`: a root pairing all of whose roots are `±α` has the base `{α}`;
  `RootPairing.cartanMatrix_baseOfEqOrNeg`: its Cartan matrix is `(2)`, type `A₁`.
* `RootPairing.kernelRootPairingBaseOfEq`, `RootPairing.kernelRootSystemBaseOfEq`: **the bases of
  an `A₁` stratum.** If the kernel roots are `±δ`, then `{δ}` is a base of the kernel root pairing
  over `ℤ` and `{1 ⊗ δ}` a base of the kernel root system over `ℚ`.

The rational space `V` is a `ℚ`-model of the real kernel `ker Z_* ⊆ N_ℝ` of the notes, not that
real space itself; for the lattice statements here the two have the same roots.
-/

open Module Set Function TensorProduct

namespace RootPairing

/-! ### A base when every root is `±α` -/

section A1

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

/-- **A base of a pairing of type `A₁`.** If every root is `α` or `-α` for the root
`α = root i₀`, then `{i₀}` is a base. -/
noncomputable def baseOfEqOrNeg [NeZero (2 : R)] [IsDomain R] [Module.IsTorsionFree R M]
    [Module.IsTorsionFree R N] (P : RootPairing ι R M N) (i₀ : ι)
    (h : ∀ i, P.root i = P.root i₀ ∨ P.root i = -P.root i₀) : P.Base where
  support := {i₀}
  linearIndepOn_root := by
    rw [Finset.coe_singleton, linearIndepOn_singleton_iff]
    exact P.ne_zero i₀
  linearIndepOn_coroot := by
    rw [Finset.coe_singleton, linearIndepOn_singleton_iff]
    exact P.ne_zero' i₀
  root_mem_or_neg_mem i := by
    have hmem : P.root i₀ ∈ AddSubmonoid.closure (P.root '' ↑({i₀} : Finset ι)) :=
      AddSubmonoid.subset_closure ⟨i₀, by simp, rfl⟩
    rcases h i with hi | hi
    · exact Or.inl (hi ▸ hmem)
    · exact Or.inr (by rw [hi, neg_neg]; exact hmem)
  coroot_mem_or_neg_mem i := by
    have hmem : P.coroot i₀ ∈ AddSubmonoid.closure (P.coroot '' ↑({i₀} : Finset ι)) :=
      AddSubmonoid.subset_closure ⟨i₀, by simp, rfl⟩
    rcases h i with hi | hi
    · exact Or.inl (P.root.injective hi ▸ hmem)
    · refine Or.inr ?_
      rw [(P.coroot_eq_neg_iff).mpr ((P.root_eq_neg_iff).mp hi), neg_neg]
      exact hmem

@[simp]
lemma baseOfEqOrNeg_support [NeZero (2 : R)] [IsDomain R] [Module.IsTorsionFree R M]
    [Module.IsTorsionFree R N] (P : RootPairing ι R M N) (i₀ : ι)
    (h : ∀ i, P.root i = P.root i₀ ∨ P.root i = -P.root i₀) :
    (P.baseOfEqOrNeg i₀ h).support = {i₀} :=
  rfl

/-- **The Cartan matrix of an `A₁` base is `(2)`.** -/
theorem cartanMatrix_baseOfEqOrNeg [NeZero (2 : R)] [IsDomain R] [FaithfulSMul ℤ R]
    [Module.IsTorsionFree R M] [Module.IsTorsionFree R N] (P : RootPairing ι R M N)
    [P.IsCrystallographic] (i₀ : ι)
    (h : ∀ i, P.root i = P.root i₀ ∨ P.root i = -P.root i₀)
    (i j : (P.baseOfEqOrNeg i₀ h).support) : (P.baseOfEqOrNeg i₀ h).cartanMatrix i j = 2 := by
  have hi : (i : ι) = i₀ := Finset.mem_singleton.mp i.2
  have hj : (j : ι) = i₀ := Finset.mem_singleton.mp j.2
  rw [Base.cartanMatrix, Base.cartanMatrixIn_def, hi, hj, pairingIn_same]

end A1

/-! ### The rational kernel space -/

section Kernel

variable {N W : Type*} [AddCommGroup N] [AddCommGroup W] (B : N →ₗ[ℤ] N →ₗ[ℤ] ℤ) (Z : N →+ W)

/-- The rational kernel space `ℚ ⊗ (ker Z ∩ N)`. -/
abbrev kernelSpace : Type _ :=
  ℚ ⊗[ℤ] kernelLattice Z

/-- The form on the rational kernel space: the base change of `B` on `ker Z ∩ N`. -/
noncomputable def kernelFormRat : LinearMap.BilinForm ℚ (kernelSpace Z) :=
  LinearMap.BilinForm.baseChange ℚ (kernelForm B Z)

/-- The lattice `ker Z ∩ N` inside the rational kernel space, as the image of `x ↦ 1 ⊗ x`. -/
noncomputable def kernelLatticeRat : Submodule ℤ (kernelSpace Z) :=
  LinearMap.range (TensorProduct.mk ℤ ℚ (kernelLattice Z) 1).toAddMonoidHom.toIntLinearMap

variable {B Z}

@[simp]
lemma kernelFormRat_tmul (a b : ℚ) (x y : kernelLattice Z) :
    kernelFormRat B Z (a ⊗ₜ x) (b ⊗ₜ y) = (B x y : ℚ) * (a * b) := by
  simp [kernelFormRat, zsmul_eq_mul]

lemma mem_kernelLatticeRat {v : kernelSpace Z} :
    v ∈ kernelLatticeRat Z ↔ ∃ x : kernelLattice Z, (1 : ℚ) ⊗ₜ x = v :=
  Iff.rfl

instance [Module.Finite ℤ N] : Module.Finite ℤ (kernelLatticeRat Z) := by
  unfold kernelLatticeRat
  infer_instance

/-- The form on the rational kernel space is symmetric when `B` is. -/
theorem kernelFormRat_comm (hB : ∀ x y, B x y = B y x) (v w : kernelSpace Z) :
    kernelFormRat B Z v w = kernelFormRat B Z w v := by
  induction v using TensorProduct.inductionOn with
  | tmul a x =>
    induction w using TensorProduct.inductionOn with
    | tmul b y => rw [kernelFormRat_tmul, kernelFormRat_tmul, hB, mul_comm a]
    | add w₁ w₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | add v₁ v₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]

/-- **Definiteness passes to the rational kernel space.** If `B` is negative on the nonzero
lattice points of `ker Z`, the base change is negative on every nonzero vector of `V`: some
nonzero integer multiple `s • v` is a lattice vector `1 ⊗ x`, and `s² B(v, v) = B(x, x)`. -/
theorem kernelFormRat_neg (hD : ∀ v, Z v = 0 → v ≠ 0 → B v v < 0) (v : kernelSpace Z)
    (hv : v ≠ 0) : kernelFormRat B Z v v < 0 := by
  obtain ⟨⟨x, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ)
    (TensorProduct.mk ℤ ℚ (kernelLattice Z) 1) v
  simp only [TensorProduct.mk_apply, Submonoid.smul_def] at hs
  have hs0 : ((s : ℤ) : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero s
  have hsv : (s : ℤ) • v = ((s : ℤ) : ℚ) • v := (Int.cast_smul_eq_zsmul ℚ _ v).symm
  have hx : x ≠ 0 := by
    rintro rfl
    rw [TensorProduct.tmul_zero, hsv] at hs
    exact hv ((smul_eq_zero.mp hs).resolve_left hs0)
  have hxx : B x x < 0 := hD x x.2 fun h => hx (Subtype.ext h)
  have key : ((s : ℤ) : ℚ) ^ 2 * kernelFormRat B Z v v = (B x x : ℚ) := by
    have := kernelFormRat_tmul (B := B) (Z := Z) 1 1 x x
    rw [← hs, hsv] at this
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, mul_one] at this
    linear_combination this
  have hpos : 0 < ((s : ℤ) : ℚ) ^ 2 := by positivity
  have : ((s : ℤ) : ℚ) ^ 2 * kernelFormRat B Z v v < 0 := by
    rw [key]
    exact_mod_cast hxx
  exact neg_of_mul_neg_right this hpos.le

/-- The form takes integral values on the lattice `ker Z ∩ N ⊆ V`. -/
theorem kernelLatticeRat_integral :
    ∀ x ∈ kernelLatticeRat Z, ∀ y ∈ kernelLatticeRat Z, ∃ n : ℤ, kernelFormRat B Z x y = n := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  exact ⟨B x y, by simp⟩

variable [Module.Finite ℤ N]

/-- **The root system of a stratum over `ℚ`**: the roots of the lattice `ker Z ∩ N` in the rational
kernel space `V = ℚ ⊗ (ker Z ∩ N)`, a root pairing on the span of its roots
(`RootPairing.latticeRootSystem`). -/
noncomputable abbrev kernelRootSystem (hB : ∀ x y, B x y = B y x)
    (hD : ∀ v, Z v = 0 → v ≠ 0 → B v v < 0) :
    RootPairing (latticeRoots (kernelFormRat B Z) (kernelLatticeRat Z)) ℚ
      (Submodule.span ℚ (range (latticePairing (kernelFormRat_comm hB) (kernelFormRat_neg hD)
        (kernelLatticeRat Z) kernelLatticeRat_integral).root))
      (Submodule.span ℚ (range (latticePairing (kernelFormRat_comm hB) (kernelFormRat_neg hD)
        (kernelLatticeRat Z) kernelLatticeRat_integral).coroot)) :=
  latticeRootSystem (kernelFormRat_comm hB) (kernelFormRat_neg hD) (kernelLatticeRat Z)
    kernelLatticeRat_integral

/-- **The root system of a stratum over `ℚ` is a Mathlib root system.** -/
instance kernelRootSystem_isRootSystem (hB : ∀ x y, B x y = B y x)
    (hD : ∀ v, Z v = 0 → v ≠ 0 → B v v < 0) : (kernelRootSystem hB hD).IsRootSystem :=
  latticeRootSystem_isRootSystem _ _ _ _

/-- It has finitely many roots. -/
theorem finite_kernelRootSystem_roots (hB : ∀ x y, B x y = B y x)
    (hD : ∀ v, Z v = 0 → v ≠ 0 → B v v < 0) :
    Finite (latticeRoots (kernelFormRat B Z) (kernelLatticeRat Z)) :=
  finite_latticeRoots (kernelFormRat_comm hB) (kernelFormRat_neg hD) _ kernelLatticeRat_integral

@[simp]
lemma coe_kernelRootSystem_root (hB : ∀ x y, B x y = B y x)
    (hD : ∀ v, Z v = 0 → v ≠ 0 → B v v < 0)
    (i : latticeRoots (kernelFormRat B Z) (kernelLatticeRat Z)) :
    ((kernelRootSystem hB hD).root i : kernelSpace Z) = i :=
  rfl

omit [Module.Finite ℤ N] in
/-- **The roots over `ℚ` are the kernel roots**: a vector of `V` is a root iff it is `1 ⊗ δ` for a
`(-2)`-vector `δ` of `ker Z ∩ N`. -/
theorem mem_latticeRoots_kernelLatticeRat_iff {v : kernelSpace Z} :
    v ∈ latticeRoots (kernelFormRat B Z) (kernelLatticeRat Z) ↔
      ∃ δ ∈ sphericalRoots (kernelForm B Z), v = (1 : ℚ) ⊗ₜ δ := by
  constructor
  · rintro ⟨⟨δ, rfl⟩, hδ⟩
    refine ⟨δ, ?_, rfl⟩
    have : ((kernelForm B Z δ δ : ℤ) : ℚ) = -2 := by
      simpa using hδ
    change kernelForm B Z δ δ = -2
    exact_mod_cast this
  · rintro ⟨δ, hδ, rfl⟩
    refine ⟨⟨δ, rfl⟩, ?_⟩
    have hδ' : kernelForm B Z δ δ = -2 := hδ
    simp only [kernelFormRat_tmul, mul_one]
    rw [kernelForm_apply] at hδ'
    exact_mod_cast hδ'

/-! ### Bases of an `A₁` stratum -/

omit [Module.Finite ℤ N] in
/-- If the kernel roots are `±δ`, every root of `ker Z ∩ N` is `±δ`. -/
lemma eq_or_eq_neg_of_kernelRoots_eq {δ : N} (hR : kernelRoots B Z = {δ, -δ})
    (i : sphericalRoots (kernelForm B Z)) :
    (i : N) = δ ∨ (i : N) = -δ := by
  have : ((i : kernelLattice Z) : N) ∈ kernelRoots B Z := by
    rw [kernelRoots_eq_image]
    exact ⟨i, i.2, rfl⟩
  rw [hR] at this
  simpa using this

omit [Module.Finite ℤ N] in
lemma mem_kernelRoots_of_eq {δ : N} (hR : kernelRoots B Z = {δ, -δ}) : δ ∈ kernelRoots B Z := by
  rw [hR]
  exact Set.mem_insert _ _

/-- The kernel root `δ` as a root of the lattice `ker Z ∩ N`. -/
def kernelRootOf {δ : N} (hδ : δ ∈ kernelRoots B Z) : sphericalRoots (kernelForm B Z) :=
  ⟨⟨δ, hδ.2⟩, hδ.1⟩

variable [Module.Free ℤ N]

/-- **The base of an `A₁` stratum over `ℤ`.** If the kernel roots are `±δ`, then `{δ}` is a base
of the kernel root pairing. -/
noncomputable def kernelRootPairingBaseOfEq (hB : ∀ x y, B x y = B y x)
    (hD : ∀ v, Z v = 0 → v ≠ 0 → B v v < 0) {δ : N} (hR : kernelRoots B Z = {δ, -δ}) :
    (kernelRootPairing hB hD).Base :=
  (kernelRootPairing hB hD).baseOfEqOrNeg (kernelRootOf (mem_kernelRoots_of_eq hR)) fun i => by
    rcases eq_or_eq_neg_of_kernelRoots_eq hR i with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)

/-- The Cartan matrix of the base of an `A₁` stratum over `ℤ` is `(2)`. -/
theorem cartanMatrix_kernelRootPairingBaseOfEq (hB : ∀ x y, B x y = B y x)
    (hD : ∀ v, Z v = 0 → v ≠ 0 → B v v < 0) {δ : N} (hR : kernelRoots B Z = {δ, -δ})
    (i j : (kernelRootPairingBaseOfEq hB hD hR).support) :
    (kernelRootPairingBaseOfEq hB hD hR).cartanMatrix i j = 2 :=
  cartanMatrix_baseOfEqOrNeg _ _ _ i j

omit [Module.Free ℤ N] in
/-- **The base of an `A₁` stratum over `ℚ`.** If the kernel roots are `±δ`, then `{1 ⊗ δ}` is a
base of the kernel root system over `ℚ`. -/
noncomputable def kernelRootSystemBaseOfEq (hB : ∀ x y, B x y = B y x)
    (hD : ∀ v, Z v = 0 → v ≠ 0 → B v v < 0) {δ : N} (hR : kernelRoots B Z = {δ, -δ}) :
    (kernelRootSystem hB hD).Base :=
  have hδ := mem_kernelRoots_of_eq hR
  have hmem : (1 : ℚ) ⊗ₜ (kernelRootOf hδ : kernelLattice Z) ∈
      latticeRoots (kernelFormRat B Z) (kernelLatticeRat Z) :=
    mem_latticeRoots_kernelLatticeRat_iff.mpr ⟨_, (kernelRootOf hδ).2, rfl⟩
  (kernelRootSystem hB hD).baseOfEqOrNeg ⟨_, hmem⟩ fun i => by
    obtain ⟨x, hx, hi⟩ := mem_latticeRoots_kernelLatticeRat_iff.mp i.2
    rcases eq_or_eq_neg_of_kernelRoots_eq hR ⟨x, hx⟩ with h | h
    · refine Or.inl (Subtype.ext ?_)
      change (i : kernelSpace Z) = (1 : ℚ) ⊗ₜ (kernelRootOf hδ : kernelLattice Z)
      rw [hi]
      congr 1
      exact Subtype.ext h
    · refine Or.inr (Subtype.ext ?_)
      change (i : kernelSpace Z) = -((1 : ℚ) ⊗ₜ (kernelRootOf hδ : kernelLattice Z))
      rw [hi, ← TensorProduct.tmul_neg]
      congr 1
      exact Subtype.ext h

end Kernel

end RootPairing
