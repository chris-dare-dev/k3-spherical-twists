/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.RepresentationTheory.Quiver.Kronecker.IncomingFlag

/-!
# The Mukai budget in the preprojective model of a wall

For representations of the doubled `g`-Kronecker quiver with the preprojective relations, the
heart of the wall between two spherical objects with `dim Ext¹ = g`, `e(X) = dim Ext¹(X, X)` is
defined by the standard complex (`Ext.lean`). Here the inputs of the Mukai budget are theorems on
these real objects:

* `e` is invariant under isomorphism (`DoubledRep.Iso.selfExtDim_eq`);
* Mukai's inequality `e(A) + e(B) ≤ e(N)` for an extension `0 → A → N → B → 0` with
  `Hom(A, B) = 0` (`DoubledRep.selfExtDim_add_le`, from `finrank_Ext1_add_le`; Bayer–Bridgeland,
  arXiv:1310.8266, Lemma 2.5);
* `e` is even, and `e(X) = 2 dim End(X) + v(X)²` with `v(X)² = -2(x₀² + x₁² - g x₀ x₁)`, so
  `e = 2 + v²` when `End(X) = k`: Riemann–Roch for simple objects, and only for them
  (`DoubledRep.selfExtDim_eq`, `DoubledRep.even_selfExtDim`).

From them follows **the Mukai budget lemma in the model**: along a flag of subrepresentations
whose prefixes have no maps to the next subquotient, `∑ e(M_{j+1}/M_j) ≤ e(M)`
(`DoubledRep.sum_selfExtDim_subquotient_le`), and so along the HN filtration of every charge on
either side of the wall (`DoubledRep.sum_selfExtDim_le_of_hnFiltration`).

This is the real-object instance of the budget available in the library. It is not an instance of
`CategoryTheory.Triangulated.MukaiBudget`, which lives on a pretriangulated category: the model is
the heart of the wall, and Mukai's inequality is proved here for extensions of representations,
not for distinguished triangles.

## Main definitions

* `DoubledRep.selfExtDim`: `e(X) = dim Ext¹(X, X)`.

## Main results

* `DoubledRep.Iso.selfExtDim_eq`: isomorphic representations have the same `e`.
* `DoubledRep.selfExtDim_eq`, `DoubledRep.even_selfExtDim`: Riemann–Roch and evenness.
* `DoubledRep.selfExtDim_add_le`: Mukai's inequality.
* `DoubledRep.sum_selfExtDim_subquotient_le`: the budget along a Hom-orthogonal flag.
* `DoubledRep.sum_selfExtDim_le_of_hnFiltration`: the budget along HN filtrations.

## Implementation notes

`selfExtDim` is a definition rather than `finrank k (Ext1 X X)` written out: stated for concrete
subquotients, the `Module` instance on `Ext1` is found by a slow search through quotients of
submodules; through `selfExtDim` it is found once, for abstract vertex spaces.

## Tags

Mukai's lemma, preprojective algebra, Kronecker quiver, Ext, Harder–Narasimhan filtration
-/

namespace Quiver.Kronecker.DoubledRep

open Module

variable {k ι : Type*} [Field k] [Fintype ι]
  {V₀ V₁ : Type*} [AddCommGroup V₀] [Module k V₀] [AddCommGroup V₁] [Module k V₁]

/-- `e(X) = dim Ext¹(X, X)`, the dimension of the self-extensions of a representation. -/
noncomputable def selfExtDim (X : DoubledRep k ι V₀ V₁) : ℕ :=
  finrank k (Ext1 X X)

/-! ### Invariance under isomorphism -/

section IsoInvariance

variable {V₀' V₁' : Type*} [AddCommGroup V₀'] [Module k V₀'] [AddCommGroup V₁'] [Module k V₁']
  {X : DoubledRep k ι V₀ V₁} {X' : DoubledRep k ι V₀' V₁'}

/-- The map `Ext¹(X, X) → Ext¹(X', X')`, `c ↦ u c u⁻¹`, of an isomorphism `u : X ≅ X'`. -/
noncomputable def Iso.extMap (u : Iso X X') : Ext1 X X →ₗ[k] Ext1 X' X' :=
  Submodule.mapQ _ _
    ((map₁ ((u.symm.e₀ : V₀' →ₗ[k] V₀), (u.symm.e₁ : V₁' →ₗ[k] V₁))
      ((u.e₀ : V₀ →ₗ[k] V₀'), (u.e₁ : V₁ →ₗ[k] V₁'))).restrict
        fun _ hc ↦ map₁_mem_cocycles₁ u.symm.mem_Hom u.mem_Hom hc)
    fun _ hc ↦ map₁_mem_coboundaries₁ u.symm.mem_Hom u.mem_Hom hc

omit [Fintype ι] in
private lemma map₁_symm_map₁ (u : Iso X X') (c : (ι → V₀ →ₗ[k] V₁) × (ι → V₁ →ₗ[k] V₀)) :
    map₁ ((u.e₀ : V₀ →ₗ[k] V₀'), (u.e₁ : V₁ →ₗ[k] V₁'))
        ((u.symm.e₀ : V₀' →ₗ[k] V₀), (u.symm.e₁ : V₁' →ₗ[k] V₁))
      (map₁ ((u.symm.e₀ : V₀' →ₗ[k] V₀), (u.symm.e₁ : V₁' →ₗ[k] V₁))
        ((u.e₀ : V₀ →ₗ[k] V₀'), (u.e₁ : V₁ →ₗ[k] V₁')) c) = c := by
  refine Prod.ext (funext fun i ↦ LinearMap.ext fun x ↦ ?_)
    (funext fun i ↦ LinearMap.ext fun x ↦ ?_) <;>
  simp [Iso.symm]

theorem Iso.extMap_symm_extMap (u : Iso X X') (x : Ext1 X X) :
    u.symm.extMap (u.extMap x) = x := by
  induction x using Submodule.Quotient.induction_on with
  | H c => exact congrArg Submodule.Quotient.mk (Subtype.ext (map₁_symm_map₁ u c))

variable [FiniteDimensional k V₀] [FiniteDimensional k V₁] [FiniteDimensional k V₀']
  [FiniteDimensional k V₁']

omit [FiniteDimensional k V₀] [FiniteDimensional k V₁] in
theorem Iso.selfExtDim_le (u : Iso X X') : selfExtDim X ≤ selfExtDim X' :=
  LinearMap.finrank_le_finrank_of_injective (f := u.extMap)
    (Function.LeftInverse.injective u.extMap_symm_extMap)

/-- **`e` is invariant under isomorphism** in the quiver model. -/
theorem Iso.selfExtDim_eq (u : Iso X X') : selfExtDim X = selfExtDim X' :=
  le_antisymm u.selfExtDim_le u.symm.selfExtDim_le

end IsoInvariance

/-! ### Riemann–Roch and evenness -/

section RiemannRoch

variable [FiniteDimensional k V₀] [FiniteDimensional k V₁] {X : DoubledRep k ι V₀ V₁}

/-- **Riemann–Roch in the quiver model**: `e(X) = 2 dim End(X) + v(X)²`, with
`v(X)² = -2(x₀² + x₁² - g x₀ x₁)` the Mukai square of `x₀ v(S₀) + x₁ v(S₁)` for spherical `S₀`,
`S₁` of pairing `g` (`x` the dimension vector). For `dim End(X) = 1` it reads `e = 2 + v²`; it is
not `2 + v²` in general: the zero representation has `e = 0`. -/
theorem selfExtDim_eq (hX : X.IsPreprojective) :
    (selfExtDim X : ℤ) = 2 * finrank k (Hom X X) -
      2 * ((finrank k V₀ : ℤ) ^ 2 + (finrank k V₁ : ℤ) ^ 2 -
        Fintype.card ι * finrank k V₀ * finrank k V₁) := by
  have h := finrank_Ext1 hX hX
  zify at h
  rw [selfExtDim]
  linear_combination h

/-- **`e` is even** in the quiver model. -/
theorem even_selfExtDim (hX : X.IsPreprojective) : Even (selfExtDim X) := by
  rw [← Int.even_natCast, selfExtDim_eq hX]
  exact (even_two_mul _).sub (even_two_mul _)

end RiemannRoch

/-! ### Mukai's inequality and the budget along flags -/

section Budget

/-- **Mukai's inequality** for `e`, `finrank_Ext1_add_le` restated: for an extension
`0 → A → N → B → 0` with `Hom(A, B) = 0`, `e(A) + e(B) ≤ e(N)`. -/
theorem selfExtDim_add_le {W₀ W₁ : Type*} [AddCommGroup W₀] [Module k W₀] [AddCommGroup W₁]
    [Module k W₁] [FiniteDimensional k V₀] [FiniteDimensional k V₁] [FiniteDimensional k W₀]
    [FiniteDimensional k W₁] {A : DoubledRep k ι V₀ V₁} {B : DoubledRep k ι W₀ W₁}
    {ξ : (ι → W₀ →ₗ[k] V₁) × (ι → W₁ →ₗ[k] V₀)} (hA : A.IsPreprojective)
    (hB : B.IsPreprojective) (hξ : ξ ∈ cocycles₁ B A) (hAB : Hom A B = ⊥) :
    selfExtDim A + selfExtDim B ≤ selfExtDim (extension A B ξ) :=
  finrank_Ext1_add_le hA hB hξ hAB

omit [Field k] [Fintype ι] in
/-- The induction of the budget on a sequence: if `a(m) + s(m) ≤ a(m + 1)` for `m < n`, then
`a(0) + ∑_{m<n} s(m) ≤ a(n)`. -/
private theorem add_sum_le_of_step {a s : ℕ → ℕ} {n : ℕ} (h : ∀ m < n, a m + s m ≤ a (m + 1)) :
    a 0 + ∑ j ∈ Finset.range n, s j ≤ a n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← add_assoc]
    exact (Nat.add_le_add_right (ih fun m hm ↦ h m (by lia)) _).trans (h n (by lia))

variable [FiniteDimensional k V₀] [FiniteDimensional k V₁] {M : DoubledRep k ι V₀ V₁}

/-- **One step of the budget**: for subrepresentations `P ≤ Q` with `Hom(M|P, Q/P) = 0`,
`e(M|P) + e(Q/P) ≤ e(M|Q)`, since `M|Q` is an extension of `Q/P` by `M|P`. -/
theorem selfExtDim_restrict_add_le (hM : M.IsPreprojective) {P Q : M.subreps} (hPQ : P ≤ Q)
    (hHom : Hom (M.restrict P) (M.subquotient P Q) = ⊥) :
    selfExtDim (M.restrict P) + selfExtDim (M.subquotient P Q) ≤ selfExtDim (M.restrict Q) := by
  have hex := exists_iso_extension_of_le hM hPQ
  obtain ⟨ξ, hξ, hu⟩ := hex
  obtain ⟨u⟩ := hu
  exact (selfExtDim_add_le (hM.restrict P) ((hM.restrict Q).quotient _) hξ hHom).trans_eq
    u.selfExtDim_eq.symm

/-- **The Mukai budget lemma in the quiver model.** Let `M` satisfy the preprojective relations
and `M_0 ≤ M_1 ≤ ⋯ ≤ M_n = M` be subrepresentations such that no prefix `M_j` maps nonzero to the
next subquotient `M_{j+1}/M_j`. Then `∑_j e(M_{j+1}/M_j) ≤ e(M)`. The proof is the induction of the
tower form, `e(M_0) + ∑_{j<m} e(M_{j+1}/M_j) ≤ e(M_m)`, with Mukai's inequality at each step. -/
theorem sum_selfExtDim_subquotient_le (hM : M.IsPreprojective) {n : ℕ} {c : ℕ → M.subreps}
    (hc : Monotone c) (hcn : c n = ⊤)
    (hHom : ∀ j < n, Hom (M.restrict (c j)) (M.subquotient (c j) (c (j + 1))) = ⊥) :
    ∑ j ∈ Finset.range n, selfExtDim (M.subquotient (c j) (c (j + 1))) ≤ selfExtDim M :=
  (Nat.le_add_left _ _).trans ((add_sum_le_of_step (a := fun j ↦ selfExtDim (M.restrict (c j)))
    fun m hm ↦ selfExtDim_restrict_add_le hM (hc (Nat.le_succ m)) (hHom m hm)).trans_eq
      (restrictTopIso hcn).selfExtDim_eq)

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **The Mukai budget lemma along HN filtrations in the quiver model.** For every charge
`slopeFunction r d` (on either side of the wall), the HN factors of a representation `M` with the
relations have `∑ e(F_{j+1}/F_j) ≤ e(M)`. -/
theorem sum_selfExtDim_le_of_hnFiltration (hM : M.IsPreprojective) {r₀ r₁ : K} (h₀ : 0 < r₀)
    (h₁ : 0 < r₁) (d₀ d₁ : K) (F : (M.slopeFunction h₀ h₁ d₀ d₁).HNFiltration) :
    ∑ j ∈ Finset.range F.n, selfExtDim (M.subquotient (F.c j) (F.c (j + 1))) ≤ selfExtDim M :=
  sum_selfExtDim_subquotient_le hM F.c_mono F.c_n
    fun _ hj ↦ Hom_restrict_subquotient_eq_bot h₀ h₁ d₀ d₁ F hj

end Budget

end Quiver.Kronecker.DoubledRep
