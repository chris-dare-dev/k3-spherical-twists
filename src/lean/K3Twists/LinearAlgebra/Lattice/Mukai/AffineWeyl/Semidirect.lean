/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.Lattice.Mukai.AffineWeyl.LengthZeroGroup

/-!
# The extended affine Weyl group of a fibre as `W ⋉ Λ`

For a connected exceptional fibre `F` (`Mukai.FundamentalCycle`) with curves `Cᵢ` in a lattice `N`,
every element of the extended affine Weyl group `W_aff ⊔ E(N)` (`extendedAffineWeyl`) is
`⊗𝒪(L) ∘ w` with `w ∈ W(R)` (`exists_tensorLine_mul_of_mem_extendedAffineWeyl`), and on the affine
root lattice it acts through `w` and the degree `deg L = (L·Cᵢ)ᵢ` alone
(`fixes_affineRoot_iff`). This file builds the semidirect product `W ⋉ Λ` for the lattice
`Λ = deg(N)` of `AffineWeyl/Index.lean`, the homomorphism from the extended group onto it, and its
action on the affine root lattice: the affine Weyl group as a semidirect product of `W` and a
lattice of translations (Bourbaki, Ch. VI, §2.1; Kac, §6.5), at the level of classes.

* **`W(R)` on coweights.** `W(R)` acts on the root lattice `⊕ ℤCᵢ` in the basis `Cᵢ`
  (`FundamentalCycle.rootRep`) and on coweight coordinates `ℤ^l` by the contragredient action
  `(w • λ)ᵢ = ⟨w⁻¹ Cᵢ, λ⟩` (`FundamentalCycle.coweightRep`). The pairing of `L` with `Σ dⱼ Cⱼ` is
  `Σ dⱼ (L·Cⱼ)` (`degree_dotProduct`), so `deg(wL) = w • deg L` (`degree_finiteWeyl_apply`). So
  `Λ` and `Q^∨ = Aℤ^l` are `W(R)`-stable (`coweightRep_mem_degreeLattice`,
  `coweightRep_mem_corootLattice`), and `W(R)` acts trivially on `Λ/Q^∨`
  (`coweightRep_sub_mem_corootLattice`): `wL - L` lies in `⊕ ℤCᵢ`.
* **The groups.** `W ⋉ Λ` is Mathlib's semidirect product of `Λ`, written multiplicatively, by
  `W(R)` (`FundamentalCycle.DegreeSemidirect`), and `W ⋉ Q^∨` its subgroup of the `(λ, w)` with
  `λ ∈ Q^∨` (`FundamentalCycle.corootSemidirect`). The class `(λ, w) ↦ λ mod Q^∨` is a
  homomorphism to `P^∨/Q^∨` (`degreeSemidirectClass`) with kernel `W ⋉ Q^∨`
  (`ker_degreeSemidirectClass`), so `W ⋉ Q^∨` is normal (`normal_corootSemidirect`) and
  `(W ⋉ Λ)/(W ⋉ Q^∨)` is isomorphic to `Λ/Q^∨`, the image of `Λ` in `P^∨/Q^∨`
  (`degreeSemidirectQuotientEquiv`), of order `[Λ : Q^∨]`, which divides `|det A|`
  (`card_quotient_corootSemidirect`, `card_quotient_corootSemidirect_dvd`).
* **The homomorphism.** `⊗𝒪(L) ∘ w ↦ (deg L, w)` (`FundamentalCycle.toDegreeSemidirect`,
  `toDegreeSemidirect_eq`) is well defined because `W(R) ∩ E(N) = 1`
  (`disjoint_finiteWeyl_lineTwists`): `W(R)` fixes `(1, 0, 0)`, so `L` is the middle coordinate of
  the image of `(1, 0, 0)` (`translationPart_eq`) and `w` is then unique (`finitePart_eq`). Its
  kernel is `E(N ∩ {Cᵢ}^⊥)` (`FundamentalCycle.orthogonalLineTwists`,
  `ker_toDegreeSemidirect`), the elements fixing every affine simple root
  (`mem_ker_toDegreeSemidirect_iff`); it is surjective for an even lattice
  (`toDegreeSemidirect_surjective`) and maps `W_aff` onto `W ⋉ Q^∨`
  (`map_affineWeyl_toDegreeSemidirect`).
* **The action on the affine root lattice.** `W ⋉ Λ` acts on the classes `(0, c, s)` with
  `c ∈ ⊕ ℤCᵢ`, the span of the affine simple roots (`affineEmbed`, `range_affineEmbed`), by
  `(λ, w)·(0, c, s) = (0, wc, s + ⟨wc, λ⟩)` (`FundamentalCycle.degreeSemidirectRep`), matching
  `⊗𝒪(L) αᵢ = αᵢ - (Cᵢ·L)δ`. The action is faithful (`degreeSemidirectRep_injective`), and each
  element of the extended affine Weyl group acts as its image (`apply_affineEmbed`).
* **The class in `P^∨/Q^∨`.** Composing with `(λ, w) ↦ λ mod Q^∨` gives `translationClass`
  (`degreeSemidirectClass_comp_toDegreeSemidirect`). So its kernel is the preimage of
  `W ⋉ Q^∨`, that is `W_aff ⊔ E(N ∩ {Cᵢ}^⊥)` (`ker_translationClass`,
  `mem_ker_translationClass_iff`), and its range is the image of `Λ` for an even lattice
  (`range_translationClass`).

## Main definitions

* `FundamentalCycle.rootRep`, `FundamentalCycle.coweightRep`: `W(R)` on `⊕ ℤCᵢ` and on `ℤ^l`.
* `FundamentalCycle.DegreeSemidirect`: the group `W ⋉ Λ`, with the normal subgroup
  `FundamentalCycle.corootSemidirect`, `W ⋉ Q^∨`.
* `FundamentalCycle.toDegreeSemidirect`: the extended affine Weyl group to `W ⋉ Λ`.
* `FundamentalCycle.orthogonalLineTwists`: the line bundles `E(N ∩ {Cᵢ}^⊥)`.
* `FundamentalCycle.degreeSemidirectRep`: the action of `W ⋉ Λ` on the affine root lattice.

## Main results

* `degree_finiteWeyl_apply`, `coweightRep_sub_mem_corootLattice`: `W(R)` on degrees.
* `ker_degreeSemidirectClass`, `degreeSemidirectQuotientEquiv`,
  `card_quotient_corootSemidirect`: `W ⋉ Q^∨` is normal with quotient `Λ/Q^∨`.
* `ker_toDegreeSemidirect`, `toDegreeSemidirect_surjective`,
  `map_affineWeyl_toDegreeSemidirect`: the homomorphism to `W ⋉ Λ`.
* `apply_affineEmbed`, `degreeSemidirectRep_injective`: the faithful action on the affine root
  lattice through `W ⋉ Λ`.
* `ker_translationClass`, `range_translationClass`: the kernel and range of the class in
  `P^∨/Q^∨`.

## References

* N. Bourbaki, *Groupes et algèbres de Lie*, Ch. VI, §2.1 and §2.3, Proposition 6.
* V. G. Kac, *Infinite dimensional Lie algebras*, §6.5.
-/

open Matrix

namespace Mukai

variable {N : Type*} [AddCommGroup N]

/-- Automorphisms of the Mukai lattice. -/
local notation "Aut(Λ)" => MukaiLattice ℤ N ≃ₗ[ℤ] MukaiLattice ℤ N

/-- The middle coordinate of `g (0, c, 0)`, as a linear map of `c`. For `g ∈ W(R)` it is the
action `c ↦ wc` of `g` on `N`. -/
def middleMap (g : Aut(Λ)) : N →ₗ[ℤ] N where
  toFun c := (g ((0 : ℤ), c, (0 : ℤ))).2.1
  map_add' c c' := by
    rw [show ((0 : ℤ), c + c', (0 : ℤ)) = ((0 : ℤ), c, (0 : ℤ)) + ((0 : ℤ), c', (0 : ℤ)) by simp,
      map_add]
    rfl
  map_smul' a c := by
    rw [show ((0 : ℤ), a • c, (0 : ℤ)) = a • ((0 : ℤ), c, (0 : ℤ)) by simp, map_zsmul]
    rfl

@[simp]
theorem middleMap_apply (g : Aut(Λ)) (c : N) : middleMap g c = (g ((0 : ℤ), c, (0 : ℤ))).2.1 :=
  rfl

/-- `⊗𝒪(L)` is injective, for every value of the parameter `q`. -/
theorem tensorLine_injective (b : N →ₗ[ℤ] N →ₗ[ℤ] ℤ) (L : N) (q : ℤ) :
    Function.Injective (tensorLine b L q) := by
  rintro ⟨r, c, s⟩ ⟨r', c', s'⟩ h
  simp only [tensorLine_apply, Prod.mk.injEq] at h
  obtain ⟨rfl, h2, h3⟩ := h
  obtain rfl : c = c' := add_right_cancel h2
  simp only [Prod.mk.injEq, true_and]
  linarith

namespace FundamentalCycle

variable {b : N →ₗ[ℤ] N →ₗ[ℤ] ℤ} {ι : Type*} [Fintype ι] (F : FundamentalCycle b ι)

/-! ### Coordinates on the root lattice -/

/-- **Coordinates on the root lattice**: a class `c ∈ ⊕ ℤCᵢ` is `Σ dᵢ Cᵢ` for a unique `d`, the
curves being linearly independent (`combination_injective`). -/
noncomputable def rootCoord : F.rootLattice ≃ₗ[ℤ] (ι → ℤ) :=
  (LinearEquiv.ofInjective F.combination F.combination_injective).symm

@[simp]
theorem combination_rootCoord (c : F.rootLattice) : F.combination (F.rootCoord c) = c :=
  LinearEquiv.ofInjective_symm_apply (h := F.combination_injective) F.combination c

/-- `w ∈ W(R)` maps `(0, c, 0)` with `c ∈ ⊕ ℤCᵢ` to `(0, c', 0)` with `c' ∈ ⊕ ℤCᵢ`. -/
theorem middleMap_mem_rootLattice {w : Aut(Λ)} (hw : w ∈ F.finiteWeyl) {c : N}
    (hc : c ∈ F.rootLattice) : middleMap w c ∈ F.rootLattice := by
  simpa using add_mem (F.apply_snd_fst_sub_mem_of_mem_finiteWeyl hw ((0 : ℤ), c, (0 : ℤ))) hc

/-! ### `W(R)` on the root lattice -/

/-- `w ∈ W(R)` on the root lattice, in the basis `Cᵢ`: `w (Σ dⱼ Cⱼ) = Σ (w d)ⱼ Cⱼ`. -/
noncomputable def rootMap (w : F.finiteWeyl) : Module.End ℤ (ι → ℤ) :=
  F.rootCoord.toLinearMap ∘ₗ (middleMap (w : Aut(Λ)) ∘ₗ F.combination).codRestrict F.rootLattice
    fun d => F.middleMap_mem_rootLattice w.2 ⟨d, rfl⟩

theorem combination_rootMap (w : F.finiteWeyl) (d : ι → ℤ) :
    F.combination (F.rootMap w d) = ((w : Aut(Λ)) ((0 : ℤ), F.combination d, (0 : ℤ))).2.1 := by
  simp [rootMap]

/-- **`W(R)` on the root lattice `⊕ ℤCᵢ`**, in the basis `Cᵢ`: `w (Σ dⱼ Cⱼ) = Σ (w d)ⱼ Cⱼ`. -/
noncomputable def rootRep : F.finiteWeyl →* Module.End ℤ (ι → ℤ) where
  toFun := F.rootMap
  map_one' := LinearMap.ext fun d => F.combination_injective <| by
    rw [combination_rootMap]
    rfl
  map_mul' w w' := LinearMap.ext fun d => F.combination_injective <| by
    rw [mul_apply_eq_comp, combination_rootMap, combination_rootMap, combination_rootMap,
      Subgroup.coe_mul, mul_apply_eq_comp, F.finiteWeyl_apply_mk w'.2]

theorem combination_rootRep (w : F.finiteWeyl) (d : ι → ℤ) :
    F.combination (F.rootRep w d) = ((w : Aut(Λ)) ((0 : ℤ), F.combination d, (0 : ℤ))).2.1 :=
  F.combination_rootMap w d

/-- The pairing of `L` with a class `Σ dⱼ Cⱼ` of the root lattice depends only on the degree of
`L`: it is `Σ dⱼ (L·Cⱼ)`. -/
theorem degree_dotProduct (L : N) (d : ι → ℤ) : F.degree L ⬝ᵥ d = b L (F.combination d) := by
  simp [dotProduct, combination_apply, map_sum, mul_comm]

/-! ### The finite part of an element of the extended affine Weyl group -/

/-- Every element of the extended affine Weyl group is `⊗𝒪(L) ∘ w` with `w ∈ W(R)`, `L` its
translation part and `L²/2` the last coordinate of the image of `(1, 0, 0)`. -/
theorem exists_eq_tensorLine_translationPart (hb : ∀ x y, b x y = b y x) {g : Aut(Λ)}
    (hg : g ∈ F.extendedAffineWeyl) :
    2 * (g rankUnit).2.2 = b (translationPart g) (translationPart g) ∧
      ∃ w ∈ F.finiteWeyl, ∀ v, g v = tensorLine b (translationPart g) (g rankUnit).2.2 (w v) := by
  obtain ⟨L, q, hq, w, hw, hgw⟩ := F.exists_tensorLine_mul_of_mem_extendedAffineWeyl hb hg
  have hq' : (g rankUnit).2.2 = q := by
    rw [hgw, F.finiteWeyl_apply_rankUnit hw]
    simp [rankUnit]
  rw [F.translationPart_eq hw hgw, hq']
  exact ⟨hq, w, hw, hgw⟩

/-- **`W(R) ∩ E(N) = 1`**: `W(R)` fixes `(1, 0, 0)`, and `⊗𝒪(L)` sends it to `(1, L, L²/2)`. -/
theorem disjoint_finiteWeyl_lineTwists (hb : ∀ x y, b x y = b y x) :
    Disjoint F.finiteWeyl (lineTwists b) := by
  rw [Subgroup.disjoint_def]
  intro g hW hE
  obtain ⟨L, q, -, hg⟩ := (mem_lineTwists_iff hb).mp hE
  have h1 := F.finiteWeyl_apply_rankUnit hW
  rw [hg] at h1
  obtain rfl : L = 0 := by simpa [rankUnit] using congrArg (fun v => v.2.1) h1
  obtain rfl : q = 0 := by simpa [rankUnit] using congrArg (fun v => v.2.2) h1
  exact LinearEquiv.ext fun v => by rw [hg, tensorLine_zero]; rfl

/-- **The finite part** `w ∈ W(R)` of an element `⊗𝒪(L) ∘ w` of the extended affine Weyl group.
It is unique (`finitePart_eq`): `W(R) ∩ E(N) = 1`, by evaluating at `(1, 0, 0)`. -/
noncomputable def finitePart (hb : ∀ x y, b x y = b y x) (g : F.extendedAffineWeyl) :
    F.finiteWeyl :=
  ⟨(F.exists_eq_tensorLine_translationPart hb g.2).2.choose,
    (F.exists_eq_tensorLine_translationPart hb g.2).2.choose_spec.1⟩

theorem apply_eq_tensorLine_finitePart (hb : ∀ x y, b x y = b y x) (g : F.extendedAffineWeyl)
    (v : MukaiLattice ℤ N) :
    (g : Aut(Λ)) v = tensorLine b (translationPart (g : Aut(Λ))) ((g : Aut(Λ)) rankUnit).2.2
      ((F.finitePart hb g : Aut(Λ)) v) :=
  (F.exists_eq_tensorLine_translationPart hb g.2).2.choose_spec.2 v

/-- **The finite part is unique**: if `g = ⊗𝒪(L) ∘ w` with `w ∈ W(R)`, then `w` is its finite part
(and `L` its translation part, `translationPart_eq`). -/
theorem finitePart_eq (hb : ∀ x y, b x y = b y x) (g : F.extendedAffineWeyl) {w : Aut(Λ)}
    (hw : w ∈ F.finiteWeyl) {L : N} {q : ℤ} (hg : ∀ v, (g : Aut(Λ)) v = tensorLine b L q (w v)) :
    (F.finitePart hb g : Aut(Λ)) = w := by
  have hL : translationPart (g : Aut(Λ)) = L := F.translationPart_eq hw hg
  have hq : ((g : Aut(Λ)) rankUnit).2.2 = q := by
    rw [hg, F.finiteWeyl_apply_rankUnit hw]
    simp [rankUnit]
  refine LinearEquiv.ext fun v => tensorLine_injective b L q ?_
  rw [← hg, F.apply_eq_tensorLine_finitePart hb g v, hL, hq]

/-- `(⊗𝒪(L) ∘ w)(⊗𝒪(L') ∘ w') = ⊗𝒪(L + wL') ∘ ww'`, by `finiteWeyl_conj_tensorLine`. -/
theorem tensorLine_finiteWeyl_tensorLine (hb : ∀ x y, b x y = b y x) {w : Aut(Λ)}
    (hw : w ∈ F.finiteWeyl) (L L' : N) (q q' : ℤ) (u : MukaiLattice ℤ N) :
    tensorLine b L q (w (tensorLine b L' q' u)) =
      tensorLine b (L + (w ((0 : ℤ), L', (0 : ℤ))).2.1)
        (q + q' + b L (w ((0 : ℤ), L', (0 : ℤ))).2.1) (w u) := by
  have hconj := F.finiteWeyl_conj_tensorLine hb hw L' q' (w u)
  rw [LinearEquiv.symm_apply_apply] at hconj
  rw [hconj, ← mul_apply_eq_comp (tensorLine b L q), tensorLine_mul b hb]

/-! ### The line bundles orthogonal to the fibre -/

/-- **The line bundles orthogonal to the fibre**, `E(N ∩ {Cᵢ}^⊥)`: the group generated by the
isometric line bundles `⊗𝒪(L)` with `L·Cᵢ = 0` for every `i` (for symmetric `b`, exactly those,
`mem_orthogonalLineTwists_iff`). -/
def orthogonalLineTwists : Subgroup Aut(Λ) :=
  Subgroup.closure {g | ∃ L : N, ∃ q : ℤ, 2 * q = b L L ∧ (∀ i, b (F.curve i) L = 0) ∧
    ∀ v, g v = tensorLine b L q v}

/-- **`E(N ∩ {Cᵢ}^⊥)` is the set of isometric line bundles orthogonal to the fibre.** -/
theorem mem_orthogonalLineTwists_iff (hb : ∀ x y, b x y = b y x) {g : Aut(Λ)} :
    g ∈ F.orthogonalLineTwists ↔ ∃ (L : N) (q : ℤ), 2 * q = b L L ∧
      (∀ i, b (F.curve i) L = 0) ∧ ∀ v, g v = tensorLine b L q v := by
  refine ⟨fun hg => ?_, fun hg => Subgroup.subset_closure hg⟩
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => exact ⟨0, 0, by simp, fun i => by simp, fun v => by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨L, q, hq, hL, hx⟩ := hx
    obtain ⟨L', q', hq', hL', hy⟩ := hy
    refine ⟨L + L', q + q' + b L L', ?_, fun i => by simp [hL i, hL' i], fun v => ?_⟩
    · simp only [map_add, LinearMap.add_apply, hb L' L]
      linarith
    · rw [mul_apply_eq_comp, hy, hx, ← mul_apply_eq_comp, tensorLine_mul b hb]
  | inv x _ hx =>
    obtain ⟨L, q, hq, hL, hx⟩ := hx
    refine ⟨-L, q, by simpa using hq, fun i => by simp [hL i], fun v => ?_⟩
    obtain ⟨w, rfl⟩ := x.surjective v
    rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply, hx, ← mul_apply_eq_comp,
      tensorLine_mul b hb, neg_add_cancel, map_neg, LinearMap.neg_apply,
      show q + q + -b L L = 0 by omega, tensorLine_zero]
    rfl

theorem orthogonalLineTwists_le_extendedAffineWeyl :
    F.orthogonalLineTwists ≤ F.extendedAffineWeyl := by
  rw [orthogonalLineTwists, Subgroup.closure_le]
  rintro g ⟨L, q, hq, -, hg⟩
  exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨L, q, hq, hg⟩)

/-! ### The affine root lattice -/

/-- **The affine root lattice in coordinates**: `(d, s) ↦ (0, Σ dᵢ Cᵢ, s)`, injective
(`affineEmbed_injective`) onto the span of the affine simple roots (`range_affineEmbed`). -/
def affineEmbed : ((ι → ℤ) × ℤ) →ₗ[ℤ] MukaiLattice ℤ N :=
  LinearMap.inr ℤ ℤ (N × ℤ) ∘ₗ F.combination.prodMap LinearMap.id

@[simp]
theorem affineEmbed_apply (y : (ι → ℤ) × ℤ) :
    F.affineEmbed y = ((0 : ℤ), F.combination y.1, y.2) :=
  rfl

theorem affineEmbed_injective : Function.Injective F.affineEmbed := by
  rintro ⟨d, s⟩ ⟨d', s'⟩ h
  simp only [affineEmbed_apply, Prod.mk.injEq, true_and] at h
  rw [F.combination_injective h.1, h.2]

/-- **The image of `affineEmbed` is the span of the affine simple roots**: `(0, Σ dᵢ Cᵢ, s)` has
coordinates `(s, s zᵢ - dᵢ)` in the affine simple roots (`sum_affineCoord_smul_affineRoot`). -/
theorem range_affineEmbed :
    LinearMap.range F.affineEmbed = Submodule.span ℤ (Set.range F.affineRoot) := by
  classical
  refine le_antisymm ?_ ?_
  · rintro _ ⟨⟨d, s⟩, rfl⟩
    rw [affineEmbed_apply, combination_apply, ← F.sum_affineCoord_smul_affineRoot s d]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    cases k with
    | none => exact ⟨(F.mult, 1), rfl⟩
    | some i => exact ⟨(-Pi.single i 1, 0), by simp [F.combination_neg_single]⟩

/-- The action of `(λ, w)` on the affine root lattice in coordinates:
`(d, s) ↦ (w d, s + ⟨w d, λ⟩)`. -/
noncomputable def affineAct (x : ι → ℤ) (w : F.finiteWeyl) : Module.End ℤ ((ι → ℤ) × ℤ) where
  toFun y := (F.rootRep w y.1, y.2 + F.rootRep w y.1 ⬝ᵥ x)
  map_add' y y' := by
    ext
    · simp
    · simp only [Prod.snd_add, Prod.fst_add, map_add, add_dotProduct]
      ring
  map_smul' a y := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_zsmul, smul_dotProduct, smul_eq_mul,
      RingHom.id_apply, Prod.smul_mk, mul_add]

@[simp]
theorem affineAct_apply (x : ι → ℤ) (w : F.finiteWeyl) (y : (ι → ℤ) × ℤ) :
    F.affineAct x w y = (F.rootRep w y.1, y.2 + F.rootRep w y.1 ⬝ᵥ x) :=
  rfl

/-- `w ∈ W(R)` maps `(0, c, s)` to `(0, wc, s)`. -/
theorem finiteWeyl_apply_rankZero (hb : ∀ x y, b x y = b y x) {w : Aut(Λ)}
    (hw : w ∈ F.finiteWeyl) (c : N) (s : ℤ) :
    w ((0 : ℤ), c, s) = (0, (w ((0 : ℤ), c, (0 : ℤ))).2.1, s) := by
  have hδ : w corankUnit = corankUnit :=
    (F.affineWeyl_le_rootPreserving hb (F.finiteWeyl_le_affineWeyl hw)).2
  rw [show ((0 : ℤ), c, s) = ((0 : ℤ), c, (0 : ℤ)) + s • (corankUnit : MukaiLattice ℤ N) by
    ext <;> simp [corankUnit], map_add, map_zsmul, hδ, F.finiteWeyl_apply_mk hw]
  ext <;> simp [corankUnit]

variable [DecidableEq ι]

/-! ### `W(R)` on coweights -/

/-- **`W(R)` on coweight coordinates**: `(w • λ)ᵢ = ⟨w⁻¹ Cᵢ, λ⟩` with `⟨Σ dⱼ Cⱼ, λ⟩ = Σ dⱼ λⱼ`,
the contragredient of the action on the root lattice (`coweightRep_dotProduct`). -/
noncomputable def coweightRep : F.finiteWeyl →* Module.End ℤ (ι → ℤ) where
  toFun w := (LinearMap.toMatrix' (F.rootRep w⁻¹)).vecMulLinear
  map_one' := LinearMap.ext fun x => by simp
  map_mul' w w' := LinearMap.ext fun x => by simp [LinearMap.toMatrix'_mul]

theorem coweightRep_apply (w : F.finiteWeyl) (x : ι → ℤ) :
    F.coweightRep w x = x ᵥ* LinearMap.toMatrix' (F.rootRep w⁻¹) :=
  rfl

/-- `⟨c, w • λ⟩ = ⟨w⁻¹ c, λ⟩`. -/
theorem coweightRep_dotProduct (w : F.finiteWeyl) (x d : ι → ℤ) :
    F.coweightRep w x ⬝ᵥ d = x ⬝ᵥ F.rootRep w⁻¹ d := by
  rw [coweightRep_apply, ← dotProduct_mulVec, LinearMap.toMatrix'_mulVec]

/-- `⟨wc, w • λ⟩ = ⟨c, λ⟩`. -/
theorem rootRep_dotProduct_coweightRep (w : F.finiteWeyl) (d x : ι → ℤ) :
    F.rootRep w d ⬝ᵥ F.coweightRep w x = d ⬝ᵥ x := by
  rw [dotProduct_comm, coweightRep_dotProduct, ← mul_apply_eq_comp, ← map_mul, inv_mul_cancel,
    map_one, one_apply_eq_self, dotProduct_comm]

/-- **`W(R)` acts on degrees**: `deg(wL) = w • deg L`. -/
theorem degree_finiteWeyl_apply (hb : ∀ x y, b x y = b y x) (w : F.finiteWeyl) (L : N) :
    F.degree ((w : Aut(Λ)) ((0 : ℤ), L, (0 : ℤ))).2.1 = F.coweightRep w (F.degree L) := by
  ext i
  have hi : F.coweightRep w (F.degree L) i = F.coweightRep w (F.degree L) ⬝ᵥ Pi.single i 1 := by
    simp
  have hC : F.combination (Pi.single i 1) = F.curve i := by
    simp [combination]
  rw [hi, coweightRep_dotProduct, degree_dotProduct, combination_rootRep, hC, degree_apply]
  have hwO : (w : Aut(Λ)) ∈ orthogonalGroup b :=
    F.affineWeyl_le_orthogonalGroup hb (F.finiteWeyl_le_affineWeyl w.2)
  have key := hwO ((0 : ℤ), L, (0 : ℤ))
    (((w⁻¹ : F.finiteWeyl) : Aut(Λ)) ((0 : ℤ), F.curve i, (0 : ℤ)))
  rw [Subgroup.coe_inv, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply,
    F.finiteWeyl_apply_mk w.2, ← LinearEquiv.coe_inv, ← Subgroup.coe_inv,
    F.finiteWeyl_apply_mk (w⁻¹).2] at key
  simpa using key

theorem coweightRep_inv_apply (w : F.finiteWeyl) (x : ι → ℤ) :
    F.coweightRep w⁻¹ (F.coweightRep w x) = x := by
  change (F.coweightRep w⁻¹ * F.coweightRep w) x = x
  rw [← map_mul, inv_mul_cancel, map_one]
  rfl

theorem coweightRep_apply_inv (w : F.finiteWeyl) (x : ι → ℤ) :
    F.coweightRep w (F.coweightRep w⁻¹ x) = x := by
  simpa using F.coweightRep_inv_apply w⁻¹ x

/-- **`Λ` is `W(R)`-stable.** -/
theorem coweightRep_mem_degreeLattice (hb : ∀ x y, b x y = b y x) (w : F.finiteWeyl)
    {x : ι → ℤ} (hx : x ∈ F.degreeLattice) : F.coweightRep w x ∈ F.degreeLattice := by
  obtain ⟨L, rfl⟩ := hx
  rw [← F.degree_finiteWeyl_apply hb]
  exact LinearMap.mem_range_self _ _

/-- **`W(R)` acts trivially on `Λ/Q^∨`**: `w • λ - λ ∈ Q^∨` for `λ ∈ Λ`, since `wL - L` lies in
`⊕ ℤCᵢ`. -/
theorem coweightRep_sub_mem_corootLattice (hb : ∀ x y, b x y = b y x) (w : F.finiteWeyl)
    {x : ι → ℤ} (hx : x ∈ F.degreeLattice) : F.coweightRep w x - x ∈ F.corootLattice := by
  obtain ⟨L, rfl⟩ := hx
  rw [← F.degree_finiteWeyl_apply hb, ← map_sub]
  exact F.degree_mem_corootLattice hb
    (by simpa using F.apply_snd_fst_sub_mem_of_mem_finiteWeyl w.2 ((0 : ℤ), L, (0 : ℤ)))

/-- **`Q^∨` is `W(R)`-stable.** -/
theorem coweightRep_mem_corootLattice (hb : ∀ x y, b x y = b y x) (w : F.finiteWeyl)
    {x : ι → ℤ} (hx : x ∈ F.corootLattice) : F.coweightRep w x ∈ F.corootLattice := by
  simpa using add_mem
    (F.coweightRep_sub_mem_corootLattice hb w (F.corootLattice_le_degreeLattice hb hx)) hx

/-- **`W(R)` acts on `Λ`** through `coweightRep` (`coweightRep_mem_degreeLattice`), written
multiplicatively. -/
noncomputable def degreeAction (hb : ∀ x y, b x y = b y x) :
    F.finiteWeyl →* MulAut (Multiplicative F.degreeLattice) where
  toFun w :=
    { toFun := fun x => .ofAdd ⟨F.coweightRep w (Multiplicative.toAdd x : F.degreeLattice),
        F.coweightRep_mem_degreeLattice hb w (Multiplicative.toAdd x).2⟩
      invFun := fun x => .ofAdd ⟨F.coweightRep w⁻¹ (Multiplicative.toAdd x : F.degreeLattice),
        F.coweightRep_mem_degreeLattice hb w⁻¹ (Multiplicative.toAdd x).2⟩
      left_inv := fun x =>
        Multiplicative.toAdd.injective (Subtype.ext (by simp [coweightRep_inv_apply]))
      right_inv := fun x =>
        Multiplicative.toAdd.injective (Subtype.ext (by simp [coweightRep_apply_inv]))
      map_mul' := fun x y => Multiplicative.toAdd.injective (Subtype.ext (by simp)) }
  map_one' := MulEquiv.ext fun x => Multiplicative.toAdd.injective (Subtype.ext (by simp))
  map_mul' w w' := MulEquiv.ext fun x => Multiplicative.toAdd.injective (Subtype.ext (by simp))

@[simp]
theorem coe_toAdd_degreeAction (hb : ∀ x y, b x y = b y x) (w : F.finiteWeyl)
    (x : Multiplicative F.degreeLattice) :
    ((Multiplicative.toAdd (F.degreeAction hb w x) : F.degreeLattice) : ι → ℤ) =
      F.coweightRep w (Multiplicative.toAdd x : F.degreeLattice) :=
  rfl

/-! ### The group `W ⋉ Λ` and its normal subgroup `W ⋉ Q^∨` -/

/-- **The group `W ⋉ Λ`**: the semidirect product of the degree lattice `Λ = deg(N)`, written
multiplicatively, by the finite Weyl group `W(R)` acting on coweight coordinates
(`degreeAction`): `(λ, w)(λ', w') = (λ + wλ', ww')`. -/
abbrev DegreeSemidirect (hb : ∀ x y, b x y = b y x) : Type _ :=
  Multiplicative F.degreeLattice ⋊[F.degreeAction hb] F.finiteWeyl

/-- **The subgroup `W ⋉ Q^∨`** of `W ⋉ Λ`: the elements `(λ, w)` with `λ` in the coroot lattice
`Q^∨ = Aℤ^l`. -/
def corootSemidirect (hb : ∀ x y, b x y = b y x) : Subgroup (F.DegreeSemidirect hb) where
  carrier := {x | ((Multiplicative.toAdd x.left : F.degreeLattice) : ι → ℤ) ∈ F.corootLattice}
  one_mem' := by simp
  mul_mem' {x y} hx hy := by
    change ((Multiplicative.toAdd (x * y).left : F.degreeLattice) : ι → ℤ) ∈ F.corootLattice
    simp only [SemidirectProduct.mul_left, toAdd_mul, Submodule.coe_add, coe_toAdd_degreeAction]
    exact add_mem hx (F.coweightRep_mem_corootLattice hb _ hy)
  inv_mem' {x} hx := by
    change ((Multiplicative.toAdd x⁻¹.left : F.degreeLattice) : ι → ℤ) ∈ F.corootLattice
    simp only [SemidirectProduct.inv_left, coe_toAdd_degreeAction, toAdd_inv, Submodule.coe_neg,
      map_neg]
    exact neg_mem (F.coweightRep_mem_corootLattice hb _ hx)

theorem mem_corootSemidirect (hb : ∀ x y, b x y = b y x) {x : F.DegreeSemidirect hb} :
    x ∈ F.corootSemidirect hb ↔
      ((Multiplicative.toAdd x.left : F.degreeLattice) : ι → ℤ) ∈ F.corootLattice :=
  Iff.rfl

/-- **The class of `(λ, w)` in `P^∨/Q^∨`**: `λ` modulo the coroot lattice. It is a homomorphism
because `W(R)` acts trivially on `Λ/Q^∨` (`coweightRep_sub_mem_corootLattice`). -/
noncomputable def degreeSemidirectClass (hb : ∀ x y, b x y = b y x) :
    F.DegreeSemidirect hb →* Multiplicative ((ι → ℤ) ⧸ F.corootLattice) where
  toFun x :=
    .ofAdd (Submodule.Quotient.mk ((Multiplicative.toAdd x.left : F.degreeLattice) : ι → ℤ))
  map_one' := by simp
  map_mul' x y := by
    rw [← ofAdd_add, ← Submodule.Quotient.mk_add, EmbeddingLike.apply_eq_iff_eq,
      Submodule.Quotient.eq]
    simp only [SemidirectProduct.mul_left, toAdd_mul, Submodule.coe_add, coe_toAdd_degreeAction]
    convert F.coweightRep_sub_mem_corootLattice hb x.right (Multiplicative.toAdd y.left).2
      using 1
    abel

theorem degreeSemidirectClass_apply (hb : ∀ x y, b x y = b y x) (x : F.DegreeSemidirect hb) :
    F.degreeSemidirectClass hb x =
      .ofAdd (Submodule.Quotient.mk ((Multiplicative.toAdd x.left : F.degreeLattice) : ι → ℤ)) :=
  rfl

/-- **`W ⋉ Q^∨` is the kernel of the class in `P^∨/Q^∨`.** -/
theorem ker_degreeSemidirectClass (hb : ∀ x y, b x y = b y x) :
    (F.degreeSemidirectClass hb).ker = F.corootSemidirect hb := by
  ext x
  rw [MonoidHom.mem_ker, degreeSemidirectClass_apply, ofAdd_eq_one, Submodule.Quotient.mk_eq_zero]
  rfl

/-- **`W ⋉ Q^∨` is normal in `W ⋉ Λ`.** -/
instance normal_corootSemidirect (hb : ∀ x y, b x y = b y x) :
    (F.corootSemidirect hb).Normal := by
  rw [← F.ker_degreeSemidirectClass hb]
  exact MonoidHom.normal_ker _

/-- The range of the class is the image of `Λ` in `P^∨/Q^∨`. -/
theorem range_degreeSemidirectClass (hb : ∀ x y, b x y = b y x) :
    (F.degreeSemidirectClass hb).range = F.degreeClassGroup := by
  ext x
  rw [MonoidHom.mem_range, mem_degreeClassGroup]
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨L, hL⟩ := (Multiplicative.toAdd y.left).2
    exact ⟨L, by rw [degreeSemidirectClass_apply, hL]⟩
  · rintro ⟨L, rfl⟩
    exact ⟨⟨.ofAdd ⟨F.degree L, L, rfl⟩, 1⟩, rfl⟩

/-- **`(W ⋉ Λ)/(W ⋉ Q^∨) ≃* Λ/Q^∨`**, realized as the image of `Λ` in `P^∨/Q^∨`
(`degreeClassGroup`). -/
noncomputable def degreeSemidirectQuotientEquiv (hb : ∀ x y, b x y = b y x) :
    F.DegreeSemidirect hb ⧸ F.corootSemidirect hb ≃* F.degreeClassGroup :=
  (QuotientGroup.quotientMulEquivOfEq (F.ker_degreeSemidirectClass hb).symm).trans
    ((QuotientGroup.quotientKerEquivRange _).trans
      (MulEquiv.subgroupCongr (F.range_degreeSemidirectClass hb)))

/-- **The quotient `(W ⋉ Λ)/(W ⋉ Q^∨)` has order `[Λ : Q^∨]`.** -/
theorem card_quotient_corootSemidirect (hb : ∀ x y, b x y = b y x) :
    Nat.card (F.DegreeSemidirect hb ⧸ F.corootSemidirect hb) =
      F.corootLattice.toAddSubgroup.relIndex F.degreeLattice.toAddSubgroup := by
  rw [Nat.card_congr (F.degreeSemidirectQuotientEquiv hb).toEquiv, card_degreeClassGroup]

/-- The order of `(W ⋉ Λ)/(W ⋉ Q^∨)` divides `|det A|`. -/
theorem card_quotient_corootSemidirect_dvd (hb : ∀ x y, b x y = b y x) :
    Nat.card (F.DegreeSemidirect hb ⧸ F.corootSemidirect hb) ∣ F.cartan.det.natAbs := by
  rw [F.card_quotient_corootSemidirect hb]
  exact F.relIndex_corootLattice_dvd hb

/-- When every degree is realized, `Λ = ℤ^l`, the quotient `(W ⋉ Λ)/(W ⋉ Q^∨)` has order
`|det A|`. -/
theorem card_quotient_corootSemidirect_of_degreeLattice (hb : ∀ x y, b x y = b y x)
    (hΛ : F.degreeLattice = ⊤) :
    Nat.card (F.DegreeSemidirect hb ⧸ F.corootSemidirect hb) = F.cartan.det.natAbs := by
  rw [F.card_quotient_corootSemidirect hb, hΛ, Submodule.top_toAddSubgroup,
    AddSubgroup.relIndex_top_right, index_corootLattice]

/-! ### The homomorphism from the extended affine Weyl group -/

/-- **The extended affine Weyl group maps to `W ⋉ Λ`**: `⊗𝒪(L) ∘ w ↦ (deg L, w)`
(`toDegreeSemidirect_eq`), a homomorphism because `⊗𝒪(L) w ⊗𝒪(L') w' = ⊗𝒪(L + wL') ww'` and
`deg(wL') = w • deg L'`. -/
noncomputable def toDegreeSemidirect (hb : ∀ x y, b x y = b y x) :
    F.extendedAffineWeyl →* F.DegreeSemidirect hb where
  toFun g := ⟨.ofAdd ⟨F.degree (translationPart (g : Aut(Λ))), LinearMap.mem_range_self _ _⟩,
    F.finitePart hb g⟩
  map_one' := by
    refine SemidirectProduct.ext (Multiplicative.toAdd.injective (Subtype.ext ?_))
      (Subtype.ext ?_)
    · simp [translationPart, rankUnit]
    · exact F.finitePart_eq hb 1 (one_mem _) (L := 0) (q := 0) fun v => by simp
  map_mul' g h := by
    obtain ⟨q, hgh⟩ : ∃ q : ℤ, ∀ v, ((g * h : F.extendedAffineWeyl) : Aut(Λ)) v =
        tensorLine b (translationPart (g : Aut(Λ)) +
          ((F.finitePart hb g : Aut(Λ)) ((0 : ℤ), translationPart (h : Aut(Λ)), (0 : ℤ))).2.1) q
          (((F.finitePart hb g * F.finitePart hb h : F.finiteWeyl) : Aut(Λ)) v) :=
      ⟨_, fun v => by
        rw [Subgroup.coe_mul, mul_apply_eq_comp, F.apply_eq_tensorLine_finitePart hb h,
          F.apply_eq_tensorLine_finitePart hb g, F.tensorLine_finiteWeyl_tensorLine hb
          (F.finitePart hb g).2]
        rfl⟩
    have hmem := (F.finitePart hb g * F.finitePart hb h).2
    refine SemidirectProduct.ext (Multiplicative.toAdd.injective (Subtype.ext ?_))
      (Subtype.ext (F.finitePart_eq hb (g * h) hmem hgh))
    simp only [SemidirectProduct.mul_left, toAdd_mul, toAdd_ofAdd, Submodule.coe_add,
      coe_toAdd_degreeAction]
    rw [F.translationPart_eq hmem hgh, map_add, F.degree_finiteWeyl_apply hb]

@[simp]
theorem toDegreeSemidirect_apply_right (hb : ∀ x y, b x y = b y x) (g : F.extendedAffineWeyl) :
    (F.toDegreeSemidirect hb g).right = F.finitePart hb g :=
  rfl

@[simp]
theorem coe_toAdd_toDegreeSemidirect_apply_left (hb : ∀ x y, b x y = b y x)
    (g : F.extendedAffineWeyl) :
    ((Multiplicative.toAdd (F.toDegreeSemidirect hb g).left : F.degreeLattice) : ι → ℤ) =
      F.degree (translationPart (g : Aut(Λ))) :=
  rfl

/-- **`⊗𝒪(L) ∘ w ↦ (deg L, w)`.** -/
theorem toDegreeSemidirect_eq (hb : ∀ x y, b x y = b y x) (g : F.extendedAffineWeyl)
    {w : Aut(Λ)} (hw : w ∈ F.finiteWeyl) {L : N} {q : ℤ}
    (hg : ∀ v, (g : Aut(Λ)) v = tensorLine b L q (w v)) :
    F.toDegreeSemidirect hb g = ⟨.ofAdd ⟨F.degree L, L, rfl⟩, ⟨w, hw⟩⟩ := by
  refine SemidirectProduct.ext (Multiplicative.toAdd.injective (Subtype.ext ?_))
    (Subtype.ext (F.finitePart_eq hb g hw hg))
  simp [F.translationPart_eq hw hg]

/-- Composing with the class in `P^∨/Q^∨` gives `translationClass`. -/
theorem degreeSemidirectClass_comp_toDegreeSemidirect (hb : ∀ x y, b x y = b y x) :
    (F.degreeSemidirectClass hb).comp (F.toDegreeSemidirect hb) = F.translationClass hb :=
  MonoidHom.ext fun _ => rfl

/-- **The kernel of `toDegreeSemidirect` is `E(N ∩ {Cᵢ}^⊥)`**: `(deg L, w) = 1` iff `w = 1` and
`L ⊥ Cᵢ` for every `i`. -/
theorem ker_toDegreeSemidirect (hb : ∀ x y, b x y = b y x) :
    (F.toDegreeSemidirect hb).ker = F.orthogonalLineTwists.subgroupOf F.extendedAffineWeyl := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, F.mem_orthogonalLineTwists_iff hb]
  constructor
  · intro h
    have hl : F.degree (translationPart (g : Aut(Λ))) = 0 := by
      simpa using congrArg
        (fun x : F.DegreeSemidirect hb => ((Multiplicative.toAdd x.left : F.degreeLattice) : ι → ℤ))
        h
    have hr : (F.finitePart hb g : Aut(Λ)) = 1 := by
      simpa using congrArg (fun x : F.DegreeSemidirect hb => (x.right : Aut(Λ))) h
    refine ⟨_, _, (F.exists_eq_tensorLine_translationPart hb g.2).1, fun i => ?_, fun v => ?_⟩
    · rw [hb]
      simpa using congrFun hl i
    · rw [F.apply_eq_tensorLine_finitePart hb g v, hr]
      rfl
  · rintro ⟨L, q, -, hL, hg⟩
    have hg' : ∀ v, (g : Aut(Λ)) v = tensorLine b L q ((1 : Aut(Λ)) v) := hg
    rw [F.toDegreeSemidirect_eq hb g (one_mem _) hg']
    refine SemidirectProduct.ext (Multiplicative.toAdd.injective (Subtype.ext ?_)) rfl
    ext i
    simp [hb L (F.curve i), hL i]

/-- An element lies in the kernel of `toDegreeSemidirect` iff it fixes every affine simple root
(`fixes_affineRoot_iff`). -/
theorem mem_ker_toDegreeSemidirect_iff (hb : ∀ x y, b x y = b y x) (g : F.extendedAffineWeyl) :
    g ∈ (F.toDegreeSemidirect hb).ker ↔ ∀ k, (g : Aut(Λ)) (F.affineRoot k) = F.affineRoot k := by
  rw [F.ker_toDegreeSemidirect hb, Subgroup.mem_subgroupOf, F.mem_orthogonalLineTwists_iff hb,
    F.fixes_affineRoot_iff hb g.2]

/-- **`toDegreeSemidirect` is surjective for an even lattice**: every class `L` gives an
isometric line bundle `⊗𝒪(L)`, and `⊗𝒪(L) ∘ w ↦ (deg L, w)`. -/
theorem toDegreeSemidirect_surjective (hb : ∀ x y, b x y = b y x)
    (heven : ∀ L : N, Even (b L L)) : Function.Surjective (F.toDegreeSemidirect hb) := by
  rintro ⟨x, w⟩
  obtain ⟨L, hL⟩ := (Multiplicative.toAdd x).2
  obtain ⟨q, hq⟩ : ∃ q, 2 * q = b L L := by
    obtain ⟨m, hm⟩ := heven L
    exact ⟨m, by omega⟩
  have hgE : tensorLineEquiv hb L hq * (w : Aut(Λ)) ∈ F.extendedAffineWeyl :=
    mul_mem (Subgroup.mem_sup_right (Subgroup.subset_closure ⟨L, q, hq, fun v => rfl⟩))
      (Subgroup.mem_sup_left (F.finiteWeyl_le_affineWeyl w.2))
  refine ⟨⟨_, hgE⟩, ?_⟩
  rw [F.toDegreeSemidirect_eq hb ⟨_, hgE⟩ w.2 (L := L) (q := q) fun v => rfl]
  refine SemidirectProduct.ext (Multiplicative.toAdd.injective (Subtype.ext ?_)) rfl
  exact hL

/-- **`W_aff` maps onto `W ⋉ Q^∨`**: an element of `W_aff` has translation part in `⊕ ℤCᵢ`, of
degree in `Q^∨`; conversely `(deg D, w)` with `D ∈ ⊕ ℤCᵢ` is the image of `⊗𝒪(D) ∘ w ∈ W_aff`. -/
theorem map_affineWeyl_toDegreeSemidirect (hb : ∀ x y, b x y = b y x) :
    (F.affineWeyl.subgroupOf F.extendedAffineWeyl).map (F.toDegreeSemidirect hb) =
      F.corootSemidirect hb := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨g, hg, rfl⟩
    exact F.degree_mem_corootLattice hb (F.translationPart_mem_of_mem_affineWeyl hb hg)
  · rintro ⟨x, w⟩ hx
    obtain ⟨d, hd⟩ := (F.mem_corootSemidirect hb).mp hx
    have hDQ : F.combination (-d) ∈ F.rootLattice := ⟨-d, rfl⟩
    have hdeg : F.degree (F.combination (-d)) =
        ((Multiplicative.toAdd x : F.degreeLattice) : ι → ℤ) := by
      rw [← hd, Matrix.toLin'_apply, combination_apply, F.degree_combination hb,
        Matrix.mulVec_neg, neg_neg]
    have htW : tensorLineEquiv hb _ (F.two_mul_self_div_two hb hDQ) * (w : Aut(Λ)) ∈
        F.affineWeyl :=
      mul_mem (F.translations_le_affineWeyl hb (Subgroup.subset_closure ⟨_, hDQ, fun v => rfl⟩))
        (F.finiteWeyl_le_affineWeyl w.2)
    refine ⟨⟨_, Subgroup.mem_sup_left htW⟩, htW, ?_⟩
    rw [F.toDegreeSemidirect_eq hb ⟨_, Subgroup.mem_sup_left htW⟩ w.2 fun v => rfl]
    exact SemidirectProduct.ext (Multiplicative.toAdd.injective (Subtype.ext hdeg)) rfl

/-- **The kernel of `translationClass` is `W_aff ⊔ E(N ∩ {Cᵢ}^⊥)`**: it is the preimage of
`W ⋉ Q^∨`, the image of `W_aff`, so it is `W_aff` times the kernel `E(N ∩ {Cᵢ}^⊥)` of
`toDegreeSemidirect`. -/
theorem ker_translationClass (hb : ∀ x y, b x y = b y x) :
    (F.translationClass hb).ker = F.affineWeyl.subgroupOf F.extendedAffineWeyl ⊔
      F.orthogonalLineTwists.subgroupOf F.extendedAffineWeyl := by
  rw [← F.degreeSemidirectClass_comp_toDegreeSemidirect hb, ← MonoidHom.comap_ker,
    F.ker_degreeSemidirectClass hb, ← F.map_affineWeyl_toDegreeSemidirect hb,
    Subgroup.comap_map_eq, F.ker_toDegreeSemidirect hb]

/-- **An element of the extended affine Weyl group has trivial class in `P^∨/Q^∨` iff it is
`⊗𝒪(L₀) ∘ u` with `L₀ ⊥ Cᵢ` and `u ∈ W_aff`.** -/
theorem mem_ker_translationClass_iff (hb : ∀ x y, b x y = b y x) (g : F.extendedAffineWeyl) :
    g ∈ (F.translationClass hb).ker ↔
      ∃ t ∈ F.orthogonalLineTwists, ∃ u ∈ F.affineWeyl, t * u = (g : Aut(Λ)) := by
  have := F.affineWeyl_normal hb
  rw [F.ker_translationClass hb, sup_comm, ← SetLike.mem_coe, Subgroup.mul_normal, Set.mem_mul]
  constructor
  · rintro ⟨t, ht, u, hu, rfl⟩
    exact ⟨t, ht, u, hu, rfl⟩
  · rintro ⟨t, ht, u, hu, h⟩
    exact ⟨⟨t, F.orthogonalLineTwists_le_extendedAffineWeyl ht⟩, ht,
      ⟨u, Subgroup.mem_sup_left hu⟩, hu, Subtype.ext h⟩

/-- **The range of `translationClass` is the image of `Λ` in `P^∨/Q^∨`**, for an even
lattice. -/
theorem range_translationClass (hb : ∀ x y, b x y = b y x) (heven : ∀ L : N, Even (b L L)) :
    (F.translationClass hb).range = F.degreeClassGroup := by
  rw [← F.degreeSemidirectClass_comp_toDegreeSemidirect hb, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (F.toDegreeSemidirect_surjective hb heven),
    ← MonoidHom.range_eq_map, F.range_degreeSemidirectClass hb]

/-! ### The action of `W ⋉ Λ` on the affine root lattice -/

/-- **`W ⋉ Λ` acts on the affine root lattice**: `(λ, w)·(0, c, s) = (0, wc, s + ⟨wc, λ⟩)`, in the
coordinates `(0, Σ dᵢ Cᵢ, s) ↔ (d, s)` of `affineEmbed`. The sign matches
`⊗𝒪(L) αᵢ = αᵢ - (Cᵢ·L)δ` (`tensorLine_affineRoot_some`). -/
noncomputable def degreeSemidirectRep (hb : ∀ x y, b x y = b y x) :
    F.DegreeSemidirect hb →* Module.End ℤ ((ι → ℤ) × ℤ) where
  toFun z := F.affineAct ((Multiplicative.toAdd z.left : F.degreeLattice) : ι → ℤ) z.right
  map_one' := LinearMap.ext fun y => by simp
  map_mul' z z' := LinearMap.ext fun y => by
    simp only [affineAct_apply, SemidirectProduct.mul_left, SemidirectProduct.mul_right, toAdd_mul,
      Submodule.coe_add, coe_toAdd_degreeAction, map_mul, mul_apply_eq_comp, dotProduct_add,
      rootRep_dotProduct_coweightRep]
    ext
    · rfl
    · simp only
      ring

@[simp]
theorem degreeSemidirectRep_apply (hb : ∀ x y, b x y = b y x) (z : F.DegreeSemidirect hb)
    (y : (ι → ℤ) × ℤ) :
    F.degreeSemidirectRep hb z y = (F.rootRep z.right y.1,
      y.2 + F.rootRep z.right y.1 ⬝ᵥ ((Multiplicative.toAdd z.left : F.degreeLattice) : ι → ℤ)) :=
  rfl

/-- **Each element of the extended affine Weyl group acts on the affine root lattice as its image
in `W ⋉ Λ`**: `⊗𝒪(L) ∘ w` maps `(0, c, s)` to `(0, wc, s + ⟨wc, deg L⟩)`. -/
theorem apply_affineEmbed (hb : ∀ x y, b x y = b y x) (g : F.extendedAffineWeyl)
    (y : (ι → ℤ) × ℤ) :
    (g : Aut(Λ)) (F.affineEmbed y) =
      F.affineEmbed (F.degreeSemidirectRep hb (F.toDegreeSemidirect hb g) y) := by
  rw [F.apply_eq_tensorLine_finitePart hb g, affineEmbed_apply,
    F.finiteWeyl_apply_rankZero hb (F.finitePart hb g).2, ← combination_rootRep]
  simp only [degreeSemidirectRep_apply, affineEmbed_apply, tensorLine_apply,
    toDegreeSemidirect_apply_right, coe_toAdd_toDegreeSemidirect_apply_left, zero_smul, add_zero,
    zero_mul]
  rw [hb, ← degree_dotProduct, dotProduct_comm]

/-- **The action of `W ⋉ Λ` on the affine root lattice is faithful**: if `(λ, w)` fixes every
`(eᵢ, 0)`, then `λ = 0` and `w` fixes every `αᵢ = (0, -Cᵢ, 0)`, so `w = 1` by the trivial
stabilizer (`eq_one_of_mem_finiteWeyl`). -/
theorem degreeSemidirectRep_injective (hb : ∀ x y, b x y = b y x) :
    Function.Injective (F.degreeSemidirectRep hb) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨x, w⟩ h
  have key : ∀ i, F.rootRep w (Pi.single i 1) = Pi.single i 1 ∧
      ((Multiplicative.toAdd x : F.degreeLattice) : ι → ℤ) i = 0 := by
    intro i
    have h1 := LinearMap.congr_fun h (Pi.single i 1, 0)
    simp only [degreeSemidirectRep_apply, one_apply_eq_self, Prod.mk.injEq, zero_add] at h1
    obtain ⟨h1, h2⟩ := h1
    rw [h1, single_dotProduct, one_mul] at h2
    exact ⟨h1, h2⟩
  have hw : (w : Aut(Λ)) = 1 := by
    refine F.eq_one_of_mem_finiteWeyl hb w.2 fun i => ?_
    have hC : ((w : Aut(Λ)) ((0 : ℤ), F.curve i, (0 : ℤ))).2.1 = F.curve i := by
      have := F.combination_rootRep w (Pi.single i 1)
      rw [(key i).1] at this
      simpa [combination] using this.symm
    have hfix : (w : Aut(Λ)) (F.affineRoot (some i)) = F.affineRoot (some i) := by
      rw [affineRoot_some, show ((0 : ℤ), -F.curve i, (0 : ℤ)) =
        -((0 : ℤ), F.curve i, (0 : ℤ)) by simp, map_neg, F.finiteWeyl_apply_mk w.2, hC]
    rw [hfix]
    exact F.isPositiveRoot_affineRoot _
  refine SemidirectProduct.ext (Multiplicative.toAdd.injective (Subtype.ext ?_)) (Subtype.ext hw)
  ext i
  exact (key i).2

end FundamentalCycle

end Mukai
