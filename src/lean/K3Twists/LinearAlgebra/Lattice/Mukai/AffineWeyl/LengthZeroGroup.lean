/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.Lattice.Mukai.AffineWeyl.Index
import K3Twists.LinearAlgebra.Lattice.Mukai.AffineWeyl.Minuscule

/-!
# The group of length-zero permutations and `P^∨/Q^∨`

For a connected exceptional fibre `F` in a lattice `N`, the extended affine Weyl group
`W_aff ⊔ E(N)` (`FundamentalCycle.extendedAffineWeyl`) is `E(N) ⋊ W(R)`: every element is
`⊗𝒪(L) ∘ w` with `w ∈ W(R)` (`exists_tensorLine_mul_of_mem_extendedAffineWeyl`), because `W(R)`
conjugates `⊗𝒪(L)` to `⊗𝒪(wL)` (`finiteWeyl_conj_tensorLine`, from the conjugation law of Eichler
transvections), and the line bundle `L` is read off as the middle coordinate of the image of
`(1, 0, 0)` (`translationPart_eq`). Its **length-zero elements** are those that permute the affine
simple roots (`FundamentalCycle.lengthZeroGroup`).

* **The class of a length-zero element**: the degree `(L·Cᵢ)ᵢ` of its line bundle, modulo the
  coroot lattice `Q^∨ = Aℤ^l`, is a homomorphism to `P^∨/Q^∨ = ℤ^l/Aℤ^l`
  (`FundamentalCycle.lengthZeroClass`): `⊗𝒪(L) w ⊗𝒪(L') w' = ⊗𝒪(L + wL') ww'` and `wL' - L'`
  lies in `⊕ ℤCᵢ`.
* **It has the same kernel as the permutation of the nodes** (`ker_lengthZeroPerm`): an element
  acting trivially on the affine roots has degree `0`; conversely, if the degree of `L` lies in
  `Q^∨`, then `L = D + L₀` with `D ∈ ⊕ ℤCᵢ` and `L₀ ⊥ Cᵢ`, the element acts on the affine roots as
  `⊗𝒪(D) w ∈ W_aff`, and the trivial stabilizer of `W_aff` makes it act trivially.
* **Its range is the image of `Λ = deg(N)`** in `P^∨/Q^∨` for an even lattice `N`
  (`lengthZeroClass_mem`, `exists_lengthZeroClass_eq`): every coset `⊗𝒪(L) W_aff` contains a
  length-zero element (`exists_mul_mem_affineRootStabilizer`).

The kernel of the action of the extended group on the affine roots is `E(N ∩ {Cᵢ}^⊥)`
(`fixes_affineRoot_iff`), so it acts through `W(R) ⋉ Λ`.

So **the permutations of the nodes induced by length-zero elements form a group isomorphic to
`Λ/Q^∨`** (`lengthZeroPermEquiv`), and to `P^∨/Q^∨` when every degree is realized, `Λ = ℤ^l`
(`lengthZeroPermEquivOfDegreeLattice`); its order is then `|det A|`
(`Nat.card_lengthZeroPerm_range`). The isometries themselves do not form a group of that order:
`E(N ∩ {Cᵢ}^⊥)` acts trivially on the affine roots (`tensorLine_fixes_affineRoot_iff`). This is the
class-level statement of Bourbaki, *Groupes et algèbres de Lie*, Ch. VI, §2.3, Proposition 6, and
Iwahori–Matsumoto, Publ. Math. IHÉS 25 (1965), §1.7–1.8: on a K3 surface only `Λ/Q^∨` is realized.
-/

namespace Mukai

variable {N : Type*} [AddCommGroup N]

/-- Automorphisms of the Mukai lattice. -/
local notation "Aut(Λ)" => MukaiLattice ℤ N ≃ₗ[ℤ] MukaiLattice ℤ N

namespace FundamentalCycle

variable {b : N →ₗ[ℤ] N →ₗ[ℤ] ℤ} {ι : Type*} [Fintype ι] (F : FundamentalCycle b ι)

/-! ### Line bundles -/

/-- **`E(N)` is the set of isometric line bundles**: for symmetric `b` the generators already form
a group. -/
theorem mem_lineTwists_iff (hb : ∀ x y, b x y = b y x) {g : Aut(Λ)} :
    g ∈ lineTwists b ↔ ∃ L : N, ∃ q : ℤ, 2 * q = b L L ∧ ∀ v, g v = tensorLine b L q v := by
  refine ⟨fun hg => ?_, fun hg => Subgroup.subset_closure hg⟩
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => exact ⟨0, 0, by simp, fun v => by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨L, q, hq, hx⟩ := hx
    obtain ⟨L', q', hq', hy⟩ := hy
    refine ⟨L + L', q + q' + b L L', ?_, fun v => ?_⟩
    · simp only [map_add, LinearMap.add_apply, hb L' L]
      linarith
    · rw [mul_apply_eq_comp, hy, hx, ← mul_apply_eq_comp, tensorLine_mul b hb]
  | inv x _ hx =>
    obtain ⟨L, q, hq, hx⟩ := hx
    refine ⟨-L, q, by simpa using hq, fun v => ?_⟩
    obtain ⟨w, rfl⟩ := x.surjective v
    rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply, hx, ← mul_apply_eq_comp,
      tensorLine_mul b hb, neg_add_cancel, map_neg, LinearMap.neg_apply,
      show q + q + -b L L = 0 by omega, tensorLine_zero]
    rfl

/-! ### `W(R)` conjugates line bundles -/

/-- `W(R)` maps `(0, L, 0)` to `(0, wL, 0)`. -/
theorem finiteWeyl_apply_mk {w : Aut(Λ)} (hw : w ∈ F.finiteWeyl) (L : N) :
    w ((0 : ℤ), L, (0 : ℤ)) = (0, (w ((0 : ℤ), L, (0 : ℤ))).2.1, 0) := by
  ext
  · exact F.apply_fst_of_mem_finiteWeyl hw _
  · rfl
  · exact F.apply_snd_snd_of_mem_finiteWeyl hw _

/-- **Conjugating a line bundle by `W(R)`**: `w ⊗𝒪(L) w⁻¹ = ⊗𝒪(wL)`, by the conjugation law
`g E(e, x, q) g⁻¹ = E(ge, gx, q)` at `e = δ`. -/
theorem finiteWeyl_conj_tensorLine (hb : ∀ x y, b x y = b y x) {w : Aut(Λ)}
    (hw : w ∈ F.finiteWeyl) (L : N) (q : ℤ) (v : MukaiLattice ℤ N) :
    w (tensorLine b L q (w.symm v)) = tensorLine b (w ((0 : ℤ), L, (0 : ℤ))).2.1 q v := by
  have hwA := F.finiteWeyl_le_affineWeyl hw
  have hwO : w ∈ orthogonalGroup b := F.affineWeyl_le_orthogonalGroup hb hwA
  have key := BilinearForm.conj_eichler (mukaiForm b) w hwO corankUnit (0, -L, 0) q
  have hδ : w corankUnit = corankUnit := (F.affineWeyl_le_rootPreserving hb hwA).2
  have hx : w ((0 : ℤ), -L, (0 : ℤ)) = (0, -(w ((0 : ℤ), L, (0 : ℤ))).2.1, 0) := by
    rw [show ((0 : ℤ), -L, (0 : ℤ)) = -((0 : ℤ), L, (0 : ℤ)) by ext <;> simp, map_neg,
      F.finiteWeyl_apply_mk hw]
    ext <;> simp
  rw [hδ, hx, ← tensorLine_eq_eichler, ← tensorLine_eq_eichler] at key
  have := LinearMap.congr_fun key v
  simpa [LinearEquiv.conj_apply_apply] using this

/-- `W(R)` preserves the form on `N`. -/
theorem finiteWeyl_self_apply (hb : ∀ x y, b x y = b y x) {w : Aut(Λ)} (hw : w ∈ F.finiteWeyl)
    (L : N) :
    b (w ((0 : ℤ), L, (0 : ℤ))).2.1 (w ((0 : ℤ), L, (0 : ℤ))).2.1 = b L L := by
  have := (F.affineWeyl_le_orthogonalGroup hb (F.finiteWeyl_le_affineWeyl hw))
    ((0 : ℤ), L, (0 : ℤ)) ((0 : ℤ), L, (0 : ℤ))
  rw [F.finiteWeyl_apply_mk hw] at this
  simpa using this

/-! ### The extended affine Weyl group is `E(N) ⋊ W(R)` -/

/-- **Every element of the extended affine Weyl group is a line bundle times an element of
`W(R)`**: `g = ⊗𝒪(L) ∘ w`. -/
theorem exists_tensorLine_mul_of_mem_extendedAffineWeyl (hb : ∀ x y, b x y = b y x)
    {g : Aut(Λ)} (hg : g ∈ F.extendedAffineWeyl) :
    ∃ (L : N) (q : ℤ), 2 * q = b L L ∧ ∃ w ∈ F.finiteWeyl, ∀ v, g v = tensorLine b L q (w v) := by
  rw [extendedAffineWeyl, Subgroup.sup_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · obtain ⟨t, ht, w, hw, rfl⟩ := F.exists_mul_eq_of_mem_affineWeyl hb hx
      obtain ⟨D, hD, htD⟩ := (F.mem_translations_iff hb).mp ht
      exact ⟨D, b D D / 2, F.two_mul_self_div_two hb hD, w, hw, fun v => by
        rw [mul_apply_eq_comp, htD]⟩
    · obtain ⟨L, q, hq, hx⟩ := (mem_lineTwists_iff hb).mp hx
      exact ⟨L, q, hq, 1, one_mem _, fun v => by rw [hx]; rfl⟩
  | one => exact ⟨0, 0, by simp, 1, one_mem _, fun v => by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨L, q, hq, w, hw, hx⟩ := hx
    obtain ⟨L', q', hq', w', hw', hy⟩ := hy
    set L'' := (w ((0 : ℤ), L', (0 : ℤ))).2.1
    refine ⟨L + L'', q + q' + b L L'', ?_, w * w', mul_mem hw hw', fun v => ?_⟩
    · have hnorm := F.finiteWeyl_self_apply hb hw L'
      simp only [map_add, LinearMap.add_apply, hb L'' L]
      linarith
    · have hconj := F.finiteWeyl_conj_tensorLine hb hw L' q' (w (w' v))
      rw [LinearEquiv.symm_apply_apply] at hconj
      rw [mul_apply_eq_comp, hy, hx, hconj, ← mul_apply_eq_comp (tensorLine b L q),
        tensorLine_mul b hb, mul_apply_eq_comp w w']
  | inv x _ hx =>
    obtain ⟨L, q, hq, w, hw, hx⟩ := hx
    have hw' : w⁻¹ ∈ F.finiteWeyl := inv_mem hw
    refine ⟨(w⁻¹ ((0 : ℤ), -L, (0 : ℤ))).2.1, q, ?_, w⁻¹, hw', fun v => ?_⟩
    · rw [F.finiteWeyl_self_apply hb hw' (-L)]
      simpa using hq
    · have hconj := F.finiteWeyl_conj_tensorLine hb hw' (-L) q (w⁻¹ v)
      rw [LinearEquiv.symm_apply_apply] at hconj
      rw [← hconj]
      show x.symm v = _
      rw [LinearEquiv.symm_apply_eq, hx,
        show w (w⁻¹ (tensorLine b (-L) q v)) = tensorLine b (-L) q v from w.apply_symm_apply _,
        ← mul_apply_eq_comp, tensorLine_mul b hb, add_neg_cancel, map_neg,
        show q + q + -b L L = 0 by omega, tensorLine_zero]
      rfl

/-! ### The translation part -/

/-- **The translation part** of an automorphism: the middle coordinate of the image of
`(1, 0, 0)`. For `⊗𝒪(L) ∘ w` with `w ∈ W(R)` it is `L` (`translationPart_eq`). -/
def translationPart (g : Aut(Λ)) : N :=
  (g rankUnit).2.1

theorem translationPart_eq {g w : Aut(Λ)} (hw : w ∈ F.finiteWeyl) {L : N} {q : ℤ}
    (hg : ∀ v, g v = tensorLine b L q (w v)) : translationPart g = L := by
  rw [translationPart, hg, F.finiteWeyl_apply_rankUnit hw]
  simp [rankUnit]

/-- The translation part is additive up to `⊕ ℤCᵢ` on the extended affine Weyl group:
`⊗𝒪(L) w ⊗𝒪(L') w' = ⊗𝒪(L + wL') ww'`. -/
theorem translationPart_mul_sub_mem (hb : ∀ x y, b x y = b y x) {g h : Aut(Λ)}
    (hg : g ∈ F.extendedAffineWeyl) (hh : h ∈ F.extendedAffineWeyl) :
    translationPart (g * h) - translationPart g - translationPart h ∈ F.rootLattice := by
  obtain ⟨L, q, -, w, hw, hgw⟩ := F.exists_tensorLine_mul_of_mem_extendedAffineWeyl hb hg
  obtain ⟨L', q', -, w', hw', hhw⟩ := F.exists_tensorLine_mul_of_mem_extendedAffineWeyl hb hh
  rw [F.translationPart_eq hw hgw, F.translationPart_eq hw' hhw]
  have hδ : w corankUnit = corankUnit :=
    (F.affineWeyl_le_rootPreserving hb (F.finiteWeyl_le_affineWeyl hw)).2
  have h1 : h rankUnit = rankUnit + ((0 : ℤ), L', (0 : ℤ)) + q' • corankUnit := by
    rw [hhw, F.finiteWeyl_apply_rankUnit hw']
    ext <;> simp [rankUnit, corankUnit]
  have h2 : translationPart (g * h) = (w ((0 : ℤ), L', (0 : ℤ))).2.1 + L := by
    rw [translationPart, mul_apply_eq_comp, h1, hgw]
    simp only [map_add, map_zsmul, F.finiteWeyl_apply_rankUnit hw, hδ]
    simp [rankUnit, corankUnit, F.apply_fst_of_mem_finiteWeyl hw]
    exact add_comm _ _
  rw [h2, add_sub_cancel_right]
  have := F.apply_snd_fst_sub_mem_of_mem_finiteWeyl hw ((0 : ℤ), L', (0 : ℤ))
  simpa using this

/-- The translation part of an element of `W_aff` lies in `⊕ ℤCᵢ`. -/
theorem translationPart_mem_of_mem_affineWeyl (hb : ∀ x y, b x y = b y x) {u : Aut(Λ)}
    (hu : u ∈ F.affineWeyl) : translationPart u ∈ F.rootLattice := by
  obtain ⟨t, ht, w, hw, rfl⟩ := F.exists_mul_eq_of_mem_affineWeyl hb hu
  obtain ⟨D, hD, htD⟩ := (F.mem_translations_iff hb).mp ht
  rw [F.translationPart_eq hw (fun v => by rw [mul_apply_eq_comp, htD])]
  exact hD

/-! ### The kernel of the action on the affine roots -/

/-- **The kernel of the action on the affine roots is `E(N ∩ {Cᵢ}^⊥)`.** An element of the extended
affine Weyl group fixes every affine simple root iff it is `⊗𝒪(L)` with `L·Cᵢ = 0` for every `i`.
So `⊗𝒪(L) ∘ w` acts on the affine root lattice through `w ∈ W(R)` and the degree of `L` alone:
the extended group acts through `W(R) ⋉ Λ`. The proof: on the finite nodes, `⊗𝒪(L) w αᵢ = αᵢ`
forces `wαᵢ = αᵢ` and `L·Cᵢ = 0`, and an element of `W(R)` fixing the finite simple roots is `1`
(`eq_one_of_mem_finiteWeyl`). -/
theorem fixes_affineRoot_iff (hb : ∀ x y, b x y = b y x) {g : Aut(Λ)}
    (hg : g ∈ F.extendedAffineWeyl) :
    (∀ k, g (F.affineRoot k) = F.affineRoot k) ↔
      ∃ (L : N) (q : ℤ), 2 * q = b L L ∧ (∀ i, b (F.curve i) L = 0) ∧
        ∀ v, g v = tensorLine b L q v := by
  constructor
  · intro hfix
    obtain ⟨L, q, hq, w, hw, hgw⟩ := F.exists_tensorLine_mul_of_mem_extendedAffineWeyl hb hg
    have key : ∀ i, w (F.affineRoot (some i)) = F.affineRoot (some i) ∧
        b (F.curve i) L = 0 := by
      intro i
      have h := hfix (some i)
      rw [hgw, affineRoot_some, F.finiteWeyl_apply_mk hw] at h
      have h2 := congrArg (fun v : MukaiLattice ℤ N => v.2.1) h
      have h3 := congrArg (fun v : MukaiLattice ℤ N => v.2.2) h
      simp only [tensorLine_apply, zero_smul, add_zero, zero_add, zero_mul] at h2 h3
      refine ⟨?_, ?_⟩
      · rw [affineRoot_some, F.finiteWeyl_apply_mk hw, h2]
      · rw [h2, map_neg, LinearMap.neg_apply, neg_eq_zero] at h3
        exact h3
    have hw1 : w = 1 := F.eq_one_of_mem_finiteWeyl hb hw fun i => by
      rw [(key i).1]
      exact F.isPositiveRoot_affineRoot _
    exact ⟨L, q, hq, fun i => (key i).2, fun v => by rw [hgw, hw1]; rfl⟩
  · rintro ⟨L, q, -, hL, hg'⟩ k
    rw [hg']
    exact (F.tensorLine_fixes_affineRoot_iff L q).mpr hL k

/-! ### Length-zero elements -/

/-- **The length-zero elements** of the extended affine Weyl group: those permuting the affine
simple roots. -/
def lengthZeroGroup : Subgroup Aut(Λ) :=
  F.affineRootStabilizer ⊓ F.extendedAffineWeyl

/-- The permutation of the nodes induced by a length-zero element. -/
noncomputable def lengthZeroPerm : F.lengthZeroGroup →* Equiv.Perm (Option ι) :=
  F.affineRootPerm.comp (Subgroup.inclusion inf_le_left)

theorem lengthZeroPerm_apply (g : F.lengthZeroGroup) (k : Option ι) :
    (g : Aut(Λ)) (F.affineRoot k) = F.affineRoot (F.lengthZeroPerm g k) :=
  F.apply_affineRoot (Subgroup.inclusion inf_le_left g) k

/-! ### The class in `P^∨/Q^∨` -/

variable [DecidableEq ι]

/-- The degree of a class supported on the fibre lies in the coroot lattice `Q^∨ = Aℤ^l`. -/
theorem degree_mem_corootLattice (hb : ∀ x y, b x y = b y x) {D : N} (hD : D ∈ F.rootLattice) :
    F.degree D ∈ F.corootLattice := by
  obtain ⟨d, rfl⟩ := hD
  refine ⟨-d, ?_⟩
  rw [Matrix.toLin'_apply, combination_apply, F.degree_combination hb, Matrix.mulVec_neg]

/-- **The class of an element of the extended affine Weyl group** in `P^∨/Q^∨ = ℤ^l/Aℤ^l`: the
degree of its translation part modulo the coroot lattice. -/
noncomputable def translationClass (hb : ∀ x y, b x y = b y x) :
    F.extendedAffineWeyl →* Multiplicative ((ι → ℤ) ⧸ F.corootLattice) where
  toFun g := Multiplicative.ofAdd (Submodule.Quotient.mk (F.degree (translationPart (g : Aut(Λ)))))
  map_one' := by simp [translationPart, rankUnit]
  map_mul' g h := by
    rw [← ofAdd_add, ← Submodule.Quotient.mk_add, ← map_add]
    congr 1
    rw [Submodule.Quotient.eq, ← map_sub]
    refine F.degree_mem_corootLattice hb ?_
    rw [sub_add_eq_sub_sub]
    exact F.translationPart_mul_sub_mem hb g.2 h.2

theorem translationClass_apply (hb : ∀ x y, b x y = b y x) (g : F.extendedAffineWeyl) :
    F.translationClass hb g =
      Multiplicative.ofAdd (Submodule.Quotient.mk (F.degree (translationPart (g : Aut(Λ))))) :=
  rfl

/-- **The class of a length-zero element in `P^∨/Q^∨`.** -/
noncomputable def lengthZeroClass (hb : ∀ x y, b x y = b y x) :
    F.lengthZeroGroup →* Multiplicative ((ι → ℤ) ⧸ F.corootLattice) :=
  (F.translationClass hb).comp (Subgroup.inclusion inf_le_right)

theorem lengthZeroClass_eq_one_iff (hb : ∀ x y, b x y = b y x) (g : F.lengthZeroGroup) :
    F.lengthZeroClass hb g = 1 ↔ F.degree (translationPart (g : Aut(Λ))) ∈ F.corootLattice := by
  rw [lengthZeroClass, MonoidHom.comp_apply, translationClass_apply, ← ofAdd_zero,
    EmbeddingLike.apply_eq_iff_eq, Submodule.Quotient.mk_eq_zero]
  rfl

/-- **The permutation and the class have the same kernel.** If the permutation is trivial, the
degree of the line bundle vanishes. If the degree lies in `Q^∨`, the line bundle is `D + L₀` with
`D ∈ ⊕ ℤCᵢ` and `L₀ ⊥ Cᵢ`, so the element acts on the affine roots as `⊗𝒪(D) w ∈ W_aff`, which is
trivial by the trivial stabilizer of `W_aff`. -/
theorem lengthZeroPerm_eq_one_iff (hb : ∀ x y, b x y = b y x) (g : F.lengthZeroGroup) :
    F.lengthZeroPerm g = 1 ↔ F.lengthZeroClass hb g = 1 := by
  obtain ⟨L, q, hq, w, hw, hgw⟩ :=
    F.exists_tensorLine_mul_of_mem_extendedAffineWeyl hb g.2.2
  have hL : translationPart (g : Aut(Λ)) = L := F.translationPart_eq hw hgw
  have hwA := F.finiteWeyl_le_affineWeyl hw
  have hwR := F.affineWeyl_le_rootPreserving hb hwA
  rw [lengthZeroClass_eq_one_iff, hL]
  constructor
  · -- trivial on the affine roots: the degree of `L` is zero
    intro h1
    have hdeg : F.degree L = 0 := by
      ext i
      have h := F.lengthZeroPerm_apply g (some i)
      rw [h1, Equiv.Perm.one_apply, hgw, affineRoot_some, F.finiteWeyl_apply_mk hw] at h
      have h2 := congrArg (fun v : MukaiLattice ℤ N => v.2.1) h
      have h3 := congrArg (fun v : MukaiLattice ℤ N => v.2.2) h
      simp only [tensorLine_apply, zero_smul, add_zero, zero_add, zero_mul] at h2 h3
      rw [h2, map_neg, LinearMap.neg_apply, neg_eq_zero] at h3
      rw [degree_apply, hb, h3, Pi.zero_apply]
    rw [hdeg]
    exact zero_mem _
  · intro hdeg
    obtain ⟨d', hd'⟩ := hdeg
    have hdegD : F.degree (F.combination (-d')) = F.degree L := by
      rw [← hd', Matrix.toLin'_apply, combination_apply, F.degree_combination hb,
        Matrix.mulVec_neg, neg_neg]
    set D := F.combination (-d')
    have hDQ : D ∈ F.rootLattice := ⟨-d', rfl⟩
    -- `L - D` is orthogonal to the fibre
    have horth : ∀ c ∈ F.rootLattice, b c L = b c D := by
      rintro _ ⟨d, rfl⟩
      simp only [combination_apply, map_sum, LinearMap.sum_apply, map_zsmul,
        LinearMap.smul_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      have := congrFun hdegD i
      simp only [degree_apply] at this
      rw [hb (F.curve i) L, hb (F.curve i) D, this]
    -- `u = ⊗𝒪(D) w ∈ W_aff` acts on the affine roots as `g`
    set u := tensorLineEquiv hb D (F.two_mul_self_div_two hb hDQ) * w
    have hu : u ∈ F.affineWeyl :=
      mul_mem (F.translations_le_affineWeyl hb (Subgroup.subset_closure ⟨D, hDQ, fun v => rfl⟩))
        hwA
    have hug : ∀ k, u (F.affineRoot k) = (g : Aut(Λ)) (F.affineRoot k) := by
      intro k
      have hr : F.IsRoot (w (F.affineRoot k)) := (hwR.1 _).mpr (F.isRoot_affineRoot k)
      rw [hgw, mul_apply_eq_comp, tensorLineEquiv_apply]
      generalize w (F.affineRoot k) = v at hr ⊢
      obtain ⟨r, c, s⟩ := v
      obtain ⟨h1, h2, -⟩ := hr
      simp only at h1 h2
      subst h1
      simp only [tensorLine_apply, zero_smul, add_zero, zero_mul, horth c h2]
    have hstab : u ∈ F.affineRootStabilizer :=
      ⟨F.lengthZeroPerm g, fun k => by rw [hug, F.lengthZeroPerm_apply]⟩
    have hu1 : u = 1 := by
      have := Subgroup.mem_inf.mpr ⟨hu, hstab⟩
      rwa [F.affineWeyl_inf_affineRootStabilizer hb, Subgroup.mem_bot] at this
    refine Equiv.ext fun k => F.affineRoot_injective ?_
    rw [Equiv.Perm.one_apply, ← F.lengthZeroPerm_apply, ← hug, hu1]
    rfl

/-- The two kernels agree. -/
theorem ker_lengthZeroPerm (hb : ∀ x y, b x y = b y x) :
    F.lengthZeroPerm.ker = (F.lengthZeroClass hb).ker := by
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  exact F.lengthZeroPerm_eq_one_iff hb g

/-- **The length-zero permutations form a group isomorphic to the group of classes of length-zero
elements in `P^∨/Q^∨`.** -/
noncomputable def lengthZeroPermEquiv (hb : ∀ x y, b x y = b y x) :
    F.lengthZeroPerm.range ≃* (F.lengthZeroClass hb).range :=
  (QuotientGroup.quotientKerEquivRange F.lengthZeroPerm).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (F.ker_lengthZeroPerm hb)).trans
      (QuotientGroup.quotientKerEquivRange (F.lengthZeroClass hb)))

/-- **Every class of `Λ/Q^∨` is the class of a length-zero element**, for an even lattice: the
coset `⊗𝒪(L) W_aff` contains a length-zero element, and `W_aff` has translation parts in
`⊕ ℤCᵢ`. -/
theorem exists_lengthZeroClass_eq (hb : ∀ x y, b x y = b y x) (heven : ∀ L : N, Even (b L L))
    (L : N) : ∃ g : F.lengthZeroGroup,
      F.lengthZeroClass hb g = Multiplicative.ofAdd (Submodule.Quotient.mk (F.degree L)) := by
  obtain ⟨q, hq⟩ : ∃ q, 2 * q = b L L := by
    obtain ⟨m, hm⟩ := heven L
    exact ⟨m, by omega⟩
  set t := tensorLineEquiv hb L hq
  have htE : t ∈ F.extendedAffineWeyl :=
    Subgroup.mem_sup_right (Subgroup.subset_closure ⟨L, q, hq, fun v => rfl⟩)
  obtain ⟨u, hu, htu⟩ :=
    F.exists_mul_mem_affineRootStabilizer hb (F.extendedAffineWeyl_le_rootPreserving hb htE)
  have huE : u ∈ F.extendedAffineWeyl := Subgroup.mem_sup_left hu
  refine ⟨⟨t * u, htu, mul_mem htE huE⟩, ?_⟩
  rw [lengthZeroClass, MonoidHom.comp_apply, translationClass_apply,
    EmbeddingLike.apply_eq_iff_eq, Submodule.Quotient.eq, ← map_sub]
  refine F.degree_mem_corootLattice hb ?_
  show translationPart (t * u) - L ∈ F.rootLattice
  have h1 := F.translationPart_mul_sub_mem hb htE huE
  have h2 := F.translationPart_mem_of_mem_affineWeyl hb hu
  have h3 : translationPart t = L := F.translationPart_eq (one_mem _) (fun v => rfl)
  rw [h3] at h1
  have := add_mem h1 h2
  rwa [sub_add_cancel] at this

/-- **When every degree is realized (`Λ = ℤ^l`), every class of `P^∨/Q^∨` is the class of a
length-zero element.** -/
theorem lengthZeroClass_surjective (hb : ∀ x y, b x y = b y x) (heven : ∀ L : N, Even (b L L))
    (hΛ : F.degreeLattice = ⊤) : Function.Surjective (F.lengthZeroClass hb) := by
  intro x
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (Multiplicative.toAdd x)
  obtain ⟨L, rfl⟩ : y ∈ LinearMap.range F.degree := by
    rw [← degreeLattice, hΛ]
    trivial
  obtain ⟨g, hg⟩ := F.exists_lengthZeroClass_eq hb heven L
  exact ⟨g, by rw [hg, hy]; rfl⟩

/-- **When every degree is realized, the length-zero permutations form a group isomorphic to
`P^∨/Q^∨`.** -/
noncomputable def lengthZeroPermEquivOfDegreeLattice (hb : ∀ x y, b x y = b y x)
    (heven : ∀ L : N, Even (b L L)) (hΛ : F.degreeLattice = ⊤) :
    F.lengthZeroPerm.range ≃* Multiplicative ((ι → ℤ) ⧸ F.corootLattice) :=
  (F.lengthZeroPermEquiv hb).trans
    ((MulEquiv.subgroupCongr
      (MonoidHom.range_eq_top.mpr (F.lengthZeroClass_surjective hb heven hΛ))).trans
      Subgroup.topEquiv)

/-- **The group of length-zero permutations has order `|det A|`** when every degree is
realized. -/
theorem card_lengthZeroPerm_range (hb : ∀ x y, b x y = b y x) (heven : ∀ L : N, Even (b L L))
    (hΛ : F.degreeLattice = ⊤) : Nat.card F.lengthZeroPerm.range = F.cartan.det.natAbs := by
  rw [Nat.card_congr (F.lengthZeroPermEquivOfDegreeLattice hb heven hΛ).toEquiv,
    Nat.card_congr Multiplicative.toAdd, ← F.index_corootLattice]
  rfl

end FundamentalCycle

end Mukai
