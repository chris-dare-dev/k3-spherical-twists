/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.Lattice.Mukai.AffineWeyl.SimpleReflection

/-!
# Length-zero elements at every minuscule node

For a connected exceptional fibre `F` (`Mukai.FundamentalCycle`), a node `j` is **minuscule** when
its multiplicity in the fundamental cycle is one, `zⱼ = 1`. For such a node and a class `M` with
`M·Cᵢ = δᵢⱼ` (a class realizing the fundamental coweight `ωⱼ^∨`), there is an element `w` of the
finite Weyl group `W(R)` such that **`⊗𝒪(M) ∘ w` permutes the affine simple roots and sends `α₀` to
`αⱼ`** (`FundamentalCycle.exists_lengthZero_of_minuscule`). Bourbaki, *Groupes et algèbres de Lie*,
Ch. VI, §2.3, Proposition 6, takes `w = w₀^{(j)} w₀`; the proof here needs no longest element.

## The descent

The **inversion set** of an automorphism `g` is the set of positive roots that `g` sends to
negative roots (`FundamentalCycle.inversionSet`). For `g` preserving the roots and fixing `δ` it is
finite (`inversionSet_finite`): a positive root `(0, c, s)` has `c` among the finitely many roots of
the fibre lattice and `0 ≤ s`, and `g(0, c, s) = g(0, c, 0) + sδ` is negative only for `s` below a
bound depending on `c`. If `g` sends `αₖ` to a negative root, then `g sₖ` has one inversion fewer
(`ncard_inversionSet_mul_simpleReflection`), because `sₖ` permutes the positive roots other than
`αₖ`. So multiplying `g` on the right by simple reflections at nodes of a set `K` reaches an
element that keeps every `αₖ`, `k ∈ K`, positive (`exists_forall_isPositiveRoot`):

* with `K` all nodes, **every coset `g W_aff` contains an element permuting the affine simple
  roots** (`exists_mul_mem_affineRootStabilizer`), and by the trivial stabilizer of `W_aff`
  exactly one (`eq_of_mul_mem_affineRootStabilizer`);
* with `K` the finite nodes and `g = ⊗𝒪(M)` for a minuscule `M`, the result `⊗𝒪(M) w` keeps the
  finite simple roots positive, and the image `(0, wΘ, 1 + (wΘ)ⱼ)` of `α₀` is positive because
  `|(wΘ)ⱼ| ≤ zⱼ = 1`; so it permutes the affine simple roots, and comparing coordinates shows that
  it sends `α₀` to `αⱼ`.

## References

* N. Bourbaki, *Groupes et algèbres de Lie*, Ch. VI, §2.3.
* N. Iwahori and H. Matsumoto, *On some Bruhat decomposition and the structure of the Hecke rings
  of 𝔭-adic Chevalley groups*, Publ. Math. IHÉS 25 (1965).
-/

namespace Mukai

variable {N : Type*} [AddCommGroup N]

/-- Automorphisms of the Mukai lattice. -/
local notation "Aut(Λ)" => MukaiLattice ℤ N ≃ₗ[ℤ] MukaiLattice ℤ N

namespace FundamentalCycle

variable {b : N →ₗ[ℤ] N →ₗ[ℤ] ℤ} {ι : Type*} [Fintype ι] (F : FundamentalCycle b ι)

theorem simpleReflection_mem_affineWeyl (k : Option ι) : F.simpleReflection k ∈ F.affineWeyl :=
  Subgroup.subset_closure (F.simpleReflection_mem_affineReflections k)

theorem simpleReflection_mem_finiteWeyl (i : ι) : F.simpleReflection (some i) ∈ F.finiteWeyl :=
  Subgroup.subset_closure
    ⟨-F.curve i, (F.isRoot_affineRoot (some i)).2.1, F.isSpherical_affineRoot (some i), rfl⟩

/-! ### Inversion sets -/

/-- **The inversion set** of an automorphism: the positive roots it sends to negative roots. -/
def inversionSet (g : Aut(Λ)) : Set (MukaiLattice ℤ N) :=
  {v | F.IsPositiveRoot v ∧ F.IsPositiveRoot (-(g v))}

/-- **The inversion set is finite** for an automorphism preserving the roots and fixing `δ`. -/
theorem inversionSet_finite (hb : ∀ x y, b x y = b y x) {g : Aut(Λ)}
    (hg : g ∈ F.rootPreserving) : (F.inversionSet g).Finite := by
  have hbox : (Set.pi Set.univ fun i => Set.Icc (-F.mult i) (F.mult i)).Finite :=
    Set.Finite.pi fun i => Set.finite_Icc _ _
  refine (hbox.biUnion fun d _ => (Set.finite_Icc (0 : ℤ)
      (-(g ((0 : ℤ), F.combination d, (0 : ℤ))).2.2)).image
      fun s => ((0 : ℤ), F.combination d, s)).subset ?_
  rintro v ⟨⟨hroot, x, hx, hxv⟩, ⟨-, y, hy, hyv⟩⟩
  obtain ⟨d, hd⟩ := hroot.2.1
  have hd2 : b (∑ i, d i • F.curve i) (∑ i, d i • F.curve i) = -2 := by
    rw [← combination_apply, hd]
    exact hroot.2.2
  have hv : v = (0, F.combination d, v.2.2) := by
    ext
    · exact hroot.1
    · exact hd.symm
    · rfl
  have hs0 : 0 ≤ v.2.2 := by
    rw [← hxv, snd_snd_sum_smul_affineRoot]
    exact hx none
  have hgv : g v = g ((0 : ℤ), F.combination d, (0 : ℤ)) + v.2.2 • corankUnit := by
    conv_lhs => rw [hv]
    rw [show ((0 : ℤ), F.combination d, v.2.2) =
        ((0 : ℤ), F.combination d, (0 : ℤ)) + v.2.2 • (corankUnit : MukaiLattice ℤ N) by
      ext <;> simp [corankUnit], map_add, map_zsmul, hg.2]
  have hlev : 0 ≤ (-(g v)).2.2 := by
    rw [← hyv, snd_snd_sum_smul_affineRoot]
    exact hy none
  rw [hgv] at hlev
  simp only [Prod.snd_neg, Prod.snd_add, Prod.smul_snd, corankUnit, smul_eq_mul, mul_one] at hlev
  refine Set.mem_biUnion (x := d)
    (fun i _ => ⟨F.neg_mult_le_of_root hb hd2 i, F.le_mult_of_root hb hd2 i⟩)
    ⟨v.2.2, ⟨hs0, by linarith⟩, hv.symm⟩

/-- **One step of the descent.** If `g` sends `αₖ` to a negative root, the inversion set of
`g sₖ` is the image under `sₖ` of the inversion set of `g` without `αₖ`. -/
theorem inversionSet_mul_simpleReflection (hb : ∀ x y, b x y = b y x) {g : Aut(Λ)}
    {k : Option ι} (hk : F.IsPositiveRoot (-(g (F.affineRoot k)))) :
    F.inversionSet (g * F.simpleReflection k) =
      F.simpleReflection k '' (F.inversionSet g \ {F.affineRoot k}) := by
  have hself : F.simpleReflection k (F.affineRoot k) = -F.affineRoot k := by
    rw [simpleReflection_apply, reflect_self _ _ (F.isSpherical_affineRoot k)]
  have hinv : ∀ v, F.simpleReflection k (F.simpleReflection k v) = v := fun v => by
    rw [← mul_apply_eq_comp, simpleReflection_mul_self]
    rfl
  ext v
  constructor
  · rintro ⟨hv, hgv⟩
    have hne : v ≠ F.affineRoot k := by
      rintro rfl
      rw [mul_apply_eq_comp, hself, map_neg, neg_neg] at hgv
      exact hgv.not_neg hk
    refine ⟨F.simpleReflection k v, ⟨⟨?_, ?_⟩, ?_⟩, hinv v⟩
    · rw [simpleReflection_apply]
      exact hv.reflect_affineRoot hb hne
    · rwa [mul_apply_eq_comp] at hgv
    · intro h
      have h' := congrArg (F.simpleReflection k) h
      rw [hinv, hself] at h'
      rw [h'] at hv
      exact hv.not_neg (by rw [neg_neg]; exact F.isPositiveRoot_affineRoot k)
  · rintro ⟨u, ⟨⟨hu, hgu⟩, hne⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [simpleReflection_apply]
      exact hu.reflect_affineRoot hb hne
    · rwa [mul_apply_eq_comp, hinv]

/-- If `g` sends `αₖ` to a negative root, `g sₖ` has one inversion fewer. -/
theorem ncard_inversionSet_mul_simpleReflection (hb : ∀ x y, b x y = b y x) {g : Aut(Λ)}
    (hg : g ∈ F.rootPreserving) {k : Option ι} (hk : F.IsPositiveRoot (-(g (F.affineRoot k)))) :
    (F.inversionSet (g * F.simpleReflection k)).ncard + 1 = (F.inversionSet g).ncard := by
  rw [F.inversionSet_mul_simpleReflection hb hk,
    Set.ncard_image_of_injective _ (F.simpleReflection k).injective,
    Set.ncard_sdiff_singleton_add_one
      (show F.affineRoot k ∈ F.inversionSet g from ⟨F.isPositiveRoot_affineRoot k, hk⟩)
      (F.inversionSet_finite hb hg)]

/-- **The descent.** For `g` preserving the roots and a set `K` of nodes, some word `ω` in the
nodes of `K` makes `g ω` keep every `αₖ`, `k ∈ K`, positive. -/
theorem exists_forall_isPositiveRoot (hb : ∀ x y, b x y = b y x) (K : Set (Option ι))
    {g : Aut(Λ)} (hg : g ∈ F.rootPreserving) :
    ∃ ω : List (Option ι), (∀ l ∈ ω, l ∈ K) ∧
      ∀ k ∈ K, F.IsPositiveRoot ((g * (ω.map F.simpleReflection).prod) (F.affineRoot k)) := by
  induction h : (F.inversionSet g).ncard using Nat.strong_induction_on generalizing g with
  | _ n ih =>
    by_cases hall : ∀ k ∈ K, F.IsPositiveRoot (g (F.affineRoot k))
    · exact ⟨[], by simp, fun k hk => by simpa using hall k hk⟩
    obtain ⟨k, hkK, hk⟩ := not_forall₂.mp hall
    have hroot : F.IsRoot (g (F.affineRoot k)) := (hg.1 _).mpr (F.isRoot_affineRoot k)
    have hneg : F.IsPositiveRoot (-(g (F.affineRoot k))) :=
      (F.isPositiveRoot_or_neg hb hroot).resolve_left hk
    have hg' : g * F.simpleReflection k ∈ F.rootPreserving :=
      mul_mem hg (F.affineWeyl_le_rootPreserving hb (F.simpleReflection_mem_affineWeyl k))
    have hlt := F.ncard_inversionSet_mul_simpleReflection hb hg hneg
    obtain ⟨ω, hω, hpos⟩ := ih _ (by omega) hg' rfl
    refine ⟨k :: ω, fun l hl => ?_, fun l hl => ?_⟩
    · rcases List.mem_cons.mp hl with rfl | hl
      · exact hkK
      · exact hω l hl
    · rw [List.map_cons, List.prod_cons, ← mul_assoc]
      exact hpos l hl

/-- A word in the nodes of `K` lies in the group generated by the simple reflections at `K`; for
all nodes this is `W_aff`, for the finite nodes `W(R)`. -/
theorem prod_map_simpleReflection_mem_affineWeyl (hb : ∀ x y, b x y = b y x)
    (ω : List (Option ι)) : (ω.map F.simpleReflection).prod ∈ F.affineWeyl := by
  rw [F.affineWeyl_eq_closure hb]
  exact F.prod_map_simpleReflection_mem_closure (by simp)

theorem prod_map_simpleReflection_mem_finiteWeyl (hb : ∀ x y, b x y = b y x)
    {ω : List (Option ι)} (hω : ∀ l ∈ ω, l ∈ Set.range some) :
    (ω.map F.simpleReflection).prod ∈ F.finiteWeyl := by
  rw [F.finiteWeyl_eq_closure hb]
  exact F.prod_map_simpleReflection_mem_closure hω

/-! ### A length-zero element in every coset of `W_aff` -/

/-- **Every coset `g W_aff` of an automorphism preserving the roots contains an element that
permutes the affine simple roots.** -/
theorem exists_mul_mem_affineRootStabilizer (hb : ∀ x y, b x y = b y x) {g : Aut(Λ)}
    (hg : g ∈ F.rootPreserving) : ∃ u ∈ F.affineWeyl, g * u ∈ F.affineRootStabilizer := by
  obtain ⟨ω, -, hpos⟩ := F.exists_forall_isPositiveRoot hb Set.univ hg
  have hu := F.prod_map_simpleReflection_mem_affineWeyl hb ω
  exact ⟨_, hu, F.mem_affineRootStabilizer_of_forall hb
    (mul_mem hg (F.affineWeyl_le_rootPreserving hb hu)) fun k => hpos k (Set.mem_univ k)⟩

/-- **The element is unique**: two elements of one coset of `W_aff` that both permute the affine
simple roots are equal. -/
theorem eq_of_mul_mem_affineRootStabilizer (hb : ∀ x y, b x y = b y x) {g : Aut(Λ)} {u u' : Aut(Λ)}
    (hu : u ∈ F.affineWeyl) (hu' : u' ∈ F.affineWeyl) (h : g * u ∈ F.affineRootStabilizer)
    (h' : g * u' ∈ F.affineRootStabilizer) : g * u = g * u' := by
  have hmem : u⁻¹ * u' ∈ F.affineWeyl ⊓ F.affineRootStabilizer := by
    refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hu) hu', ?_⟩
    have := mul_mem (inv_mem h) h'
    rwa [_root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left] at this
  rw [F.affineWeyl_inf_affineRootStabilizer hb, Subgroup.mem_bot] at hmem
  rw [inv_mul_eq_one] at hmem
  rw [hmem]

/-! ### Minuscule nodes -/

/-- The image of the combination `Σ dᵢ Cᵢ` under a class `M` with `M·Cᵢ = δᵢⱼ` is `dⱼ`. -/
theorem combination_apply_of_dual [DecidableEq ι] {j : ι} {M : N}
    (hM : ∀ i, b (F.curve i) M = if i = j then 1 else 0) (d : ι → ℤ) :
    b (F.combination d) M = d j := by
  rw [combination_apply, map_sum, LinearMap.sum_apply]
  simp only [map_zsmul, LinearMap.smul_apply, hM, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

theorem combination_neg_single [DecidableEq ι] (i : ι) :
    F.combination (-Pi.single i 1) = -F.curve i := by
  rw [map_neg, combination, Fintype.linearCombination_apply_single, one_smul]

/-- **Length-zero elements at a minuscule node.** Let `j` be a node of multiplicity `zⱼ = 1` and
`M` a class with `M·Cᵢ = δᵢⱼ` and `2q = M²`. Then for some `w ∈ W(R)` the isometry
`⊗𝒪(M) ∘ w` permutes the affine simple roots and sends `α₀` to `αⱼ`. -/
theorem exists_lengthZero_of_minuscule [DecidableEq ι] (hb : ∀ x y, b x y = b y x) {j : ι}
    (hj : F.mult j = 1) {M : N} (hM : ∀ i, b (F.curve i) M = if i = j then 1 else 0) {q : ℤ}
    (hq : 2 * q = b M M) :
    ∃ w ∈ F.finiteWeyl, tensorLineEquiv hb M hq * w ∈ F.affineRootStabilizer ∧
      (tensorLineEquiv hb M hq * w) (F.affineRoot none) = F.affineRoot (some j) := by
  classical
  set t := tensorLineEquiv hb M hq
  have ht : t ∈ F.rootPreserving :=
    F.lineTwists_le_rootPreserving (Subgroup.subset_closure ⟨M, q, hq, fun v => rfl⟩)
  obtain ⟨ω, hω, hpos⟩ := F.exists_forall_isPositiveRoot hb (Set.range some) ht
  set w := (ω.map F.simpleReflection).prod
  have hw : w ∈ F.finiteWeyl := F.prod_map_simpleReflection_mem_finiteWeyl hb hω
  have hwR : w ∈ F.rootPreserving :=
    F.affineWeyl_le_rootPreserving hb (F.finiteWeyl_le_affineWeyl hw)
  have hgw : t * w ∈ F.rootPreserving := mul_mem ht hwR
  -- `w α₀ = (0, c, 1)` for a root `c` of the fibre lattice, `c = Σ dᵢ Cᵢ`
  set c := (w (F.affineRoot none)).2.1
  have hw0 : w (F.affineRoot none) = (0, c, 1) := by
    ext
    · rw [F.apply_fst_of_mem_finiteWeyl hw]
      rfl
    · rfl
    · rw [F.apply_snd_snd_of_mem_finiteWeyl hw]
      rfl
  have hcroot : F.IsRoot ((0, c, 1) : MukaiLattice ℤ N) := by
    rw [← hw0]
    exact (hwR.1 _).mpr (F.isRoot_affineRoot none)
  obtain ⟨d, hd⟩ := hcroot.2.1
  have hd : F.combination d = c := hd
  have hd2 : b (∑ i, d i • F.curve i) (∑ i, d i • F.curve i) = -2 := by
    rw [← combination_apply, hd]
    exact hcroot.2.2
  have hdj : b c M = d j := by
    rw [← hd]
    exact F.combination_apply_of_dual hM d
  -- `(⊗𝒪(M) w)(α₀) = (0, c, 1 + dⱼ)`
  have himg : (t * w) (F.affineRoot none) = (0, c, 1 + d j) := by
    rw [mul_apply_eq_comp, hw0]
    simp [t, hdj]
  -- it is positive: its coordinate at `j` is `(1 + dⱼ) zⱼ - dⱼ = 1`
  have hpos0 : F.IsPositiveRoot ((t * w) (F.affineRoot none)) := by
    have hr : F.IsRoot ((t * w) (F.affineRoot none)) := (hgw.1 _).mpr (F.isRoot_affineRoot none)
    rcases F.isPositiveRoot_or_neg hb hr with h | ⟨-, y, hy, hyv⟩
    · exact h
    · exfalso
      have hcoord : ∑ k, (-F.affineCoord (1 + d j) d) k • F.affineRoot k =
          -((t * w) (F.affineRoot none)) := by
        rw [himg]
        simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib,
          sum_affineCoord_smul_affineRoot, ← combination_apply, hd]
      have hyc := F.sum_smul_affineRoot_injective (hyv.trans hcoord.symm)
      have h2 := congrFun hyc (some j)
      simp only [Pi.neg_apply, affineCoord, hj, mul_one] at h2
      have := hy (some j)
      omega
  have hstab := F.mem_affineRootStabilizer_of_forall hb hgw fun k => by
    cases k with
    | none => exact hpos0
    | some i => exact hpos (some i) ⟨i, rfl⟩
  refine ⟨w, hw, hstab, ?_⟩
  obtain ⟨σ, hσ⟩ := hstab
  have hval := hσ none
  rw [himg] at hval
  rw [hσ none]
  cases hm : σ none with
  | none =>
    exfalso
    rw [hm, affineRoot_none] at hval
    have h3 : 1 + d j = 1 := congrArg (fun v : MukaiLattice ℤ N => v.2.2) hval
    have h2 : c = F.cycle := congrArg (fun v : MukaiLattice ℤ N => v.2.1) hval
    have : d = F.mult := F.combination_injective (by rw [hd, h2]; rfl)
    rw [this, hj] at h3
    omega
  | some i =>
    rw [hm, affineRoot_some] at hval
    have h3 : 1 + d j = 0 := congrArg (fun v : MukaiLattice ℤ N => v.2.2) hval
    have h2 : c = -F.curve i := congrArg (fun v : MukaiLattice ℤ N => v.2.1) hval
    have hdi : d = -Pi.single i 1 :=
      F.combination_injective (by rw [hd, h2, F.combination_neg_single])
    by_cases hij : i = j
    · rw [hij]
    · exfalso
      rw [hdi] at h3
      simp [Ne.symm hij] at h3

end FundamentalCycle

end Mukai
