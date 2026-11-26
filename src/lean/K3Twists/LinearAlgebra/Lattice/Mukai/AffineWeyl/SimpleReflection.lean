/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.GroupTheory.Coxeter.Deletion
import K3Twists.LinearAlgebra.Lattice.Mukai.AffineWeyl.LengthZero

/-!
# Simple reflections of an exceptional fibre

For a connected exceptional fibre `F` (`Mukai.FundamentalCycle`), the **real affine roots** are
the rank-zero classes `(0, c, s)` with `c ∈ ⊕ ℤCᵢ` and `c² = -2` (`FundamentalCycle.IsRoot`). By
sign coherence each is positive or negative in the affine simple roots
(`FundamentalCycle.isPositiveRoot_or_neg`). This file adds what the simple reflections
`sₖ = ρ_{αₖ}` (`FundamentalCycle.simpleReflection`) do with them, with no Coxeter-group theory:

* the affine simple roots are linearly independent (`sum_smul_affineRoot_injective`), so a root
  and its negative are not both positive (`IsPositiveRoot.not_neg`);
* **`sₖ` maps the positive roots other than `αₖ` to positive roots**
  (`IsPositiveRoot.reflect_affineRoot`): it changes one coordinate, and a root with a single
  nonzero coordinate is `±αₖ`;
* **every positive root is `ω(αₖ)` for a word `ω` of simple reflections**, by descent on the
  height (`exists_reflectWord_affineRoot`); a root of level zero needs only the simple reflections
  of the finite nodes. So **the simple reflections generate `W_aff`**, and those of the finite
  nodes generate `W(R)` (`affineWeyl_eq_closure`, `finiteWeyl_eq_closure`);
* **trivial stabilizer** (`eq_one_of_mem_affineWeyl`): an element of `W_aff` that keeps every
  affine simple root positive is the identity, from the deletion argument
  (`BilinearForm.reflectWord_eq_one_of_forall_mem`) with `P` the positive roots. In particular
  `W_aff` meets the stabilizer of the affine simple roots only in `1`
  (`affineWeyl_inf_affineRootStabilizer`), and an element of `W(R)` that keeps every finite simple
  root positive is the identity (`eq_one_of_mem_finiteWeyl`);
* **an automorphism preserving the roots that maps every affine simple root to a positive root
  permutes the affine simple roots** (`mem_affineRootStabilizer_of_forall`).

Every element of the extended affine Weyl group `W_aff ⊔ E(N)` preserves the roots of the fibre and
fixes the class `δ` of a point (`isRoot_apply_iff_of_mem_extendedAffineWeyl`,
`apply_corankUnit_of_mem_extendedAffineWeyl`); the elements of `W(R)` preserve the rank and the
last coordinate of every class (`apply_fst_of_mem_finiteWeyl`, `apply_snd_snd_of_mem_finiteWeyl`)
and move the middle one by a class of `⊕ ℤCᵢ` (`apply_snd_fst_sub_mem_of_mem_finiteWeyl`).

## References

* J. E. Humphreys, *Reflection groups and Coxeter groups*, §1.4–§1.7 and §4.6.
* V. G. Kac, *Infinite dimensional Lie algebras*, §3.7, §5.1.
-/

open Matrix

namespace Mukai

variable {N : Type*} [AddCommGroup N]

/-- Automorphisms of the Mukai lattice. -/
local notation "Aut(Λ)" => MukaiLattice ℤ N ≃ₗ[ℤ] MukaiLattice ℤ N

namespace FundamentalCycle

variable {b : N →ₗ[ℤ] N →ₗ[ℤ] ℤ} {ι : Type*} [Fintype ι] (F : FundamentalCycle b ι)

/-! ### Coordinates in the affine simple roots -/

/-- `d ↦ Σ dᵢ Cᵢ` is injective: the curves are linearly independent. -/
theorem combination_injective : Function.Injective F.combination := by
  intro d d' h
  have h0 : F.combination (d - d') = 0 := by rw [map_sub, h, sub_self]
  refine sub_eq_zero.mp (F.eq_zero_of_self_combination ?_)
  rw [← combination_apply, h0]
  simp

/-- **The affine simple roots are linearly independent**: coordinates are unique. -/
theorem sum_smul_affineRoot_injective :
    Function.Injective fun x : Option ι → ℤ => ∑ k, x k • F.affineRoot k := by
  intro x y h
  simp only [sum_smul_affineRoot] at h
  have h3 : x none = y none := congrArg (fun v : MukaiLattice ℤ N => v.2.2) h
  have h2 : ∑ i, (x none * F.mult i - x (some i)) • F.curve i =
      ∑ i, (y none * F.mult i - y (some i)) • F.curve i :=
    congrArg (fun v : MukaiLattice ℤ N => v.2.1) h
  have hd := F.combination_injective (by simpa only [combination_apply] using h2)
  ext k
  cases k with
  | none => exact h3
  | some i =>
    have := congrFun hd i
    simp only [h3] at this
    linarith

theorem mukaiForm_self_of_fst_eq_zero {w : MukaiLattice ℤ N} (h : w.1 = 0) :
    mukaiForm b w w = b w.2.1 w.2.1 := by
  obtain ⟨r, c, s⟩ := w
  simp only at h
  subst h
  exact mukaiForm_rankZero (b := b) c c s s

theorem mukaiForm_affineRoot_self (k : Option ι) :
    mukaiForm b (F.affineRoot k) (F.affineRoot k) = -2 :=
  F.isSpherical_affineRoot k

/-! ### Roots -/

variable {F}

theorem IsRoot.mukaiForm_self {v : MukaiLattice ℤ N} (hv : F.IsRoot v) : mukaiForm b v v = -2 := by
  rw [mukaiForm_self_of_fst_eq_zero hv.1]
  exact hv.2.2

theorem IsRoot.ne_zero {v : MukaiLattice ℤ N} (hv : F.IsRoot v) : v ≠ 0 := by
  rintro rfl
  have := hv.2.2
  simp at this

theorem IsPositiveRoot.isRoot {v : MukaiLattice ℤ N} (hv : F.IsPositiveRoot v) : F.IsRoot v :=
  hv.1

/-- A root and its negative are not both positive. -/
theorem IsPositiveRoot.not_neg {v : MukaiLattice ℤ N} (hv : F.IsPositiveRoot v) :
    ¬F.IsPositiveRoot (-v) := by
  rintro ⟨-, y, hy, hyv⟩
  obtain ⟨hr, x, hx, hxv⟩ := hv
  have h0 : ∑ k, (x + y) k • F.affineRoot k = ∑ k, (0 : Option ι → ℤ) k • F.affineRoot k := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, hxv, hyv, add_neg_cancel,
      Pi.zero_apply, zero_smul, Finset.sum_const_zero]
  have hxy := F.sum_smul_affineRoot_injective h0
  have hx0 : x = 0 := funext fun k => by
    have h1 := congrFun hxy k
    have := hx k
    have := hy k
    simp only [Pi.add_apply, Pi.zero_apply] at h1 ⊢
    linarith
  exact hr.ne_zero (by rw [← hxv, hx0]; simp)

/-- **Reflections in roots preserve roots.** -/
theorem isRoot_reflect (hb : ∀ x y, b x y = b y x) {s v : MukaiLattice ℤ N} (hs : F.IsRoot s)
    (hv : F.IsRoot v) : F.IsRoot (reflect b s v) := by
  have hsph : IsSpherical b s := hs.mukaiForm_self
  have h1 : (reflect b s v).1 = 0 := by simp [reflect_apply, hs.1, hv.1]
  refine ⟨h1, ?_, ?_⟩
  · simp only [reflect_apply, Prod.snd_add, Prod.smul_snd, Prod.fst_add, Prod.smul_fst]
    exact add_mem hv.2.1 (F.rootLattice.smul_mem _ hs.2.1)
  · rw [← mukaiForm_self_of_fst_eq_zero h1, mukaiForm_apply,
      pairing_reflect_reflect b hb s hsph v v, ← mukaiForm_apply]
    exact hv.mukaiForm_self

theorem isRoot_reflect_iff (hb : ∀ x y, b x y = b y x) {s v : MukaiLattice ℤ N}
    (hs : F.IsRoot s) : F.IsRoot (reflect b s v) ↔ F.IsRoot v := by
  refine ⟨fun h => ?_, isRoot_reflect hb hs⟩
  have := isRoot_reflect hb hs h
  rwa [reflect_reflect b s hs.mukaiForm_self] at this

/-- `⊗𝒪(L)` preserves the roots: `(0, c, s) ↦ (0, c, s + c·L)`. -/
theorem isRoot_tensorLine_iff {L : N} {q : ℤ} {v : MukaiLattice ℤ N} :
    F.IsRoot (tensorLine b L q v) ↔ F.IsRoot v := by
  obtain ⟨r, c, s⟩ := v
  simp only [IsRoot, tensorLine_apply]
  constructor
  · rintro ⟨h1, h2, h3⟩
    subst h1
    simpa using And.intro h2 h3
  · rintro ⟨h1, h2, h3⟩
    subst h1
    simpa using And.intro h2 h3

/-! ### The simple reflections -/

/-- **The simple reflection** `sₖ = ρ_{αₖ}`. -/
def simpleReflection (F : FundamentalCycle b ι) (k : Option ι) : Aut(Λ) :=
  reflectEquiv b (F.affineRoot k) (F.isSpherical_affineRoot k)

theorem simpleReflection_apply (k : Option ι) (v : MukaiLattice ℤ N) :
    F.simpleReflection k v = reflect b (F.affineRoot k) v :=
  reflectEquiv_apply b _ _ v

theorem simpleReflection_mul_self (k : Option ι) :
    F.simpleReflection k * F.simpleReflection k = 1 :=
  LinearEquiv.ext fun v => by
    rw [mul_apply_eq_comp, simpleReflection_apply, simpleReflection_apply,
      reflect_reflect b _ (F.isSpherical_affineRoot k)]
    rfl

theorem simpleReflection_apply_corankUnit (k : Option ι) :
    F.simpleReflection k corankUnit = corankUnit := by
  rw [simpleReflection_apply]
  exact reflect_of_pairing_eq_zero b (by cases k <;> simp [corankUnit, pairing])

/-- The action of a word of simple reflections is the product of the simple reflections. -/
theorem prod_map_simpleReflection_apply (ω : List (Option ι)) (v : MukaiLattice ℤ N) :
    (ω.map F.simpleReflection).prod v =
      BilinearForm.reflectWord (mukaiForm b) F.affineRoot ω v := by
  induction ω with
  | nil => rfl
  | cons k ω ih =>
    rw [List.map_cons, List.prod_cons, mul_apply_eq_comp, ih,
      BilinearForm.reflectWord_cons_apply, simpleReflection_apply]
    rfl

/-- **The simple reflection `sₖ` maps the positive roots other than `αₖ` to positive roots.** -/
theorem IsPositiveRoot.reflect_affineRoot (hb : ∀ x y, b x y = b y x) {v : MukaiLattice ℤ N}
    (hv : F.IsPositiveRoot v) {k : Option ι} (hne : v ≠ F.affineRoot k) :
    F.IsPositiveRoot (reflect b (F.affineRoot k) v) := by
  classical
  have hroot : F.IsRoot (reflect b (F.affineRoot k) v) :=
    isRoot_reflect hb (F.isRoot_affineRoot k) hv.1
  have hvn := hv.1.mukaiForm_self
  obtain ⟨-, x, hx, hxv⟩ := hv
  set t := pairing b v (F.affineRoot k)
  have hcoord : ∑ l, (x + Pi.single k t : Option ι → ℤ) l • F.affineRoot l =
      reflect b (F.affineRoot k) v := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, hxv, reflect_apply]
    congr 1
    rw [Finset.sum_eq_single k (fun l _ hl => by simp [hl]) (by simp)]
    simp [t]
  rcases F.isPositiveRoot_or_neg hb hroot with h | h
  · exact h
  · exfalso
    obtain ⟨-, y, hy, hyv⟩ := h
    have h0 : ∑ l, (x + Pi.single k t + y : Option ι → ℤ) l • F.affineRoot l =
        ∑ l, (0 : Option ι → ℤ) l • F.affineRoot l := by
      have : ∑ l, (x + Pi.single k t + y : Option ι → ℤ) l • F.affineRoot l =
          ∑ l, (x + Pi.single k t : Option ι → ℤ) l • F.affineRoot l +
            ∑ l, y l • F.affineRoot l := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun l _ => by rw [Pi.add_apply, add_smul]
      rw [this, hcoord, hyv, add_neg_cancel]
      simp
    have hxy := F.sum_smul_affineRoot_injective h0
    have hxl : ∀ l, l ≠ k → x l = 0 := fun l hl => by
      have h1 := congrFun hxy l
      simp only [Pi.add_apply, Pi.single_apply, hl, ↓reduceIte, add_zero, Pi.zero_apply] at h1
      linarith [hx l, hy l]
    have hv' : v = x k • F.affineRoot k := by
      rw [← hxv, Finset.sum_eq_single k (fun l _ hl => by rw [hxl l hl, zero_smul]) (by simp)]
    have hk1 : x k * x k = 1 := by
      rw [hv'] at hvn
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, F.mukaiForm_affineRoot_self] at hvn
      linarith
    have : x k = 1 := by nlinarith [hx k]
    exact hne (by rw [hv', this, one_smul])

/-! ### Descent on the height -/

/-- **Every positive root is the image of an affine simple root under a word of simple
reflections.** If the coordinates of the root are supported on a set `K` of nodes, the word
uses only letters of `K` and the simple root is at a node of `K`. -/
theorem exists_reflectWord_affineRoot (hb : ∀ x y, b x y = b y x) (K : Set (Option ι)) :
    ∀ (n : ℕ) (v : MukaiLattice ℤ N) (x : Option ι → ℤ), F.IsRoot v → (∀ k, 0 ≤ x k) →
      (∀ k, k ∉ K → x k = 0) → ∑ k, x k • F.affineRoot k = v → ∑ k, x k = n →
      ∃ (ω : List (Option ι)) (k : Option ι), (∀ l ∈ ω, l ∈ K) ∧ k ∈ K ∧
        v = BilinearForm.reflectWord (mukaiForm b) F.affineRoot ω (F.affineRoot k) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v x hv hx hK hxv hn
    -- some coordinate `k` has `xₖ > 0` and `⟨v, αₖ⟩ < 0`, since `⟨v, v⟩ = -2`
    obtain ⟨k, -, hk⟩ : ∃ k ∈ Finset.univ, x k * mukaiForm b v (F.affineRoot k) < 0 := by
      by_contra! h
      have hsum : mukaiForm b v v = ∑ k, x k * mukaiForm b v (F.affineRoot k) :=
        calc mukaiForm b v v = mukaiForm b v (∑ k, x k • F.affineRoot k) := by rw [hxv]
          _ = ∑ k, x k * mukaiForm b v (F.affineRoot k) := by
            rw [map_sum]
            simp only [map_zsmul, smul_eq_mul]
      have := Finset.sum_nonneg h
      rw [← hsum, hv.mukaiForm_self] at this
      norm_num at this
    have hxk : 0 < x k := lt_of_le_of_ne (hx k) fun h => by
      rw [← h, zero_mul] at hk
      exact lt_irrefl _ hk
    have hpk : mukaiForm b v (F.affineRoot k) < 0 := by
      by_contra h
      exact absurd hk (not_lt.mpr (mul_nonneg (hx k) (not_lt.mp h)))
    have hkK : k ∈ K := by
      by_contra h
      exact hxk.ne' (hK k h)
    by_cases hvk : v = F.affineRoot k
    · exact ⟨[], k, by simp, hkK, by rw [hvk]; rfl⟩
    -- reflect and descend
    set t := mukaiForm b v (F.affineRoot k)
    have hcoord : ∑ l, (x + Pi.single k t : Option ι → ℤ) l • F.affineRoot l =
        reflect b (F.affineRoot k) v := by
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, hxv, reflect_apply]
      congr 1
      rw [Finset.sum_eq_single k (fun l _ hl => by simp [hl]) (by simp)]
      simp [t]
    have hpos := (show F.IsPositiveRoot v from ⟨hv, x, hx, hxv⟩).reflect_affineRoot hb hvk
    obtain ⟨-, y, hy, hyv⟩ := hpos
    have hyx : y = x + Pi.single k t := F.sum_smul_affineRoot_injective (hyv.trans hcoord.symm)
    have hsingle : ∑ l, (Pi.single k t : Option ι → ℤ) l = t := by
      rw [Finset.sum_eq_single k (fun l _ hl => by rw [Pi.single_eq_of_ne hl]) (by simp),
        Pi.single_eq_same]
    have hlt : ∑ l, y l < n := by
      rw [hyx]
      simp only [Pi.add_apply]
      rw [Finset.sum_add_distrib, hsingle, hn]
      linarith
    have hy0 : 0 ≤ ∑ l, y l := Finset.sum_nonneg fun l _ => hy l
    obtain ⟨ω, m, hω, hm, hv'⟩ := ih (∑ l, y l).toNat (by omega)
      (reflect b (F.affineRoot k) v) y (isRoot_reflect hb (F.isRoot_affineRoot k) hv) hy
      (fun l hl => by
        rw [hyx, Pi.add_apply, hK l hl, zero_add]
        rw [Pi.single_eq_of_ne (fun h : l = k => hl (h ▸ hkK))])
      hyv (by omega)
    refine ⟨k :: ω, m, fun l hl => ?_, hm, ?_⟩
    · rcases List.mem_cons.mp hl with rfl | hl
      · exact hkK
      · exact hω l hl
    · rw [BilinearForm.reflectWord_cons_apply, ← hv']
      exact (reflect_reflect b _ (F.isSpherical_affineRoot k) v).symm

/-- The closure of the simple reflections at a set of nodes contains the action of every word
in those nodes. -/
theorem prod_map_simpleReflection_mem_closure {K : Set (Option ι)} {ω : List (Option ι)}
    (hω : ∀ l ∈ ω, l ∈ K) :
    (ω.map F.simpleReflection).prod ∈ Subgroup.closure (F.simpleReflection '' K) := by
  induction ω with
  | nil => exact one_mem _
  | cons k ω ih =>
    rw [List.map_cons, List.prod_cons]
    exact mul_mem (Subgroup.subset_closure ⟨k, hω k List.mem_cons_self, rfl⟩)
      (ih fun l hl => hω l (List.mem_cons_of_mem _ hl))

/-- The simple reflections are isometries. -/
theorem closure_simpleReflection_le_orthogonalGroup (hb : ∀ x y, b x y = b y x)
    (K : Set (Option ι)) :
    Subgroup.closure (F.simpleReflection '' K) ≤ orthogonalGroup b := by
  rw [Subgroup.closure_le]
  rintro _ ⟨k, -, rfl⟩
  exact reflectEquiv_mem_orthogonalGroup hb _ _

/-- The reflection in a positive root with coordinates supported on `K` lies in the group
generated by the simple reflections at `K`: it is `g sₖ g⁻¹` for a word `g` with `g αₖ = v`. -/
theorem reflectEquiv_mem_closure (hb : ∀ x y, b x y = b y x) (K : Set (Option ι))
    {v : MukaiLattice ℤ N} {x : Option ι → ℤ} (hv : F.IsRoot v) (hsph : IsSpherical b v)
    (hx : ∀ k, 0 ≤ x k) (hK : ∀ k, k ∉ K → x k = 0) (hxv : ∑ k, x k • F.affineRoot k = v) :
    reflectEquiv b v hsph ∈ Subgroup.closure (F.simpleReflection '' K) := by
  obtain ⟨ω, k, hω, hk, hvk⟩ := F.exists_reflectWord_affineRoot hb K (∑ k, x k).toNat v x hv hx
    hK hxv (Int.toNat_of_nonneg (Finset.sum_nonneg fun k _ => hx k)).symm
  have hgmem := F.prod_map_simpleReflection_mem_closure hω
  set g := (ω.map F.simpleReflection).prod
  have hgO : g ∈ orthogonalGroup b := F.closure_simpleReflection_le_orthogonalGroup hb K hgmem
  have hgv : g (F.affineRoot k) = v := by rw [prod_map_simpleReflection_apply, hvk]
  have heq : reflectEquiv b v hsph = g * F.simpleReflection k * g⁻¹ := by
    refine LinearEquiv.ext fun w => ?_
    rw [mul_apply_eq_comp, mul_apply_eq_comp, LinearEquiv.coe_inv, reflectEquiv_apply,
      simpleReflection_apply, apply_reflect_symm hgO, hgv]
  rw [heq]
  exact mul_mem (mul_mem hgmem (Subgroup.subset_closure ⟨k, hk, rfl⟩)) (inv_mem hgmem)

/-- The reflection in the negative of a class is the reflection in the class. -/
theorem reflectEquiv_neg {v : MukaiLattice ℤ N} (h : IsSpherical b v) (h' : IsSpherical b (-v)) :
    reflectEquiv b (-v) h' = reflectEquiv b v h :=
  LinearEquiv.ext fun w => by
    rw [reflectEquiv_apply, reflectEquiv_apply, reflect_apply, reflect_apply, pairing_neg_right,
      neg_smul, smul_neg, neg_neg]

/-- The reflection in any root lies in the group generated by the simple reflections at `K`,
when the coordinates of the root are supported on `K`. -/
theorem reflectEquiv_root_mem_closure (hb : ∀ x y, b x y = b y x) (K : Set (Option ι))
    {v : MukaiLattice ℤ N} (hv : F.IsRoot v) (hsph : IsSpherical b v)
    (hK : ∀ x : Option ι → ℤ, ∑ k, x k • F.affineRoot k = v ∨ ∑ k, x k • F.affineRoot k = -v →
      ∀ k, k ∉ K → x k = 0) :
    reflectEquiv b v hsph ∈ Subgroup.closure (F.simpleReflection '' K) := by
  rcases F.isPositiveRoot_or_neg hb hv with ⟨-, x, hx, hxv⟩ | ⟨hv', x, hx, hxv⟩
  · exact F.reflectEquiv_mem_closure hb K hv hsph hx (hK x (Or.inl hxv)) hxv
  · have hsph' : IsSpherical b (-v) := hv'.mukaiForm_self
    rw [← reflectEquiv_neg hsph hsph']
    exact F.reflectEquiv_mem_closure hb K hv' hsph' hx (hK x (Or.inr hxv)) hxv

/-- The level of `Σ xₖ αₖ` is `x₀`. -/
theorem snd_snd_sum_smul_affineRoot (x : Option ι → ℤ) :
    (∑ k, x k • F.affineRoot k).2.2 = x none := by
  rw [sum_smul_affineRoot]

/-! ### The simple reflections generate -/

theorem simpleReflection_mem_affineReflections (k : Option ι) :
    F.simpleReflection k ∈ F.affineReflections := by
  cases k with
  | none => exact ⟨F.cycle, ⟨F.mult, rfl⟩, 1, F.isSpherical_affineRoot none, rfl⟩
  | some i =>
    exact ⟨-F.curve i, (F.isRoot_affineRoot (some i)).2.1, 0, F.isSpherical_affineRoot (some i),
      rfl⟩

/-- **The simple reflections generate the affine Weyl group.** -/
theorem affineWeyl_eq_closure (hb : ∀ x y, b x y = b y x) :
    F.affineWeyl = Subgroup.closure (F.simpleReflection '' Set.univ) := by
  refine le_antisymm ?_ ?_
  · rw [affineWeyl, Subgroup.closure_le]
    rintro g ⟨c, hcQ, s, hs, rfl⟩
    have hv : F.IsRoot ((0, c, s) : MukaiLattice ℤ N) :=
      ⟨rfl, hcQ, by simpa [IsSpherical] using hs⟩
    exact F.reflectEquiv_root_mem_closure hb Set.univ hv hs fun _ _ k hk => absurd trivial hk
  · rw [Subgroup.closure_le]
    rintro _ ⟨k, -, rfl⟩
    exact Subgroup.subset_closure (F.simpleReflection_mem_affineReflections k)

/-- **The simple reflections of the finite nodes generate the finite Weyl group.** -/
theorem finiteWeyl_eq_closure (hb : ∀ x y, b x y = b y x) :
    F.finiteWeyl = Subgroup.closure (F.simpleReflection '' Set.range some) := by
  refine le_antisymm ?_ ?_
  · rw [finiteWeyl, Subgroup.closure_le]
    rintro g ⟨c, hcQ, hs, rfl⟩
    have hv : F.IsRoot ((0, c, 0) : MukaiLattice ℤ N) :=
      ⟨rfl, hcQ, by simpa [IsSpherical] using hs⟩
    refine F.reflectEquiv_root_mem_closure hb _ hv hs fun x hx k hk => ?_
    cases k with
    | none =>
      rcases hx with hx | hx
      · simpa using (F.snd_snd_sum_smul_affineRoot x).symm.trans (congrArg (·.2.2) hx)
      · have := (F.snd_snd_sum_smul_affineRoot x).symm.trans (congrArg (·.2.2) hx)
        simpa using this
    | some i => exact absurd ⟨i, rfl⟩ hk
  · rw [Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact Subgroup.subset_closure
      ⟨-F.curve i, (F.isRoot_affineRoot (some i)).2.1, F.isSpherical_affineRoot (some i), rfl⟩

/-! ### The trivial stabilizer -/

/-- **An element of `W_aff` that keeps every affine simple root positive is the identity.** The
deletion argument, with the positive roots as the positive set. -/
theorem eq_one_of_mem_affineWeyl (hb : ∀ x y, b x y = b y x) {u : Aut(Λ)}
    (hu : u ∈ F.affineWeyl) (h : ∀ k, F.IsPositiveRoot (u (F.affineRoot k))) : u = 1 := by
  rw [F.affineWeyl_eq_closure hb, Set.image_univ] at hu
  obtain ⟨ω, hω⟩ := BilinearForm.exists_reflectWord_of_mem_closure (b := mukaiForm b)
    (α := F.affineRoot) F.mukaiForm_affineRoot_self hu
  have h1 := BilinearForm.reflectWord_eq_one_of_forall_mem {v | F.IsPositiveRoot v}
    (mukaiForm_comm b hb) F.mukaiForm_affineRoot_self
    (fun j v hv hne => IsPositiveRoot.reflect_affineRoot hb hv hne) F.isPositiveRoot_affineRoot
    (fun v hv => IsPositiveRoot.not_neg hv) ω (fun i => by rw [← hω]; exact h i)
  exact LinearEquiv.ext fun v => by rw [hω, h1]; rfl

/-- **`W_aff` meets the stabilizer of the affine simple roots only in `1`.** -/
theorem affineWeyl_inf_affineRootStabilizer (hb : ∀ x y, b x y = b y x) :
    F.affineWeyl ⊓ F.affineRootStabilizer = ⊥ := by
  rw [eq_bot_iff]
  rintro u ⟨hu, σ, hσ⟩
  rw [Subgroup.mem_bot]
  exact F.eq_one_of_mem_affineWeyl hb hu fun k => by rw [hσ]; exact F.isPositiveRoot_affineRoot _

/-! ### The finite Weyl group on coordinates -/

/-- `W(R)` preserves the rank and the last coordinate, and moves the middle one inside
`⊕ ℤCᵢ`. -/
theorem finiteWeyl_apply {w : Aut(Λ)} (hw : w ∈ F.finiteWeyl) (v : MukaiLattice ℤ N) :
    (w v).1 = v.1 ∧ (w v).2.2 = v.2.2 ∧ (w v).2.1 - v.2.1 ∈ F.rootLattice := by
  induction hw using Subgroup.closure_induction generalizing v with
  | mem x hx =>
    obtain ⟨c, hcQ, h, rfl⟩ := hx
    refine ⟨by simp [reflect_apply], by simp [reflect_apply], ?_⟩
    simpa [reflect_apply] using F.rootLattice.smul_mem _ hcQ
  | one => simp
  | mul x y _ _ hx hy =>
    obtain ⟨h1, h2, h3⟩ := hx (y v)
    obtain ⟨h1', h2', h3'⟩ := hy v
    refine ⟨by rw [mul_apply_eq_comp, h1, h1'], by rw [mul_apply_eq_comp, h2, h2'], ?_⟩
    rw [mul_apply_eq_comp, show (x (y v)).2.1 - v.2.1 = ((x (y v)).2.1 - (y v).2.1) +
      ((y v).2.1 - v.2.1) by abel]
    exact add_mem h3 h3'
  | inv x _ hx =>
    obtain ⟨h1, h2, h3⟩ := hx (x⁻¹ v)
    have e : x (x⁻¹ v) = v := by rw [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
    rw [e] at h1 h2 h3
    refine ⟨h1.symm, h2.symm, ?_⟩
    rw [show (x⁻¹ v).2.1 - v.2.1 = -(v.2.1 - (x⁻¹ v).2.1) by abel]
    exact neg_mem h3

theorem apply_fst_of_mem_finiteWeyl {w : Aut(Λ)} (hw : w ∈ F.finiteWeyl) (v : MukaiLattice ℤ N) :
    (w v).1 = v.1 :=
  (F.finiteWeyl_apply hw v).1

theorem apply_snd_snd_of_mem_finiteWeyl {w : Aut(Λ)} (hw : w ∈ F.finiteWeyl)
    (v : MukaiLattice ℤ N) : (w v).2.2 = v.2.2 :=
  (F.finiteWeyl_apply hw v).2.1

theorem apply_snd_fst_sub_mem_of_mem_finiteWeyl {w : Aut(Λ)} (hw : w ∈ F.finiteWeyl)
    (v : MukaiLattice ℤ N) : (w v).2.1 - v.2.1 ∈ F.rootLattice :=
  (F.finiteWeyl_apply hw v).2.2

/-- A root of positive level is positive. -/
theorem isPositiveRoot_of_snd_snd_pos (hb : ∀ x y, b x y = b y x) {v : MukaiLattice ℤ N}
    (hv : F.IsRoot v) (h : 0 < v.2.2) : F.IsPositiveRoot v := by
  rcases F.isPositiveRoot_or_neg hb hv with h' | ⟨-, y, hy, hyv⟩
  · exact h'
  · have := F.snd_snd_sum_smul_affineRoot y
    rw [hyv, Prod.snd_neg, Prod.snd_neg] at this
    have := hy none
    omega

/-! ### Preserving the roots -/

/-- The automorphisms that preserve the roots of the fibre and fix the class `δ` of a point. -/
def rootPreserving : Subgroup Aut(Λ) where
  carrier := {g | (∀ v, F.IsRoot (g v) ↔ F.IsRoot v) ∧ g corankUnit = corankUnit}
  one_mem' := ⟨fun _ => Iff.rfl, rfl⟩
  mul_mem' := fun {g h} hg hh =>
    ⟨fun v => by rw [mul_apply_eq_comp]; exact (hg.1 _).trans (hh.1 v), by
      rw [mul_apply_eq_comp, hh.2, hg.2]⟩
  inv_mem' := fun {g} hg =>
    ⟨fun v => by
      rw [← hg.1 (g⁻¹ v), LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply], by
      rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_eq, hg.2]⟩

theorem affineWeyl_le_rootPreserving (hb : ∀ x y, b x y = b y x) :
    F.affineWeyl ≤ F.rootPreserving := by
  rw [affineWeyl, Subgroup.closure_le]
  rintro g ⟨c, hcQ, s, hs, rfl⟩
  have hv : F.IsRoot ((0, c, s) : MukaiLattice ℤ N) := ⟨rfl, hcQ, by simpa [IsSpherical] using hs⟩
  refine ⟨fun v => ?_, ?_⟩
  · rw [reflectEquiv_apply]
    exact isRoot_reflect_iff hb hv
  · rw [reflectEquiv_apply]
    exact reflect_of_pairing_eq_zero b (by simp [corankUnit, pairing])

theorem lineTwists_le_rootPreserving : lineTwists b ≤ F.rootPreserving := by
  rw [lineTwists, Subgroup.closure_le]
  rintro g ⟨L, q, -, hg⟩
  exact ⟨fun v => by rw [hg]; exact isRoot_tensorLine_iff, by rw [hg]; simp [corankUnit]⟩

/-- **The extended affine Weyl group preserves the roots and fixes `δ`.** -/
theorem extendedAffineWeyl_le_rootPreserving (hb : ∀ x y, b x y = b y x) :
    F.extendedAffineWeyl ≤ F.rootPreserving :=
  sup_le (F.affineWeyl_le_rootPreserving hb) F.lineTwists_le_rootPreserving

/-! ### Simple roots to positive roots -/

/-- An automorphism preserving the roots that maps every affine simple root to a positive root
maps every positive root to a positive root. -/
theorem isPositiveRoot_apply_of_forall {g : Aut(Λ)} (hg : g ∈ F.rootPreserving)
    (h : ∀ k, F.IsPositiveRoot (g (F.affineRoot k))) {v : MukaiLattice ℤ N}
    (hv : F.IsPositiveRoot v) : F.IsPositiveRoot (g v) := by
  refine ⟨(hg.1 v).mpr hv.1, ?_⟩
  obtain ⟨-, x, hx, rfl⟩ := hv
  choose y hy hyv using fun k => (h k).2
  refine ⟨fun l => ∑ k, x k * y k l,
    fun l => Finset.sum_nonneg fun k _ => mul_nonneg (hx k) (hy k l), ?_⟩
  rw [map_sum]
  simp only [map_zsmul, ← hyv, Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

/-- An automorphism preserving the roots that maps every affine simple root to a positive root
maps each affine simple root to an affine simple root. -/
theorem exists_eq_affineRoot_of_forall (hb : ∀ x y, b x y = b y x) {g : Aut(Λ)}
    (hg : g ∈ F.rootPreserving) (h : ∀ k, F.IsPositiveRoot (g (F.affineRoot k)))
    (k : Option ι) : ∃ l, g (F.affineRoot k) = F.affineRoot l := by
  classical
  -- `g⁻¹` maps positive roots to positive roots
  have hinv : ∀ v, F.IsPositiveRoot v → F.IsPositiveRoot (g.symm v) := by
    intro v hv
    have hroot : F.IsRoot (g.symm v) := by
      rw [← hg.1, LinearEquiv.apply_symm_apply]
      exact hv.1
    rcases F.isPositiveRoot_or_neg hb hroot with h' | h'
    · exact h'
    · exfalso
      have := F.isPositiveRoot_apply_of_forall hg h h'
      rw [map_neg, LinearEquiv.apply_symm_apply] at this
      exact hv.not_neg this
  obtain ⟨-, y, hy, hyv⟩ := h k
  choose w hw hwv using fun l => (hinv _ (F.isPositiveRoot_affineRoot l)).2
  -- `αₖ = Σₗ yₗ g⁻¹ αₗ`, so `Σₗ yₗ wₗ = eₖ`
  have hsum : ∀ m, ∑ l, y l * w l m = (Pi.single k 1 : Option ι → ℤ) m := by
    have hR : ∑ m, (Pi.single k 1 : Option ι → ℤ) m • F.affineRoot m = F.affineRoot k := by
      rw [Finset.sum_eq_single k (fun m _ hm => by rw [Pi.single_eq_of_ne hm, zero_smul])
        (by simp), Pi.single_eq_same, one_smul]
    have hL : ∑ m, (∑ l, y l * w l m) • F.affineRoot m = F.affineRoot k :=
      calc ∑ m, (∑ l, y l * w l m) • F.affineRoot m
          = ∑ l, y l • ∑ m, w l m • F.affineRoot m := by
            simp only [Finset.sum_smul, Finset.smul_sum, smul_smul]
            exact Finset.sum_comm
        _ = ∑ l, y l • g.symm (F.affineRoot l) := by simp only [hwv]
        _ = g.symm (∑ l, y l • F.affineRoot l) := by simp only [map_sum, map_zsmul]
        _ = F.affineRoot k := by rw [hyv, LinearEquiv.symm_apply_apply]
    exact fun m => congrFun (F.sum_smul_affineRoot_injective (hL.trans hR.symm)) m
  -- some `yₗ ≠ 0`
  obtain ⟨l, hl⟩ : ∃ l, y l ≠ 0 := by
    by_contra! h0
    have : g (F.affineRoot k) = g 0 := by rw [← hyv, map_zero]; simp [h0]
    exact (F.isRoot_affineRoot k).ne_zero (g.injective this)
  have hyl : 1 ≤ y l := by have := hy l; omega
  -- every term is nonnegative, so `yₗ wₗ ≤ eₖ`
  have hle : ∀ m, y l * w l m ≤ (Pi.single k 1 : Option ι → ℤ) m := fun m => by
    rw [← hsum m]
    exact Finset.single_le_sum (f := fun l => y l * w l m)
      (fun l' _ => mul_nonneg (hy l') (hw l' m)) (Finset.mem_univ l)
  have hw0 : ∀ m, m ≠ k → w l m = 0 := fun m hm => by
    have h1 := hle m
    rw [Pi.single_eq_of_ne hm] at h1
    have := hw l m
    nlinarith
  have hwk : w l k = 1 := by
    have h1 := hle k
    rw [Pi.single_eq_same] at h1
    have hne : w l k ≠ 0 := by
      intro h0
      have : g.symm (F.affineRoot l) = g.symm 0 := by
        rw [← hwv l, map_zero]
        refine Finset.sum_eq_zero fun m _ => ?_
        by_cases hm : m = k
        · rw [hm, h0, zero_smul]
        · rw [hw0 m hm, zero_smul]
      exact (F.isRoot_affineRoot l).ne_zero (g.symm.injective this)
    have := hw l k
    rcases lt_or_gt_of_ne hne with h2 | h2 <;> nlinarith
  refine ⟨l, ?_⟩
  have : g.symm (F.affineRoot l) = F.affineRoot k := by
    rw [← hwv l, Finset.sum_eq_single k (fun m _ hm => by rw [hw0 m hm, zero_smul]) (by simp),
      hwk, one_smul]
  rw [← this, LinearEquiv.apply_symm_apply]

/-- **An automorphism preserving the roots that maps every affine simple root to a positive root
permutes the affine simple roots.** -/
theorem mem_affineRootStabilizer_of_forall (hb : ∀ x y, b x y = b y x) {g : Aut(Λ)}
    (hg : g ∈ F.rootPreserving) (h : ∀ k, F.IsPositiveRoot (g (F.affineRoot k))) :
    g ∈ F.affineRootStabilizer := by
  classical
  choose σ hσ using F.exists_eq_affineRoot_of_forall hb hg h
  have hinj : Function.Injective σ := fun k k' hkk' =>
    F.affineRoot_injective (g.injective (by rw [hσ, hσ, hkk']))
  exact ⟨Equiv.ofBijective σ (Finite.injective_iff_bijective.mp hinj), fun k => hσ k⟩

/-- **An element of `W(R)` that keeps every finite simple root positive is the identity**: the
image of `α₀ = (0, Θ, 1)` has level one, so it is positive too. -/
theorem eq_one_of_mem_finiteWeyl (hb : ∀ x y, b x y = b y x) {w : Aut(Λ)}
    (hw : w ∈ F.finiteWeyl) (h : ∀ i, F.IsPositiveRoot (w (F.affineRoot (some i)))) : w = 1 := by
  refine F.eq_one_of_mem_affineWeyl hb (F.finiteWeyl_le_affineWeyl hw) fun k => ?_
  cases k with
  | some i => exact h i
  | none =>
    have hroot : F.IsRoot (w (F.affineRoot none)) :=
      ((F.affineWeyl_le_rootPreserving hb (F.finiteWeyl_le_affineWeyl hw)).1 _).mpr
        (F.isRoot_affineRoot none)
    refine F.isPositiveRoot_of_snd_snd_pos hb hroot ?_
    rw [F.apply_snd_snd_of_mem_finiteWeyl hw]
    simp

end FundamentalCycle

end Mukai
