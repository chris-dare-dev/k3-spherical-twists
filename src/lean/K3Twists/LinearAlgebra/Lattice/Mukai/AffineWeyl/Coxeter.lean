/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.Lattice.Mukai.AffineWeyl.SimpleReflection

/-!
# The Weyl groups of a fibre as Coxeter groups, and the sign of the class at the stratum

At an ADE contraction, the spherical objects `Sᵢ = 𝒪_{Cᵢ}(-1)[1]` of one connected exceptional
fibre have classes `αᵢ = (0, -Cᵢ, 0)`, and with `S₀ = 𝒪_Θ` the affine simple roots `α₀, …, α_l`
(`Mukai.FundamentalCycle.affineRoot`). This file instantiates, on these classes, the class-level
inputs of the Weyl-gallery theorems of `CategoryTheory.Triangulated.WeylGalleryHypotheses`
(`StabilityCondition/WeylTilt.lean`), for every fibre at once:

* **The Coxeter matrices.** The pairings `⟨αₖ, αₗ⟩`, `k ≠ l`, are natural numbers
  (`FundamentalCycle.affineExt`): the extended Dynkin matrix is a Z-matrix. So the Gram matrix of
  the affine simple roots is `rootMatrix affineExt` (`mukaiForm_affineRoot_eq_rootMatrix`), the
  Mukai-sign Seidel–Thomas matrix of the configuration, and the reflections `ρ_{αₖ}` give the
  reflection representation of the Coxeter group `W(ofExt affineExt)`
  (`FundamentalCycle.affineWeylRep`), **whose image is the affine Weyl group `W_aff`**
  (`range_affineWeylRep`). On the finite nodes (`finiteExt`, `finiteWeylRep`) the image is
  `W(R)` (`range_finiteWeylRep`). The classes are linearly independent
  (`linearIndependent_affineRoot`, `linearIndependent_finiteRoot`).
* **The sign of the class at the stratum.** For `Z(r, c, s) = β·c - s` (`fibreCharge`), the
  classes with `Z < 0` form a cone with no pair `v, -v` (`FundamentalCycle.chargeCone`). In the
  fundamental alcove (`IsInFundamentalAlcove`: `β·Cᵢ > 0`, `β·Θ < 1`) the positive cone of the
  affine simple roots lies in it, and **a word is root-positive exactly when `Z < 0` on each of
  its prefix roots** (`isRootPositive_affineRoot_iff`): the prefix roots are roots of the fibre,
  which by sign coherence are positive or negative, and the alcove makes `Z` negative on the
  positive ones. At the stratum `β = 0` of all the finite walls, the fundamental Weyl chamber
  `β·Cᵢ > 0` does the same for words in the finite nodes (`isRootPositive_finiteRoot_iff`).
* **Explicit words are computed on `ℤ^l`.** Root-positivity for the finite nodes is
  root-positivity for `rootForm finiteExt` on `ℤ^l` (`isRootPositive_finiteRoot_iff_rootForm`),
  so the computations of `GroupTheory/Coxeter/GeometricRepresentation.lean` apply; for a chain
  of curves (`finiteExt = extA n`) the longest word `longestWordA n` is root-positive and sends
  `αᵢ` to `-α_{n-1-i}` for `n ≤ 6` (`isRootPositive_longestWordA`,
  `reflectWord_longestWordA`).

With the categorical fields of `WeylGalleryHypotheses` (the twist functors and the tilts, which
have no geometric instance), the root-positive words here are the words for which the gallery
theorems apply: `F_ω Sᵢ` has class `ω(αᵢ)`, and the sign of the class places it in the heart.
That a stability condition with this charge has the heart in which the `Sᵢ` are simple is
geometry and is not formalized.

## References

* P. Seidel and R. Thomas, *Braid group actions on derived categories of coherent sheaves*,
  arXiv:math/0001043, §2.
* J. E. Humphreys, *Reflection groups and Coxeter groups*, §4.6, §5.4.
* V. G. Kac, *Infinite dimensional Lie algebras*, §3.7, §5.1.
-/

namespace BilinearForm

variable {B Λ : Type*} [AddCommGroup Λ] {α : B → Λ}

/-- A nonempty sum of the `α i` is a combination with natural coefficients, not all zero. -/
theorem exists_nat_of_mem_positiveCone [Fintype B] [DecidableEq B] {v : Λ}
    (hv : v ∈ positiveCone α) : ∃ n : B → ℕ, n ≠ 0 ∧ v = ∑ i, (n i : ℤ) • α i := by
  induction hv using AddSubsemigroup.closure_induction with
  | mem v hv =>
    obtain ⟨i, rfl⟩ := hv
    refine ⟨Pi.single i 1, fun h => by simpa using congrFun h i, ?_⟩
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
    simp
  | add v w _ _ hv hw =>
    obtain ⟨n, hn, rfl⟩ := hv
    obtain ⟨n', -, rfl⟩ := hw
    refine ⟨n + n', fun h => hn (funext fun i => ?_), ?_⟩
    · have := congrFun h i
      simp only [Pi.add_apply, Pi.zero_apply] at this
      simp only [Pi.zero_apply]
      omega
    · rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by simp only [Pi.add_apply, Nat.cast_add, add_smul]

/-- A combination of the `α i` with nonnegative coefficients, not all zero, lies in the positive
cone. -/
theorem sum_smul_mem_positiveCone [Fintype B] [DecidableEq B] {n : B → ℤ} (h0 : ∀ i, 0 ≤ n i)
    (hn : n ≠ 0) : ∑ i, n i • α i ∈ positiveCone α := by
  have := map_mem_positiveCone (CoxeterMatrix.rootMap α) CoxeterMatrix.rootMap_stdRoot
    (CoxeterMatrix.mem_positiveCone_stdRoot h0 hn)
  simpa [Fintype.linearCombination_apply] using this

end BilinearForm

namespace Mukai

variable {N : Type*} [AddCommGroup N]

/-- Automorphisms of the Mukai lattice. -/
local notation "Aut(Λ)" => MukaiLattice ℤ N ≃ₗ[ℤ] MukaiLattice ℤ N

namespace FundamentalCycle

open BilinearForm CoxeterMatrix

variable {b : N →ₗ[ℤ] N →ₗ[ℤ] ℤ} {ι : Type*} [Fintype ι] (F : FundamentalCycle b ι)

/-- The classes `αᵢ = (0, -Cᵢ, 0)` of the finite nodes. -/
def finiteRoot (i : ι) : MukaiLattice ℤ N :=
  F.affineRoot (some i)

/-- The pairing of two distinct affine simple roots is nonnegative: the extended Dynkin matrix
is a Z-matrix. -/
theorem mukaiForm_affineRoot_nonneg (hb : ∀ x y, b x y = b y x) {k l : Option ι} (h : k ≠ l) :
    0 ≤ mukaiForm b (F.affineRoot k) (F.affineRoot l) := by
  have := F.affineCartan_isZMatrix hb k l h
  simp only [affineCartan, LinearMap.BilinForm.wallMatrix_apply] at this
  linarith

/-- **The affine simple roots are linearly independent.** -/
theorem linearIndependent_affineRoot : LinearIndependent ℤ F.affineRoot := by
  refine Fintype.linearIndependent_iff.2 fun g hg k => ?_
  have := F.sum_smul_affineRoot_injective (hg.trans (by simp : (0 : MukaiLattice ℤ N) =
    ∑ k, (0 : Option ι → ℤ) k • F.affineRoot k))
  exact congrFun this k

/-- **The finite simple roots are linearly independent.** -/
theorem linearIndependent_finiteRoot : LinearIndependent ℤ F.finiteRoot :=
  F.linearIndependent_affineRoot.comp some (Option.some_injective ι)

/-! ### The charge cone -/

omit [Fintype ι] in
theorem fibreCharge_add (β : N →+ ℝ) (v w : MukaiLattice ℤ N) :
    fibreCharge β (v + w) = fibreCharge β v + fibreCharge β w := by
  simp only [fibreCharge, Prod.snd_add, Prod.fst_add, map_add, Int.cast_add]
  ring

omit [Fintype ι] in
/-- **The cone of classes with negative charge** `Z = β·c - s`. -/
def chargeCone (β : N →+ ℝ) : AddSubsemigroup (MukaiLattice ℤ N) where
  carrier := {v | fibreCharge β v < 0}
  add_mem' {v w} hv hw := by
    show fibreCharge β (v + w) < 0
    rw [fibreCharge_add]
    exact add_neg hv hw

omit [Fintype ι] in
theorem mem_chargeCone {β : N →+ ℝ} {v : MukaiLattice ℤ N} :
    v ∈ chargeCone β ↔ fibreCharge β v < 0 :=
  Iff.rfl

omit [Fintype ι] in
/-- **The charge cone contains no pair `v, -v`.** -/
theorem neg_notMem_chargeCone {β : N →+ ℝ} {v : MukaiLattice ℤ N} (hv : v ∈ chargeCone β) :
    -v ∉ chargeCone β := by
  rw [mem_chargeCone, fibreCharge_neg] at *
  linarith

/-- In the fundamental alcove the positive cone of the affine simple roots lies in the charge
cone. -/
theorem positiveCone_affineRoot_le_chargeCone {β : N →+ ℝ} (hβ : F.IsInFundamentalAlcove β) :
    positiveCone F.affineRoot ≤ chargeCone β :=
  AddSubsemigroup.closure_le.2 (Set.range_subset_iff.2
    ((F.isInFundamentalAlcove_iff_affineRoot β).mp hβ))

/-- In the fundamental Weyl chamber the positive cone of the finite simple roots lies in the
charge cone. -/
theorem positiveCone_finiteRoot_le_chargeCone {β : N →+ ℝ} (hβ : ∀ i, 0 < β (F.curve i)) :
    positiveCone F.finiteRoot ≤ chargeCone β :=
  AddSubsemigroup.closure_le.2 (Set.range_subset_iff.2 fun i => by
    show fibreCharge β (F.affineRoot (some i)) < 0
    rw [fibreCharge_affineRoot_some]
    linarith [hβ i])

/-! ### The sign of the class at the stratum -/

/-- The prefix roots of a word in the affine simple reflections are roots of the fibre. -/
theorem isRoot_of_mem_prefixRoots (hb : ∀ x y, b x y = b y x) {ω : List (Option ι)}
    {v : MukaiLattice ℤ N} (hv : v ∈ prefixRoots (mukaiForm b) F.affineRoot ω) : F.IsRoot v := by
  induction ω generalizing v with
  | nil => simp at hv
  | cons k ω ih =>
    rw [prefixRoots_cons, List.mem_cons, List.mem_map] at hv
    rcases hv with rfl | ⟨u, hu, rfl⟩
    · exact F.isRoot_affineRoot k
    · exact isRoot_reflect hb (F.isRoot_affineRoot k) (ih hu)

/-- The prefix roots of a word in the finite simple reflections are roots of the fibre at level
zero. -/
theorem isRoot_of_mem_prefixRoots_finite (hb : ∀ x y, b x y = b y x) {ω : List ι}
    {v : MukaiLattice ℤ N} (hv : v ∈ prefixRoots (mukaiForm b) F.finiteRoot ω) :
    F.IsRoot v ∧ v.2.2 = 0 := by
  induction ω generalizing v with
  | nil => simp at hv
  | cons i ω ih =>
    rw [prefixRoots_cons, List.mem_cons, List.mem_map] at hv
    rcases hv with rfl | ⟨u, hu, rfl⟩
    · exact ⟨F.isRoot_affineRoot (some i), rfl⟩
    · obtain ⟨hu1, hu2⟩ := ih hu
      exact ⟨isRoot_reflect hb (F.isRoot_affineRoot (some i)) hu1, by
        simp [BilinearForm.reflect_apply, hu2, finiteRoot]⟩

/-- A root with negative charge in the fundamental alcove is positive. -/
theorem isPositiveRoot_of_fibreCharge_neg (hb : ∀ x y, b x y = b y x) {β : N →+ ℝ}
    (hβ : F.IsInFundamentalAlcove β) {v : MukaiLattice ℤ N} (hv : F.IsRoot v)
    (hZ : fibreCharge β v < 0) : F.IsPositiveRoot v := by
  rcases F.isPositiveRoot_or_neg hb hv with h | h
  · exact h
  · have := (F.isInFundamentalAlcove_iff β).mp hβ _ h
    rw [fibreCharge_neg] at this
    linarith

/-- **The sign of the class in the fundamental alcove.** For `β` in the fundamental alcove, a
word in the affine simple reflections is root-positive iff the charge `Z = β·c - s` is negative
on each of its prefix roots. -/
theorem isRootPositive_affineRoot_iff (hb : ∀ x y, b x y = b y x) {β : N →+ ℝ}
    (hβ : F.IsInFundamentalAlcove β) (ω : List (Option ι)) :
    IsRootPositive (mukaiForm b) F.affineRoot ω ↔
      ∀ v ∈ prefixRoots (mukaiForm b) F.affineRoot ω, fibreCharge β v < 0 := by
  classical
  refine ⟨fun h v hv => F.positiveCone_affineRoot_le_chargeCone hβ (h v hv), fun h v hv => ?_⟩
  obtain ⟨-, x, hx, hxv⟩ :=
    F.isPositiveRoot_of_fibreCharge_neg hb hβ (F.isRoot_of_mem_prefixRoots hb hv) (h v hv)
  rw [← hxv]
  refine sum_smul_mem_positiveCone hx fun hx0 => ?_
  have := (F.isRoot_of_mem_prefixRoots hb hv).ne_zero
  rw [← hxv, hx0] at this
  simp at this

/-- **The sign of the class at the stratum `β = 0`.** For `β` in the fundamental Weyl chamber
(`β·Cᵢ > 0`), a word in the finite simple reflections is root-positive iff the charge is
negative on each of its prefix roots. -/
theorem isRootPositive_finiteRoot_iff (hb : ∀ x y, b x y = b y x) {β : N →+ ℝ}
    (hβ : ∀ i, 0 < β (F.curve i)) (ω : List ι) :
    IsRootPositive (mukaiForm b) F.finiteRoot ω ↔
      ∀ v ∈ prefixRoots (mukaiForm b) F.finiteRoot ω, fibreCharge β v < 0 := by
  classical
  refine ⟨fun h v hv => F.positiveCone_finiteRoot_le_chargeCone hβ (h v hv), fun h v hv => ?_⟩
  obtain ⟨hroot, hlev⟩ := F.isRoot_of_mem_prefixRoots_finite hb hv
  rcases F.isPositiveRoot_or_neg hb hroot with ⟨-, x, hx, hxv⟩ | ⟨-, x, hx, hxv⟩
  · -- the coordinate at `α₀` is the level, zero
    have h0 : x none = 0 := by
      rw [← F.snd_snd_sum_smul_affineRoot x, hxv, hlev]
    rw [← hxv, Fintype.sum_option, h0, zero_smul, zero_add]
    refine sum_smul_mem_positiveCone (fun i => hx (some i)) fun hx0 => ?_
    have := hroot.ne_zero
    rw [← hxv, Fintype.sum_option, h0, zero_smul, zero_add] at this
    exact this (by simp [show ∀ i, x (some i) = 0 from fun i => congrFun hx0 i])
  · -- a negative root has positive charge
    exfalso
    have h0 : x none = 0 := by
      rw [← F.snd_snd_sum_smul_affineRoot x, hxv, Prod.snd_neg, Prod.snd_neg, hlev, neg_zero]
    have hneg : fibreCharge β (-v) < 0 := by
      rw [← hxv, fibreCharge_sum_smul_affineRoot, Fintype.sum_option, h0, Int.cast_zero,
        zero_mul, zero_add]
      obtain ⟨i, hi⟩ : ∃ i, x (some i) ≠ 0 := by
        by_contra! hx0
        have := hroot.ne_zero
        rw [← neg_neg v, ← hxv, Fintype.sum_option, h0, zero_smul, zero_add] at this
        exact this (by simp [hx0])
      have hterm : ∀ j, (x (some j) : ℝ) * fibreCharge β (F.affineRoot (some j)) ≤ 0 :=
        fun j => mul_nonpos_of_nonneg_of_nonpos (by exact_mod_cast hx (some j))
          (by rw [fibreCharge_affineRoot_some]; linarith [hβ j])
      have hi' : (x (some i) : ℝ) * fibreCharge β (F.affineRoot (some i)) < 0 :=
        mul_neg_of_pos_of_neg (by exact_mod_cast lt_of_le_of_ne (hx (some i)) (Ne.symm hi))
          (by rw [fibreCharge_affineRoot_some]; linarith [hβ i])
      have h1 := Finset.single_le_sum
        (f := fun j => -((x (some j) : ℝ) * fibreCharge β (F.affineRoot (some j))))
        (fun j _ => neg_nonneg.mpr (hterm j)) (Finset.mem_univ i)
      simp only [Finset.sum_neg_distrib] at h1
      linarith
    have := h v hv
    rw [fibreCharge_neg] at hneg
    linarith

/-! ### The Coxeter matrices -/

variable [DecidableEq ι]

/-- **The total Ext numbers of the affine simple roots**: `⟨αₖ, αₗ⟩` for `k ≠ l`, as natural
numbers, and `0` on the diagonal. -/
def affineExt (k l : Option ι) : ℕ :=
  if k = l then 0 else (mukaiForm b (F.affineRoot k) (F.affineRoot l)).toNat

/-- The total Ext numbers of the finite simple roots, `Cᵢ·Cⱼ` for `i ≠ j`. -/
def finiteExt (i j : ι) : ℕ :=
  F.affineExt (some i) (some j)

theorem affineExt_symm (hb : ∀ x y, b x y = b y x) (k l : Option ι) :
    F.affineExt k l = F.affineExt l k := by
  unfold affineExt
  by_cases h : k = l
  · subst h
    rfl
  · simp only [h, Ne.symm h, ↓reduceIte, mukaiForm_comm b hb (F.affineRoot k)]

theorem finiteExt_symm (hb : ∀ x y, b x y = b y x) (i j : ι) :
    F.finiteExt i j = F.finiteExt j i :=
  F.affineExt_symm hb _ _

theorem mukaiForm_affineRoot_of_ne (hb : ∀ x y, b x y = b y x) {k l : Option ι} (h : k ≠ l) :
    mukaiForm b (F.affineRoot k) (F.affineRoot l) = F.affineExt k l := by
  simp only [affineExt, h, ↓reduceIte]
  rw [Int.toNat_of_nonneg (F.mukaiForm_affineRoot_nonneg hb h)]

/-- **The Gram matrix of the affine simple roots is `rootMatrix affineExt`.** -/
theorem mukaiForm_affineRoot_eq_rootMatrix (hb : ∀ x y, b x y = b y x) (k l : Option ι) :
    mukaiForm b (F.affineRoot l) (F.affineRoot k) = rootMatrix F.affineExt l k := by
  by_cases h : l = k
  · subst h
    simp [rootMatrix, F.mukaiForm_affineRoot_self]
  · simp [rootMatrix, h, F.mukaiForm_affineRoot_of_ne hb h]

/-- **The Gram matrix of the finite simple roots is `rootMatrix finiteExt`.** -/
theorem mukaiForm_finiteRoot_eq_rootMatrix (hb : ∀ x y, b x y = b y x) (i j : ι) :
    mukaiForm b (F.finiteRoot j) (F.finiteRoot i) = rootMatrix F.finiteExt j i := by
  have := F.mukaiForm_affineRoot_eq_rootMatrix hb (some i) (some j)
  simpa [rootMatrix, finiteExt, finiteRoot] using this

/-- **The Coxeter matrix of the extended Dynkin diagram** of the fibre. -/
def affineCoxeterMatrix (hb : ∀ x y, b x y = b y x) : CoxeterMatrix (Option ι) :=
  ofExt F.affineExt (F.affineExt_symm hb)

/-- **The Coxeter matrix of the Dynkin diagram** of the fibre. -/
def finiteCoxeterMatrix (hb : ∀ x y, b x y = b y x) : CoxeterMatrix ι :=
  ofExt F.finiteExt (F.finiteExt_symm hb)

/-- **The reflection representation of the affine Weyl group** of the fibre on the Mukai lattice:
`sₖ ↦ ρ_{αₖ}`. -/
noncomputable def affineWeylRep (hb : ∀ x y, b x y = b y x) :
    (F.affineCoxeterMatrix hb).Group →* Aut(Λ) :=
  reflectionRep F.affineExt (F.affineExt_symm hb) (mukaiForm_comm b hb) F.mukaiForm_affineRoot_self
    fun _ _ h => F.mukaiForm_affineRoot_of_ne hb h

/-- **The reflection representation of the finite Weyl group** of the fibre: `sᵢ ↦ ρ_{αᵢ}`. -/
noncomputable def finiteWeylRep (hb : ∀ x y, b x y = b y x) :
    (F.finiteCoxeterMatrix hb).Group →* Aut(Λ) :=
  reflectionRep F.finiteExt (F.finiteExt_symm hb) (mukaiForm_comm b hb)
    (fun i => F.mukaiForm_affineRoot_self (some i))
    fun _ _ h => F.mukaiForm_affineRoot_of_ne hb fun h' => h (Option.some_injective ι h')

theorem affineWeylRep_simple (hb : ∀ x y, b x y = b y x) (k : Option ι) :
    F.affineWeylRep hb ((F.affineCoxeterMatrix hb).simple k) = F.simpleReflection k :=
  reflectionRep_simple _ _ _ _ _ k

theorem finiteWeylRep_simple (hb : ∀ x y, b x y = b y x) (i : ι) :
    F.finiteWeylRep hb ((F.finiteCoxeterMatrix hb).simple i) = F.simpleReflection (some i) :=
  reflectionRep_simple _ _ _ _ _ i

/-- **The image of the reflection representation is the affine Weyl group.** -/
theorem range_affineWeylRep (hb : ∀ x y, b x y = b y x) :
    (F.affineWeylRep hb).range = F.affineWeyl := by
  rw [MonoidHom.range_eq_map, ← (F.affineCoxeterMatrix hb).subgroupClosure_range_simple,
    MonoidHom.map_closure, F.affineWeyl_eq_closure hb, Set.image_univ, ← Set.range_comp]
  congr 2

/-- **The image of the finite reflection representation is `W(R)`.** -/
theorem range_finiteWeylRep (hb : ∀ x y, b x y = b y x) :
    (F.finiteWeylRep hb).range = F.finiteWeyl := by
  rw [MonoidHom.range_eq_map, ← (F.finiteCoxeterMatrix hb).subgroupClosure_range_simple,
    MonoidHom.map_closure, F.finiteWeyl_eq_closure hb, ← Set.range_comp, ← Set.range_comp]
  congr 2

/-! ### Explicit words on `ℤ^l` -/

/-- **Root-positivity for the finite nodes is the finite check on `ℤ^l`.** -/
theorem isRootPositive_finiteRoot_iff_rootForm (hb : ∀ x y, b x y = b y x) (ω : List ι) :
    IsRootPositive (mukaiForm b) F.finiteRoot ω ↔
      IsRootPositive (rootForm F.finiteExt) stdRoot ω := by
  refine ⟨fun h β hβ => ?_, fun h => h.of_rootForm _ (F.mukaiForm_finiteRoot_eq_rootMatrix hb)⟩
  have hmem : rootMap F.finiteRoot β ∈ prefixRoots (mukaiForm b) F.finiteRoot ω := by
    rw [prefixRoots_map (rootMap F.finiteRoot) rootMap_stdRoot
      (rootForm_rootMap F.finiteExt (F.mukaiForm_finiteRoot_eq_rootMatrix hb))]
    exact List.mem_map_of_mem hβ
  obtain ⟨n, hn, hnv⟩ := exists_nat_of_mem_positiveCone (h _ hmem)
  have hinj : Function.Injective (rootMap F.finiteRoot) :=
    LinearIndependent.fintypeLinearCombination_injective F.linearIndependent_finiteRoot
  have hβn : β = fun i => (n i : ℤ) := hinj (by rw [hnv]; simp [Fintype.linearCombination_apply])
  rw [hβn]
  exact mem_positiveCone_stdRoot (fun i => by positivity) fun h0 => hn (funext fun i => by
    have := congrFun h0 i
    simpa using this)

end FundamentalCycle

/-! ### Chains of curves -/

section Chain

open BilinearForm CoxeterMatrix

variable {b : N →ₗ[ℤ] N →ₗ[ℤ] ℤ}

/-- **The longest word on a chain of curves** (checked for `n ≤ 6`): if the curves of the fibre
form a chain, `finiteExt = extA n`, then `longestWordA n` is root-positive on the classes
`αᵢ = (0, -Cᵢ, 0)`. -/
theorem FundamentalCycle.isRootPositive_longestWordA (hb : ∀ x y, b x y = b y x) {n : ℕ}
    (F : FundamentalCycle b (Fin n)) (hext : F.finiteExt = extA n) (hn : n ≤ 6) :
    IsRootPositive (mukaiForm b) F.finiteRoot (longestWordA n) := by
  rw [F.isRootPositive_finiteRoot_iff_rootForm hb, hext]
  exact CoxeterMatrix.isRootPositive_longestWordA hn

/-- **On a chain of curves `w₀` sends `αᵢ` to `-α_{n-1-i}`** (checked for `n ≤ 6`). -/
theorem FundamentalCycle.reflectWord_longestWordA (hb : ∀ x y, b x y = b y x) {n : ℕ}
    (F : FundamentalCycle b (Fin n)) (hext : F.finiteExt = extA n) (hn : n ≤ 6) (i : Fin n) :
    reflectWord (mukaiForm b) F.finiteRoot (longestWordA n) (F.finiteRoot i) =
      -F.finiteRoot i.rev := by
  have hG : ∀ i j, mukaiForm b (F.finiteRoot j) (F.finiteRoot i) = rootMatrix (extA n) j i :=
    fun i j => by rw [F.mukaiForm_finiteRoot_eq_rootMatrix hb, hext]
  have h := reflectWord_of_rootForm (extA n) hG (longestWordA n) (stdRoot i)
  rw [rootMap_stdRoot, stdWord_longestWordA hn, map_neg, rootMap_stdRoot] at h
  exact h

end Chain

end Mukai
