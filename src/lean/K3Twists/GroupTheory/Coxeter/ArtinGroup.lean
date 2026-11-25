/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.GroupTheory.Coxeter.Basic

/-!
# The Artin group of a Coxeter matrix

Mathlib has the Coxeter group `M.Group` of a Coxeter matrix `M` and the braid words
`CoxeterSystem.braidWord M i i'`, but no Artin group. This file defines it, as a presented group
mirroring `CoxeterMatrix.Group`, and proves the facts the braid layer of the twist-word study
needs. Everything here uses Mathlib alone and holds for every Coxeter matrix.

## Main definitions

* `CoxeterMatrix.ArtinGroup M`: the group with generators `σ_i` and one braid relation
  `σ_i σ_{i'} σ_i ⋯ = σ_{i'} σ_i σ_{i'} ⋯` (`M i i'` letters on each side) for every pair. Mathlib
  encodes `m = ∞` as `M i i' = 0`, which gives the empty relation, as it should.
* `CoxeterMatrix.IsBraidLiftable M f`: values `f i` in a monoid satisfying the braid relations.
* `CoxeterMatrix.ArtinGroup.lift`: the universal property.
* `CoxeterMatrix.toCoxeterGroup`: the surjection `Art(M) → W(M)`, `σ_i ↦ s_i`.
* `CoxeterMatrix.pureArtinGroup`: its kernel.
* `CoxeterMatrix.ArtinGroup.reverse`: the anti-automorphism `σ_i ↦ σ_i`, which reads words
  backwards.
* `CoxeterMatrix.ofExt`: the simply-laced Coxeter matrix of a configuration of spherical objects
  with total Ext dimensions `e i j` (Seidel–Thomas, arXiv:math/0001043, §2):
  `m = 2, 3, ∞` for `e = 0, 1, ≥ 2`.

## Main results

* `CoxeterMatrix.pureArtinGroup_eq_normalClosure`: the pure Artin group is the normal closure
  of the squares `σ_i²`.
* `CoxeterMatrix.exists_factor_of_sq`, `CoxeterMatrix.pureArtinGroup_le_ker_of_sq`: a
  representation of `Art(M)` whose generators act by involutions factors through `W(M)` and
  kills the pure Artin group. So no such representation (the action of twists on a lattice by
  reflections, for one) separates elements of the pure Artin group.
* `CoxeterMatrix.braid_iff_conj`: in a group, the braid relation of length `m = M i i' ≥ 1` is the
  single conjugation identity `u f(i') u⁻¹ = f(c)`, where `u` is the product along the
  alternating word of length `m - 1` and `c` is `i` for odd `m` and `i'` for even `m`.
* `CoxeterMatrix.isBraidLiftable_of_equivariant`: if `G` acts on `X` and `τ : X → G` is
  conjugation-equivariant at points `x i` (`τ (g • x i) = g τ(x i) g⁻¹`), then the values
  `τ (x i)` satisfy the braid relations of `M` as soon as one object identity
  `u • x i' = x c` holds per edge. This is the frame of racks: twists of spherical objects up to
  shift, with `X ◃ Y = T_X Y`.

## Conventions

`alternatingWord i i' m` ends with `i'` (Mathlib's convention), and a word `[j₁, …, j_k]` is
evaluated as `f j₁ * ⋯ * f j_k`. Braid relations are closed under reversal
(`isBraidLiftable_op_iff`), so either composition order of autoequivalences gives the same
relations.
-/

open CoxeterSystem

namespace CoxeterMatrix

variable {B : Type*} (M : CoxeterMatrix B)

/-! ### The presentation -/

/-- A word, read in the free group. -/
def freeWord (ω : List B) : FreeGroup B := (ω.map FreeGroup.of).prod

/-- The braid relation `σ_i σ_{i'} σ_i ⋯ = σ_{i'} σ_i σ_{i'} ⋯`, `M i i'` letters on each side,
as the relator `braidWord M i i' * (braidWord M i' i)⁻¹`. For `M i i' = 0` (Mathlib's `∞`) both
words are empty and the relator is trivial. -/
def artinRelation (i i' : B) : FreeGroup B :=
  freeWord (braidWord M i i') * (freeWord (braidWord M i' i))⁻¹

/-- The set of braid relators. -/
def artinRelationsSet : Set (FreeGroup B) := Set.range (Function.uncurry M.artinRelation)

/-- **The Artin group** `Art(M)` of a Coxeter matrix: generators `σ_i` and the braid relations.
It mirrors `CoxeterMatrix.Group`, which adds the relations `σ_i² = 1`. -/
abbrev ArtinGroup : Type _ := PresentedGroup M.artinRelationsSet

/-- The standard generator `σ_i` of the Artin group. -/
abbrev artinGen (i : B) : M.ArtinGroup := PresentedGroup.of i

/-- Values `f i` in a monoid satisfying the braid relations of `M`. -/
def IsBraidLiftable {G : Type*} [Monoid G] (f : B → G) : Prop :=
  ∀ i i', ((braidWord M i i').map f).prod = ((braidWord M i' i).map f).prod

theorem lift_freeWord {G : Type*} [Group G] (f : B → G) (ω : List B) :
    FreeGroup.lift f (freeWord ω) = (ω.map f).prod := by
  induction ω with
  | nil => simp [freeWord]
  | cons i ω ih => simp [freeWord] at ih ⊢; exact ih

/-- A braid relation of a pair `i = i'`, or of a pair with `M i i' = 0`, holds for any values. -/
theorem isBraidLiftable_iff {G : Type*} [Monoid G] (f : B → G) :
    M.IsBraidLiftable f ↔ ∀ i i', i ≠ i' → M i i' ≠ 0 →
      ((braidWord M i i').map f).prod = ((braidWord M i' i).map f).prod := by
  refine ⟨fun h i i' _ _ => h i i', fun h i i' => ?_⟩
  by_cases hii : i = i'
  · subst hii; rfl
  by_cases hm : M i i' = 0
  · simp [braidWord, hm, M.symmetric i' i, alternatingWord]
  exact h i i' hii hm

namespace ArtinGroup

variable {M}

/-- **The universal property.** Braid-liftable values define a homomorphism out of `Art(M)`. -/
def lift {G : Type*} [Group G] (f : B → G) (hf : M.IsBraidLiftable f) : M.ArtinGroup →* G :=
  PresentedGroup.toGroup (rels := M.artinRelationsSet) (f := f) (by
    rintro _ ⟨⟨i, i'⟩, rfl⟩
    simp [artinRelation, lift_freeWord, hf i i'])

@[simp] theorem lift_of {G : Type*} [Group G] (f : B → G) (hf : M.IsBraidLiftable f) (i : B) :
    lift f hf (M.artinGen i) = f i :=
  PresentedGroup.toGroup.of _

theorem hom_ext {G : Type*} [Group G] {φ ψ : M.ArtinGroup →* G}
    (h : ∀ i, φ (M.artinGen i) = ψ (M.artinGen i)) : φ = ψ :=
  PresentedGroup.ext h

theorem mk_freeWord (ω : List B) :
    PresentedGroup.mk M.artinRelationsSet (freeWord ω) = (ω.map M.artinGen).prod := by
  induction ω with
  | nil => simp [freeWord]
  | cons i ω ih => simp [freeWord] at ih ⊢; rw [ih]; rfl

/-- The generators satisfy the braid relations. -/
theorem isBraidLiftable_artinGen : M.IsBraidLiftable M.artinGen := by
  intro i i'
  rw [← mk_freeWord, ← mk_freeWord]
  exact PresentedGroup.mk_eq_mk_of_mul_inv_mem ⟨⟨i, i'⟩, rfl⟩

/-- The converse of `lift`: the images of the generators under any homomorphism satisfy the
braid relations. -/
theorem isBraidLiftable_comp {G : Type*} [Group G] (φ : M.ArtinGroup →* G) :
    M.IsBraidLiftable (φ ∘ M.artinGen) := by
  intro i i'
  rw [← List.map_map, ← List.map_map, ← map_list_prod, ← map_list_prod,
    isBraidLiftable_artinGen i i']

/-- `lift` and `isBraidLiftable_comp` are inverse: every homomorphism is a lift. -/
theorem lift_comp {G : Type*} [Group G] (φ : M.ArtinGroup →* G) :
    lift (φ ∘ M.artinGen) (isBraidLiftable_comp φ) = φ :=
  hom_ext fun i => by simp

variable (M) in
/-- The element of `Art(M)` of a signed word: the letter `(i, true)` is `σ_i` and `(i, false)` is
`σ_i⁻¹`, as in `FreeGroup.mk`. Every element is of this form. -/
def ofSignedWord (L : List (B × Bool)) : M.ArtinGroup :=
  PresentedGroup.mk M.artinRelationsSet (FreeGroup.mk L)

theorem ofSignedWord_surjective : Function.Surjective (ofSignedWord M) := by
  intro g
  obtain ⟨x, rfl⟩ := PresentedGroup.mk_surjective _ g
  induction x using Quot.ind with
  | mk L => exact ⟨L, rfl⟩

/-- `lift` on a signed word: the product of the values and their inverses along the word. -/
theorem lift_ofSignedWord {G : Type*} [Group G] (f : B → G) (hf : M.IsBraidLiftable f)
    (L : List (B × Bool)) :
    lift f hf (ofSignedWord M L) = (L.map fun x => cond x.2 (f x.1) (f x.1)⁻¹).prod := by
  rw [← FreeGroup.lift_mk]
  have : (lift f hf).comp (PresentedGroup.mk M.artinRelationsSet) = FreeGroup.lift f :=
    FreeGroup.ext_hom _ _ fun i => by
      rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
      exact lift_of f hf i
  exact DFunLike.congr_fun this (FreeGroup.mk L)

end ArtinGroup

/-! ### The Coxeter quotient and the pure Artin group -/

/-- The surjection `Art(M) →* W(M)`, `σ_i ↦ s_i`. -/
def toCoxeterGroup : M.ArtinGroup →* M.Group :=
  ArtinGroup.lift M.simple (fun i i' => by
    simpa [wordProd] using M.toCoxeterSystem.wordProd_braidWord_eq i i')

@[simp] theorem toCoxeterGroup_of (i : B) : M.toCoxeterGroup (M.artinGen i) = M.simple i :=
  ArtinGroup.lift_of _ _ i

theorem toCoxeterGroup_surjective : Function.Surjective M.toCoxeterGroup := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← M.subgroupClosure_range_simple,
    Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨M.artinGen i, M.toCoxeterGroup_of i⟩

/-- **The pure Artin group**: the kernel of `Art(M) → W(M)`. -/
def pureArtinGroup : Subgroup M.ArtinGroup := M.toCoxeterGroup.ker

instance : M.pureArtinGroup.Normal := M.toCoxeterGroup.normal_ker

theorem mem_pureArtinGroup {g : M.ArtinGroup} :
    g ∈ M.pureArtinGroup ↔ M.toCoxeterGroup g = 1 :=
  MonoidHom.mem_ker

/-- In any monoid, the product along an alternating word. Mathlib's
`CoxeterSystem.prod_alternatingWord_eq_mul_pow` is the same identity inside a Coxeter group; this
one needs no involution. -/
theorem prod_map_alternatingWord {G : Type*} [Monoid G] (f : B → G) (i i' : B) (m : ℕ) :
    ((alternatingWord i i' m).map f).prod =
      (if Even m then 1 else f i') * (f i * f i') ^ (m / 2) := by
  induction m with
  | zero => simp [alternatingWord]
  | succ m ih =>
    rw [alternatingWord_succ', List.map_cons, List.prod_cons, ih]
    by_cases hm : Even m
    · have h₁ : ¬ Even (m + 1) := by simp [hm, parity_simps]
      have h₂ : (m + 1) / 2 = m / 2 := Nat.succ_div_of_not_dvd <| by rwa [← even_iff_two_dvd]
      simp [hm, h₁, h₂]
    · have h₁ : Even (m + 1) := by simp [hm, parity_simps]
      have h₂ : (m + 1) / 2 = m / 2 + 1 := Nat.succ_div_of_dvd h₁.two_dvd
      simp [hm, h₁, h₂, ← pow_succ', ← mul_assoc]

/-- Braid relations among involutions are the Coxeter relations `(f i f i')^{M i i'} = 1`. -/
theorem isLiftable_of_braid {G : Type*} [Group G] (f : B → G) (hf : M.IsBraidLiftable f)
    (hsq : ∀ i, f i * f i = 1) : M.IsLiftable f := by
  intro i i'
  have h := hf i i'
  rw [braidWord, braidWord, prod_map_alternatingWord, prod_map_alternatingWord,
    M.symmetric i' i] at h
  set a := f i
  set b := f i'
  have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq i)
  have hb : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq i')
  have hba : b * a = (a * b)⁻¹ := by rw [mul_inv_rev, ha, hb]
  rw [hba] at h
  set x := a * b with hx
  rcases Nat.even_or_odd' (M i i') with ⟨k, hk | hk⟩
  · rw [hk] at h ⊢
    have h2 : 2 * k / 2 = k := by omega
    simp only [even_two_mul, ite_true, one_mul, h2] at h
    rw [pow_mul', sq]
    nth_rewrite 1 [h]
    rw [inv_pow, inv_mul_cancel]
  · rw [hk] at h ⊢
    have h2 : (2 * k + 1) / 2 = k := by omega
    have hodd : ¬ Even (2 * k + 1) := by simp [parity_simps]
    simp only [hodd, ite_false, h2] at h
    -- `h : b * x ^ k = a * x⁻¹ ^ k`, so `x ^ (k + 1) = a * (b * x ^ k) = x⁻ᵏ`
    have h3 : x ^ (k + 1) = (x ^ k)⁻¹ := by
      rw [pow_succ', hx, mul_assoc, h, ← mul_assoc, hsq i, one_mul, inv_pow]
    rw [show 2 * k + 1 = (k + 1) + k by ring, pow_add, h3, inv_mul_cancel]

/-- **A representation with involutive generators factors through the Coxeter group.** If every
`φ σ_i` is an involution, `φ = ψ ∘ toCoxeterGroup` for a homomorphism `ψ` out of `W(M)`. -/
theorem exists_factor_of_sq {G : Type*} [Group G] (φ : M.ArtinGroup →* G)
    (hsq : ∀ i, φ (M.artinGen i) ^ 2 = 1) :
    ∃ ψ : M.Group →* G, ψ.comp M.toCoxeterGroup = φ := by
  have hφ : M.IsLiftable (φ ∘ M.artinGen) :=
    isLiftable_of_braid M _ (ArtinGroup.isBraidLiftable_comp φ)
      (fun i => by simpa [sq] using hsq i)
  refine ⟨M.toCoxeterSystem.lift ⟨_, hφ⟩, ArtinGroup.hom_ext fun i => ?_⟩
  simp only [MonoidHom.comp_apply, toCoxeterGroup_of]
  rw [← toCoxeterSystem_simple, CoxeterSystem.lift_apply_simple]
  rfl

/-- **A representation with involutive generators kills the pure Artin group.** -/
theorem pureArtinGroup_le_ker_of_sq {G : Type*} [Group G] (φ : M.ArtinGroup →* G)
    (hsq : ∀ i, φ (M.artinGen i) ^ 2 = 1) : M.pureArtinGroup ≤ φ.ker := by
  obtain ⟨ψ, hψ⟩ := M.exists_factor_of_sq φ hsq
  intro g hg
  rw [MonoidHom.mem_ker, ← hψ, MonoidHom.comp_apply, M.mem_pureArtinGroup.mp hg, map_one]

/-- Elementwise form of `pureArtinGroup_le_ker_of_sq`: two elements of `Art(M)` with the same image
in `W(M)` have the same image under every representation with involutive generators. -/
theorem pure_mem_ker_of_sq {G : Type*} [Group G] (φ : M.ArtinGroup →* G)
    (hsq : ∀ i, φ (M.artinGen i) ^ 2 = 1) {g : M.ArtinGroup} (hg : g ∈ M.pureArtinGroup) :
    φ g = 1 :=
  M.pureArtinGroup_le_ker_of_sq φ hsq hg

/-- **The pure Artin group is the normal closure of the squares** `σ_i²`. The inclusion `⊇` is
`s_i² = 1`; for `⊆`, the generators of `Art(M)` modulo the squares are involutions satisfying the
braid relations, hence the Coxeter relations, so the quotient map factors through `W(M)`. -/
theorem pureArtinGroup_eq_normalClosure :
    M.pureArtinGroup = Subgroup.normalClosure (Set.range fun i => M.artinGen i ^ 2) := by
  apply le_antisymm
  · set N := Subgroup.normalClosure (Set.range fun i => M.artinGen i ^ 2)
    let q : M.ArtinGroup →* M.ArtinGroup ⧸ N := QuotientGroup.mk' N
    have hq : M.pureArtinGroup ≤ q.ker := M.pureArtinGroup_le_ker_of_sq q fun i =>
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨i, rfl⟩)
    rwa [QuotientGroup.ker_mk'] at hq
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, mem_pureArtinGroup, map_pow, toCoxeterGroup_of]
    exact M.toCoxeterSystem.simple_sq i

/-! ### Reversal -/

/-- Reversing `alternatingWord i i' m` gives `alternatingWord i' i m` for even `m` and the word
itself for odd `m`. -/
theorem reverse_alternatingWord (i i' : B) (m : ℕ) :
    (alternatingWord i i' m).reverse =
      if Even m then alternatingWord i' i m else alternatingWord i i' m := by
  induction m generalizing i i' with
  | zero => simp [alternatingWord]
  | succ m ih =>
    conv_lhs => rw [alternatingWord_succ, List.concat_eq_append, List.reverse_append, ih i' i]
    by_cases hm : Even m
    · have h₁ : ¬ Even (m + 1) := by simp [hm, parity_simps]
      simp only [hm, h₁, ↓reduceIte, alternatingWord_succ']
      rfl
    · have h₁ : Even (m + 1) := by simp [hm, parity_simps]
      simp only [hm, h₁, ↓reduceIte, alternatingWord_succ']
      rfl

/-- Braid relations are closed under reversal: values satisfy them in `G` exactly when their
images satisfy them in the opposite monoid. -/
theorem isBraidLiftable_op_iff {G : Type*} [Monoid G] (f : B → G) :
    M.IsBraidLiftable (MulOpposite.op ∘ f) ↔ M.IsBraidLiftable f := by
  have key : ∀ l : List B, (l.map (MulOpposite.op ∘ f)).prod =
      MulOpposite.op ((l.reverse.map f).prod) := by
    intro l
    rw [MulOpposite.op_list_prod, List.map_reverse, List.map_reverse, List.reverse_reverse,
      List.map_map]
  refine forall_congr' fun i => forall_congr' fun i' => ?_
  rw [key, key, MulOpposite.op_inj, braidWord, braidWord, reverse_alternatingWord,
    reverse_alternatingWord, M.symmetric i' i]
  split_ifs
  · exact eq_comm
  · exact Iff.rfl

/-- **The anti-automorphism** `σ_i ↦ σ_i` of the Artin group, which reads every word backwards. -/
def ArtinGroup.reverse : M.ArtinGroup →* M.ArtinGroupᵐᵒᵖ :=
  ArtinGroup.lift (MulOpposite.op ∘ M.artinGen)
    ((M.isBraidLiftable_op_iff _).2 ArtinGroup.isBraidLiftable_artinGen)

@[simp] theorem ArtinGroup.reverse_of (i : B) :
    ArtinGroup.reverse M (M.artinGen i) = MulOpposite.op (M.artinGen i) :=
  ArtinGroup.lift_of _ _ i

/-- `reverse` is an involution. -/
theorem ArtinGroup.unop_reverse_unop_reverse (g : M.ArtinGroup) :
    (ArtinGroup.reverse M (ArtinGroup.reverse M g).unop).unop = g := by
  let ρ : M.ArtinGroup →* M.ArtinGroup :=
    (MulEquiv.opOp M.ArtinGroup).symm.toMonoidHom.comp
      ((ArtinGroup.reverse M).op.comp
        ((MulEquiv.op (MulEquiv.refl M.ArtinGroup)).symm.toMonoidHom.comp
          (ArtinGroup.reverse M)))
  have : ρ = MonoidHom.id _ := ArtinGroup.hom_ext fun i => by
    simp [ρ, MulEquiv.opOp]
    exact rfl
  exact DFunLike.congr_fun this g

/-! ### One conjugation identity per braid relation -/

/-- **The braid relation of length `m` is one conjugation identity.** In a group, for
`m = M i i' ≥ 1` and `u` the product along `alternatingWord i' i (m - 1)`, the braid relation is
`u f(i') u⁻¹ = f(c)`, with `c = i` for odd `m` and `c = i'` for even `m`. For `m = 2` it says
that `f i` commutes with `f i'`; for `m = 3`, that `(f i' f i) f i' (f i' f i)⁻¹ = f i`. -/
theorem braid_iff_conj {G : Type*} [Group G] (f : B → G) (i i' : B) (hm : M i i' ≠ 0) :
    ((braidWord M i i').map f).prod = ((braidWord M i' i).map f).prod ↔
      ((alternatingWord i' i (M i i' - 1)).map f).prod * f i' *
        (((alternatingWord i' i (M i i' - 1)).map f).prod)⁻¹ =
          f (if Even (M i i' - 1) then i else i') := by
  obtain ⟨m, hm'⟩ : ∃ m, M i i' = m + 1 := Nat.exists_eq_succ_of_ne_zero hm
  rw [braidWord, braidWord, M.symmetric i' i, hm', alternatingWord_succ, alternatingWord_succ',
    Nat.add_sub_cancel]
  simp only [List.concat_eq_append, List.map_append, List.prod_append, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [mul_inv_eq_iff_eq_mul]

/-- **Braid relations from one conjugation identity per edge.** Values `f i` in a group satisfy
the braid relations of `M` as soon as `u f(i') u⁻¹ = f(c)` for every pair `i ≠ i'` with
`M i i' ≠ 0` (notation of `braid_iff_conj`). -/
theorem isBraidLiftable_of_conj {G : Type*} [Group G] (f : B → G)
    (h : ∀ i i', i ≠ i' → M i i' ≠ 0 →
      ((alternatingWord i' i (M i i' - 1)).map f).prod * f i' *
        (((alternatingWord i' i (M i i' - 1)).map f).prod)⁻¹ =
          f (if Even (M i i' - 1) then i else i')) :
    M.IsBraidLiftable f :=
  (M.isBraidLiftable_iff f).2 fun i i' hii hm => (M.braid_iff_conj f i i' hm).2 (h i i' hii hm)

/-- **Braid relations from an equivariant map.** Let `G` act on `X` and let `τ : X → G` be
equivariant for conjugation at the points `x i`: `τ (g • x i) = g τ(x i) g⁻¹`, the formula
`T_{Φ S} = Φ T_S Φ⁻¹` for twists. Then the values `τ (x i)` satisfy the braid relations of `M`
as soon as there is one object identity `u • x i' = x c` per pair `i ≠ i'` with `M i i' ≠ 0`,
where `u` is the product of the `τ (x j)` along `alternatingWord i' i (M i i' - 1)` and `c` is as
in `braid_iff_conj`. For `m = 2` the identity is `τ(x i) • x i' = x i'`; for `m = 3` it is
`τ(x i') τ(x i) • x i' = x i`. -/
theorem isBraidLiftable_of_equivariant {G X : Type*} [Group G] [MulAction G X] (τ : X → G)
    (x : B → X) (hτ : ∀ (g : G) (i : B), τ (g • x i) = g * τ (x i) * g⁻¹)
    (hobj : ∀ i i', i ≠ i' → M i i' ≠ 0 →
      ((alternatingWord i' i (M i i' - 1)).map (τ ∘ x)).prod • x i' =
        x (if Even (M i i' - 1) then i else i')) :
    M.IsBraidLiftable (τ ∘ x) :=
  M.isBraidLiftable_of_conj _ fun i i' hii hm => by
    simp only [Function.comp_apply]
    rw [← hτ, hobj i i' hii hm]

/-! ### The Coxeter matrix of a configuration of spherical objects -/

/-- The Coxeter matrix of a configuration of spherical objects `S_i` with total Ext dimensions
`e i j = Σ_k dim Ext^k(S_i, S_j)` (Seidel–Thomas, arXiv:math/0001043, §2): off the diagonal,
`m = 2` for `e = 0`, `m = 3` for `e = 1` and `m = ∞` (Mathlib's `0`) for `e ≥ 2`. The diagonal is
`1` and the diagonal values of `e` are not read (for a spherical object `e i i = 2`, which would
read as `∞`). -/
def ofExt [DecidableEq B] (e : B → B → ℕ) (he : ∀ i j, e i j = e j i) : CoxeterMatrix B where
  M := Matrix.of fun i j =>
    if i = j then 1 else if e i j = 0 then 2 else if e i j = 1 then 3 else 0
  isSymm := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.of_apply, he i j, eq_comm (a := i)]
  diagonal i := by simp
  off_diagonal i j hij := by
    simp only [Matrix.of_apply, hij, ite_false]
    split_ifs <;> omega

theorem ofExt_apply_of_ne [DecidableEq B] (e : B → B → ℕ) (he : ∀ i j, e i j = e j i)
    {i j : B} (hij : i ≠ j) :
    ofExt e he i j = if e i j = 0 then 2 else if e i j = 1 then 3 else 0 := by
  simp [ofExt, hij]

/-- For the matrix `ofExt e`, the braid relations are: `f i` and `f j` commute when `e i j = 0`,
and satisfy `f i f j f i = f j f i f j` when `e i j = 1`; nothing is asked when `e i j ≥ 2`. -/
theorem isBraidLiftable_ofExt [DecidableEq B] (e : B → B → ℕ) (he : ∀ i j, e i j = e j i)
    {G : Type*} [Monoid G] (f : B → G)
    (h0 : ∀ i j, i ≠ j → e i j = 0 → f i * f j = f j * f i)
    (h1 : ∀ i j, i ≠ j → e i j = 1 → f i * f j * f i = f j * f i * f j) :
    (ofExt e he).IsBraidLiftable f := by
  intro i j
  by_cases hij : i = j
  · subst hij; rfl
  rw [braidWord, braidWord, (ofExt e he).symmetric j i, ofExt_apply_of_ne e he hij]
  split_ifs with h0' h1'
  · simp [alternatingWord, h0 j i (Ne.symm hij) (he i j ▸ h0')]
  · simpa [alternatingWord, mul_assoc] using h1 j i (Ne.symm hij) (he i j ▸ h1')
  · rfl

end CoxeterMatrix
