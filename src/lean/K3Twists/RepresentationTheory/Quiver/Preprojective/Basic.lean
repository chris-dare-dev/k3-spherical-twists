/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Order.HarderNarasimhan
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Pi
import Mathlib.Order.CompleteSublattice

/-!
# Representations of a doubled quiver with loops

Let `Q` be a quiver on a vertex type `I`, given by its sets of arrows `Q i j` from `i` to `j`;
loops `Q i i` are allowed. Its **double** has, for every arrow `a : i → j` of `Q`, the arrow `a`
and a reverse arrow `a* : j → i`. So the multiplicities of the double are symmetric, and a loop of
`Q` gives two loops of the double. A representation of the double over a field `k` on vector
spaces `V i` is a family of linear maps `A a : V i → V j` and `B a : V j → V i`, the actions of
`a` and `a*`. The **preprojective relation** at a vertex `i` is

  `∑_{a : j → i} A_a B_a - ∑_{a : i → j} B_a A_a = 0`,

the component at `i` of `∑_a [a, a*]`; its representations are the modules over the preprojective
algebra `Π_Q` (Gelfand–Ponomarev; Crawley-Boevey, *On the exceptional fibres of Kleinian
singularities*, Amer. J. Math. 122 (2000)). For a loop `a` the two terms make the commutator
`[A_a, B_a]`: for the Jordan quiver, one vertex with one loop, the preprojective representations
are the modules over `k[x, y]`.

## The wall model

Let `S_i` be pairwise non-isomorphic stable objects of one phase in a 2-Calabi–Yau category, with
`dim Ext¹(S_i, S_j) = m_{ij}` for `i ≠ j` and `dim Ext¹(S_i, S_i) = 2 m_{ii}` (by Serre duality the
first is symmetric and the second even). A half of their `Ext`-quiver is a quiver `Q` with `m_{ij}`
arrows between `i ≠ j`, all in one direction, and `m_{ii}` loops at `i`. By formality of the
`Ext`-algebra of the `S_i` (Davison, arXiv:2106.07692, Proposition 7.8), the iterated extensions of
the `S_i` are the nilpotent representations of the double of `Q` with the preprojective relations,
and the subobjects of a wall object with multiplicities `d_i` in the `S_i` are its
subrepresentations of dimension vector `d`. A spherical `S_i` is a vertex without loops and an
`S_i` with `e(S_i) = 2` a vertex with one loop. This equivalence is not formalized:
`Quiver.Preprojective.FormalWallHypotheses` states it as a hypothesis. For two spherical objects
the model is the doubled Kronecker quiver of `RepresentationTheory/Quiver/Kronecker/`, which is a
special case (`Preprojective/Kronecker.lean`).

## Main definitions

* `Quiver.Preprojective.DoubledRep k Q V`: the maps `A a`, `B a`;
* `DoubledRep.relation`, `DoubledRep.IsPreprojective`: the relations;
* `DoubledRep.IsNilpotent`: every path of length at least some `n` acts by zero;
* `DoubledRep.Hom M N`: the morphisms, as a `k`-subspace of `∏ i, (V i →ₗ W i)`;
* `DoubledRep.subreps M`: the subrepresentations, families of subspaces `U i` with
  `A_a U_i ⊆ U_j` and `B_a U_j ⊆ U_i`, a complete sublattice of `∏ i, Submodule k (V i)`;
* `DoubledRep.dimVec`: the dimension vector `i ↦ dim U_i` of a subrepresentation;
* `DoubledRep.Iso`, `DoubledRep.Iso.mapSubrep`: isomorphisms, and the isomorphism of lattices of
  subrepresentations they induce, which preserves dimension vectors;
* `DoubledRep.restrict`, `DoubledRep.quotient`, `DoubledRep.subquotient`: the restriction to a
  subrepresentation, the quotient by it, and the subquotient `Q / P` of `P ≤ Q`;
* `DoubledRep.chargeFunction`: the charge function on subrepresentations given by weights
  `r_i`, `d_i` on the vertices, rank `∑ r_i dim U_i` and degree `∑ d_i dim U_i`.

## Main results

* `DoubledRep.dimVec_sup_add_inf`: the dimension vector is a valuation on subrepresentations;
* `DoubledRep.totalDim_lt_of_lt`: a strictly larger subrepresentation has strictly larger total
  dimension;
* `DoubledRep.nonempty_hnFiltration`: every charge with `Z_i = -d_i + i r_i` in the upper half
  plane or on the negative real axis has a Harder–Narasimhan filtration on the
  subrepresentations of a finite-dimensional representation; it is unique
  (`Order.ChargeFunction.HNChain.instSubsingleton`).

## Implementation notes

The quiver is a family of types `Q : I → I → Type*`, not an instance of Mathlib's `Quiver`
class: a vertex type such as `Fin 2` already carries a `Quiver` instance from its order. Arrows
are typed by their endpoints, so the relation at `i` is a sum of endomorphisms of `V i` with no
transport between vertex spaces. Quiver representations are not in Mathlib, and as in the
Kronecker files a representation is a family of maps on given spaces, not an object of a bundled
abelian category.
-/

namespace Quiver.Preprojective

open Module Order

variable (k : Type*) [Field k] {I : Type*} (Q : I → I → Type*) (V : I → Type*)
  [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

/-- A representation of the double of the quiver `Q` on the spaces `V i`: a map
`A a : V i → V j` and a map `B a : V j → V i` for every arrow `a : i → j` of `Q`. -/
structure DoubledRep where
  /-- The arrows of `Q`. -/
  A : ∀ {i j : I}, Q i j → V i →ₗ[k] V j
  /-- The reverse arrows. -/
  B : ∀ {i j : I}, Q i j → V j →ₗ[k] V i

namespace DoubledRep

variable {k Q V}

/-! ### The relations -/

section Relations

variable [Fintype I] [∀ i j, Fintype (Q i j)]

/-- The preprojective relation at the vertex `i`, `∑_{a : j → i} A_a B_a - ∑_{a : i → j} B_a A_a`:
the component at `i` of `∑_a [a, a*]`. -/
def relation (M : DoubledRep k Q V) (i : I) : Module.End k (V i) :=
  ∑ j, ∑ a : Q j i, M.A a ∘ₗ M.B a - ∑ j, ∑ a : Q i j, M.B a ∘ₗ M.A a

/-- The preprojective relations hold at every vertex. -/
def IsPreprojective (M : DoubledRep k Q V) : Prop :=
  ∀ i, M.relation i = 0

lemma relation_apply (M : DoubledRep k Q V) (i : I) (x : V i) :
    M.relation i x = ∑ j, ∑ a : Q j i, M.A a (M.B a x) - ∑ j, ∑ a : Q i j, M.B a (M.A a x) := by
  simp [relation, LinearMap.sum_apply]

end Relations

section Nilpotent

variable [DecidableEq I]

/-- The arrows of the double as endomorphisms of `∏ i, V i`: `Sum.inl ⟨i, j, a⟩` acts by `A a`
and `Sum.inr ⟨i, j, a⟩` by `B a`. A path is a product of arrows. -/
def arrow (M : DoubledRep k Q V) : (Σ i j, Q i j) ⊕ (Σ i j, Q i j) → Module.End k (∀ i, V i)
  | .inl ⟨i, j, a⟩ => LinearMap.single k V j ∘ₗ M.A a ∘ₗ LinearMap.proj i
  | .inr ⟨i, j, a⟩ => LinearMap.single k V i ∘ₗ M.B a ∘ₗ LinearMap.proj j

/-- A representation is nilpotent when every path of length at least some `n` acts by zero: the
product of the arrows along any word `w` with `n ≤ w.length` vanishes. -/
def IsNilpotent (M : DoubledRep k Q V) : Prop :=
  ∃ n : ℕ, ∀ w : List ((Σ i j, Q i j) ⊕ (Σ i j, Q i j)), n ≤ w.length →
    (w.map M.arrow).prod = 0

end Nilpotent

/-! ### Morphisms -/

section Hom

variable {W : I → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)]

/-- The morphisms `M → N`: families of maps `f i : V i → W i` with `f j A_a = A_a f i` and
`f i B_a = B_a f j` for every arrow `a : i → j`. They form a `k`-subspace of
`∏ i, (V i →ₗ W i)`. -/
def Hom (M : DoubledRep k Q V) (N : DoubledRep k Q W) : Submodule k (∀ i, V i →ₗ[k] W i) where
  carrier := {f | ∀ i j (a : Q i j), f j ∘ₗ M.A a = N.A a ∘ₗ f i ∧ f i ∘ₗ M.B a = N.B a ∘ₗ f j}
  add_mem' {f g} hf hg i j a := by
    simp only [Pi.add_apply, LinearMap.add_comp, LinearMap.comp_add, (hf i j a).1, (hf i j a).2,
      (hg i j a).1, (hg i j a).2, and_self]
  zero_mem' i j a := by simp
  smul_mem' c f hf i j a := by
    simp only [Pi.smul_apply, LinearMap.smul_comp, LinearMap.comp_smul, (hf i j a).1,
      (hf i j a).2, and_self]

lemma mem_Hom {M : DoubledRep k Q V} {N : DoubledRep k Q W} {f : ∀ i, V i →ₗ[k] W i} :
    f ∈ Hom M N ↔
      ∀ i j (a : Q i j), f j ∘ₗ M.A a = N.A a ∘ₗ f i ∧ f i ∘ₗ M.B a = N.B a ∘ₗ f j :=
  Iff.rfl

/-- The identity is a morphism. -/
lemma id_mem_Hom (M : DoubledRep k Q V) : (fun _ ↦ LinearMap.id) ∈ Hom M M :=
  fun _ _ _ ↦ ⟨rfl, rfl⟩

/-- The composite of two morphisms is a morphism. -/
lemma comp_mem_Hom {U : I → Type*} [∀ i, AddCommGroup (U i)] [∀ i, Module k (U i)]
    {M : DoubledRep k Q V} {N : DoubledRep k Q W} {P : DoubledRep k Q U}
    {f : ∀ i, V i →ₗ[k] W i} {g : ∀ i, W i →ₗ[k] U i} (hf : f ∈ Hom M N) (hg : g ∈ Hom N P) :
    (fun i ↦ g i ∘ₗ f i) ∈ Hom M P := fun i j a ↦
  ⟨by rw [LinearMap.comp_assoc, (hf i j a).1, ← LinearMap.comp_assoc, (hg i j a).1,
      LinearMap.comp_assoc],
    by rw [LinearMap.comp_assoc, (hf i j a).2, ← LinearMap.comp_assoc, (hg i j a).2,
      LinearMap.comp_assoc]⟩

end Hom

/-! ### Subrepresentations -/

section Subrep

/-- A family of subspaces `U i ⊆ V i` is a subrepresentation of `M` when every arrow `a : i → j`
maps `U i` into `U j` and its reverse maps `U j` into `U i`. -/
def IsSubrep (M : DoubledRep k Q V) (p : ∀ i, Submodule k (V i)) : Prop :=
  ∀ i j (a : Q i j), p i ≤ (p j).comap (M.A a) ∧ p j ≤ (p i).comap (M.B a)

/-- The subrepresentations of `M`, a complete sublattice of the families of subspaces. -/
def subreps (M : DoubledRep k Q V) : CompleteSublattice (∀ i, Submodule k (V i)) :=
  CompleteSublattice.mk' {p | M.IsSubrep p}
    (fun s hs i j a ↦ by
      simp only [sSup_apply]
      exact ⟨iSup_le fun p ↦ ((hs p.2) i j a).1.trans
          (Submodule.comap_mono (le_iSup (fun q : s ↦ (q : ∀ i, Submodule k (V i)) j) p)),
        iSup_le fun p ↦ ((hs p.2) i j a).2.trans
          (Submodule.comap_mono (le_iSup (fun q : s ↦ (q : ∀ i, Submodule k (V i)) i) p))⟩)
    (fun s hs i j a ↦ by
      refine ⟨fun x hx ↦ ?_, fun y hy ↦ ?_⟩
      · simp only [sInf_apply, Submodule.mem_comap, Submodule.mem_iInf] at hx ⊢
        exact fun p ↦ ((hs p.2) i j a).1 (hx p)
      · simp only [sInf_apply, Submodule.mem_comap, Submodule.mem_iInf] at hy ⊢
        exact fun p ↦ ((hs p.2) i j a).2 (hy p))

variable {M : DoubledRep k Q V}

lemma mem_subreps {p : ∀ i, Submodule k (V i)} : p ∈ M.subreps ↔ M.IsSubrep p :=
  Iff.rfl

lemma A_mem (N : M.subreps) {i j : I} (a : Q i j) {x : V i}
    (hx : x ∈ (N : ∀ i, Submodule k (V i)) i) : M.A a x ∈ (N : ∀ i, Submodule k (V i)) j :=
  (N.2 i j a).1 hx

lemma B_mem (N : M.subreps) {i j : I} (a : Q i j) {y : V j}
    (hy : y ∈ (N : ∀ i, Submodule k (V i)) j) : M.B a y ∈ (N : ∀ i, Submodule k (V i)) i :=
  (N.2 i j a).2 hy

@[simp]
lemma coe_sup_apply (N N' : M.subreps) (i : I) :
    ((N ⊔ N' : M.subreps) : ∀ i, Submodule k (V i)) i =
      (N : ∀ i, Submodule k (V i)) i ⊔ (N' : ∀ i, Submodule k (V i)) i :=
  rfl

@[simp]
lemma coe_inf_apply (N N' : M.subreps) (i : I) :
    ((N ⊓ N' : M.subreps) : ∀ i, Submodule k (V i)) i =
      (N : ∀ i, Submodule k (V i)) i ⊓ (N' : ∀ i, Submodule k (V i)) i :=
  rfl

@[simp]
lemma coe_bot_apply (i : I) : ((⊥ : M.subreps) : ∀ i, Submodule k (V i)) i = ⊥ :=
  rfl

@[simp]
lemma coe_top_apply (i : I) : ((⊤ : M.subreps) : ∀ i, Submodule k (V i)) i = ⊤ :=
  rfl

lemma le_iff_forall {N N' : M.subreps} :
    N ≤ N' ↔ ∀ i, (N : ∀ i, Submodule k (V i)) i ≤ (N' : ∀ i, Submodule k (V i)) i :=
  Iff.rfl

/-- The dimension vector `i ↦ dim U i` of a subrepresentation `U`. -/
noncomputable def dimVec (N : M.subreps) (i : I) : ℕ :=
  finrank k ((N : ∀ i, Submodule k (V i)) i)

@[simp]
lemma dimVec_bot : dimVec (⊥ : M.subreps) = 0 := by
  funext i
  simp [dimVec]

@[simp]
lemma dimVec_top : dimVec (⊤ : M.subreps) = fun i ↦ finrank k (V i) := by
  funext i
  simp [dimVec]

variable [∀ i, FiniteDimensional k (V i)]

lemma dimVec_mono {N N' : M.subreps} (h : N ≤ N') (i : I) : dimVec N i ≤ dimVec N' i :=
  Submodule.finrank_mono (h i)

/-- The dimension vector is a valuation on the lattice of subrepresentations. -/
theorem dimVec_sup_add_inf (N N' : M.subreps) :
    dimVec (N ⊔ N') + dimVec (N ⊓ N') = dimVec N + dimVec N' := by
  funext i
  simp only [Pi.add_apply, dimVec, coe_sup_apply, coe_inf_apply,
    Submodule.finrank_sup_add_finrank_inf_eq]

lemma exists_dimVec_lt {N N' : M.subreps} (h : N < N') : ∃ i, dimVec N i < dimVec N' i := by
  have h' : (N : ∀ i, Submodule k (V i)) < N' := h
  obtain ⟨-, i, hi⟩ := Pi.lt_def.mp h'
  exact ⟨i, Submodule.finrank_lt_finrank_of_lt hi⟩

/-- A strictly larger subrepresentation has strictly larger total dimension. -/
theorem totalDim_lt_of_lt [Fintype I] {N N' : M.subreps} (h : N < N') :
    ∑ i, dimVec N i < ∑ i, dimVec N' i := by
  obtain ⟨i, hi⟩ := exists_dimVec_lt h
  exact Finset.sum_lt_sum (fun j _ ↦ dimVec_mono h.le j) ⟨i, Finset.mem_univ _, hi⟩

/-- A subrepresentation is determined, among those containing it, by its dimension vector. -/
theorem eq_of_le_of_dimVec_eq {N N' : M.subreps} (h : N ≤ N') (hd : dimVec N = dimVec N') :
    N = N' := by
  by_contra hne
  obtain ⟨i, hi⟩ := exists_dimVec_lt (lt_of_le_of_ne h hne)
  rw [hd] at hi
  exact lt_irrefl _ hi

end Subrep

/-! ### Isomorphisms -/

section Iso

variable {W : I → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)]

/-- An isomorphism of representations: linear equivalences at the vertices commuting with every
arrow and every reverse arrow. -/
structure Iso (M : DoubledRep k Q V) (N : DoubledRep k Q W) where
  /-- The equivalence at each vertex. -/
  e : ∀ i, V i ≃ₗ[k] W i
  comm_A {i j : I} (a : Q i j) (x : V i) : e j (M.A a x) = N.A a (e i x)
  comm_B {i j : I} (a : Q i j) (y : V j) : e i (M.B a y) = N.B a (e j y)

namespace Iso

/-- The identity isomorphism. -/
def refl (M : DoubledRep k Q V) : Iso M M where
  e i := LinearEquiv.refl k (V i)
  comm_A _ _ := rfl
  comm_B _ _ := rfl

variable {M : DoubledRep k Q V} {N : DoubledRep k Q W}

/-- The inverse isomorphism. -/
def symm (u : Iso M N) : Iso N M where
  e i := (u.e i).symm
  comm_A {i j} a y := (u.e j).injective (by
    rw [LinearEquiv.apply_symm_apply, u.comm_A, LinearEquiv.apply_symm_apply])
  comm_B {i j} a y := (u.e i).injective (by
    rw [LinearEquiv.apply_symm_apply, u.comm_B, LinearEquiv.apply_symm_apply])

/-- The composite of two isomorphisms. -/
def trans {U : I → Type*} [∀ i, AddCommGroup (U i)] [∀ i, Module k (U i)]
    {P : DoubledRep k Q U} (u : Iso M N) (v : Iso N P) : Iso M P where
  e i := (u.e i).trans (v.e i)
  comm_A a x := by simp only [LinearEquiv.trans_apply, u.comm_A, v.comm_A]
  comm_B a y := by simp only [LinearEquiv.trans_apply, u.comm_B, v.comm_B]

/-- The maps of an isomorphism form a morphism. -/
lemma mem_Hom (u : Iso M N) : (fun i ↦ (u.e i : V i →ₗ[k] W i)) ∈ Hom M N :=
  fun _ _ a ↦ ⟨LinearMap.ext (u.comm_A a), LinearMap.ext (u.comm_B a)⟩

/-- An isomorphic copy of a representation with the preprojective relations satisfies them. -/
lemma isPreprojective [Fintype I] [∀ i j, Fintype (Q i j)] (u : Iso M N)
    (hM : M.IsPreprojective) : N.IsPreprojective := by
  intro i
  refine LinearMap.ext fun y ↦ ?_
  obtain ⟨x, rfl⟩ := (u.e i).surjective y
  have h := congrArg (u.e i) (LinearMap.congr_fun (hM i) x)
  simp only [relation_apply, map_sub, map_sum, LinearMap.zero_apply, map_zero, u.comm_A,
    u.comm_B] at h ⊢
  exact h

/-- An isomorphism of representations induces an isomorphism of the lattices of
subrepresentations, `U ↦ (e i (U i))_i`. -/
def mapSubrep (u : Iso M N) : M.subreps ≃o N.subreps where
  toFun P := ⟨fun i ↦ ((P : ∀ i, Submodule k (V i)) i).map (u.e i : V i →ₗ[k] W i),
    fun i j a ↦ ⟨by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨M.A a x, A_mem P a hx, u.comm_A a x⟩, by
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨M.B a y, B_mem P a hy, u.comm_B a y⟩⟩⟩
  invFun P := ⟨fun i ↦ ((P : ∀ i, Submodule k (W i)) i).comap (u.e i : V i →ₗ[k] W i),
    fun i j a ↦ ⟨fun x hx ↦ by
      simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at hx ⊢
      rw [u.comm_A]
      exact A_mem P a hx, fun y hy ↦ by
      simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at hy ⊢
      rw [u.comm_B]
      exact B_mem P a hy⟩⟩
  left_inv P := Subtype.ext (funext fun i ↦
    Submodule.comap_map_eq_of_injective (u.e i).injective _)
  right_inv P := Subtype.ext (funext fun i ↦
    Submodule.map_comap_eq_of_surjective (u.e i).surjective _)
  map_rel_iff' {P P'} := by
    change (∀ i, ((P : ∀ i, Submodule k (V i)) i).map (u.e i : V i →ₗ[k] W i) ≤
        ((P' : ∀ i, Submodule k (V i)) i).map (u.e i : V i →ₗ[k] W i)) ↔ P ≤ P'
    simp only [Submodule.map_le_map_iff_of_injective (u.e _).injective]
    rfl

lemma coe_mapSubrep_apply (u : Iso M N) (P : M.subreps) (i : I) :
    (u.mapSubrep P : ∀ i, Submodule k (W i)) i =
      ((P : ∀ i, Submodule k (V i)) i).map (u.e i : V i →ₗ[k] W i) :=
  rfl

/-- An isomorphism preserves dimension vectors of subrepresentations. -/
lemma dimVec_mapSubrep (u : Iso M N) (P : M.subreps) : dimVec (u.mapSubrep P) = dimVec P :=
  funext fun i ↦ LinearEquiv.finrank_map_eq (u.e i) _

end Iso

end Iso

/-! ### Restrictions, quotients and subquotients -/

section Restrict

variable (M : DoubledRep k Q V) (P : M.subreps)

/-- The restriction of `M` to a subrepresentation `P`. -/
def restrict : DoubledRep k Q (fun i ↦ (P : ∀ i, Submodule k (V i)) i) where
  A a := (M.A a).restrict fun _ hx ↦ A_mem P a hx
  B a := (M.B a).restrict fun _ hy ↦ B_mem P a hy

@[simp]
lemma coe_restrict_A_apply {i j : I} (a : Q i j) (x : (P : ∀ i, Submodule k (V i)) i) :
    ((M.restrict P).A a x : V j) = M.A a x :=
  rfl

@[simp]
lemma coe_restrict_B_apply {i j : I} (a : Q i j) (y : (P : ∀ i, Submodule k (V i)) j) :
    ((M.restrict P).B a y : V i) = M.B a y :=
  rfl

/-- The quotient of `M` by a subrepresentation `P`. -/
def quotient : DoubledRep k Q (fun i ↦ V i ⧸ (P : ∀ i, Submodule k (V i)) i) where
  A a := Submodule.mapQ _ _ (M.A a) fun _ hx ↦ A_mem P a hx
  B a := Submodule.mapQ _ _ (M.B a) fun _ hy ↦ B_mem P a hy

@[simp]
lemma quotient_A_mk {i j : I} (a : Q i j) (x : V i) :
    (M.quotient P).A a (Submodule.Quotient.mk x) = Submodule.Quotient.mk (M.A a x) :=
  rfl

@[simp]
lemma quotient_B_mk {i j : I} (a : Q i j) (y : V j) :
    (M.quotient P).B a (Submodule.Quotient.mk y) = Submodule.Quotient.mk (M.B a y) :=
  rfl

/-- `P ⊓ Q` as a subrepresentation of the restriction `M|Q`, as `Subgroup.subgroupOf`. -/
def subrepOf (P P' : M.subreps) : (M.restrict P').subreps :=
  ⟨fun i ↦ ((P : ∀ i, Submodule k (V i)) i).comap ((P' : ∀ i, Submodule k (V i)) i).subtype,
    fun _ _ a ↦ ⟨fun _ hx ↦ A_mem P a hx, fun _ hy ↦ B_mem P a hy⟩⟩

/-- The subquotient `P' / P` of `M`, for subrepresentations `P ≤ P'` (in general
`P' / (P ⊓ P')`). -/
def subquotient (P P' : M.subreps) :
    DoubledRep k Q (fun i ↦ (P' : ∀ i, Submodule k (V i)) i ⧸
      ((M.subrepOf P P' : ∀ i, Submodule k ((P' : ∀ i, Submodule k (V i)) i)) i)) :=
  (M.restrict P').quotient (M.subrepOf P P')

variable {M} in
/-- The restriction of `M|P'` to `P ≤ P'` is the restriction of `M` to `P`. -/
def restrictSubrepOfIso {P P' : M.subreps} (h : P ≤ P') :
    Iso ((M.restrict P').restrict (M.subrepOf P P')) (M.restrict P) where
  e i := Submodule.comapSubtypeEquivOfLe (h i)
  comm_A _ _ := rfl
  comm_B _ _ := rfl

variable [Fintype I] [∀ i j, Fintype (Q i j)]

variable {M} in
/-- A restriction of a representation with the preprojective relations satisfies them. -/
lemma IsPreprojective.restrict (hM : M.IsPreprojective) (P : M.subreps) :
    (M.restrict P).IsPreprojective := by
  intro i
  refine LinearMap.ext fun x ↦ Subtype.ext ?_
  have h := LinearMap.congr_fun (hM i) x
  simp only [relation_apply, LinearMap.zero_apply] at h ⊢
  simpa using h

variable {M} in
/-- A quotient of a representation with the preprojective relations satisfies them. -/
lemma IsPreprojective.quotient (hM : M.IsPreprojective) (P : M.subreps) :
    (M.quotient P).IsPreprojective := by
  intro i
  refine LinearMap.ext fun x ↦ ?_
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    have h := congrArg (Submodule.mkQ ((P : ∀ i, Submodule k (V i)) i))
      (LinearMap.congr_fun (hM i) x)
    simp only [relation_apply, map_sub, map_sum, LinearMap.zero_apply, map_zero,
      Submodule.mkQ_apply] at h ⊢
    simpa using h

end Restrict

/-! ### Charge functions and Harder–Narasimhan filtrations -/

section Charge

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [∀ i, FiniteDimensional k (V i)] [Fintype I]

omit [IsStrictOrderedRing K] in
/-- The rank weight of a vertex with `0 < r` or `r = 0 < d` is nonnegative. -/
private lemma weight_nonneg {r d : K} (h : 0 < r ∨ (r = 0 ∧ 0 < d)) : 0 ≤ r := by
  rcases h with h | h
  exacts [h.le, h.1.ge]

/-- The charge function on the subrepresentations of `M` with weights `r i` and `d i` at the
vertices: rank `∑ r_i dim U_i` and degree `∑ d_i dim U_i`. It is the charge
`Z(U) = ∑ dim U_i Z_i` with `Z_i = -d_i + i r_i`, read as `rk = Im Z`, `deg = -Re Z`; a vertex
with `r_i = 0 < d_i` (a simple on the negative real axis) gives vertical steps. -/
noncomputable def chargeFunction (M : DoubledRep k Q V) (r d : I → K)
    (h : ∀ i, 0 < r i ∨ (r i = 0 ∧ 0 < d i)) : ChargeFunction M.subreps K where
  rk N := ∑ i, r i * dimVec N i
  deg N := ∑ i, d i * dimVec N i
  lex_lt {N N'} hlt := by
    have hle : ∀ i, (dimVec N i : K) ≤ dimVec N' i := fun i ↦ by
      exact_mod_cast dimVec_mono hlt.le i
    obtain ⟨i₀, hi₀⟩ := exists_dimVec_lt hlt
    have hi₀' : (dimVec N i₀ : K) < dimVec N' i₀ := by exact_mod_cast hi₀
    have hr : ∀ i ∈ Finset.univ, r i * (dimVec N i : K) ≤ r i * dimVec N' i := fun i _ ↦
      mul_le_mul_of_nonneg_left (hle i) (weight_nonneg (h i))
    rcases (Finset.sum_le_sum hr).lt_or_eq with hlt' | heq
    · exact Or.inl hlt'
    · right
      refine ⟨heq, ?_⟩
      have hterm := (Finset.sum_eq_sum_iff_of_le hr).mp heq
      have key : ∀ i, (dimVec N i : K) < dimVec N' i → r i = 0 ∧ 0 < d i := fun i hi ↦ by
        have h0 : r i * ((dimVec N' i : K) - dimVec N i) = 0 := by
          rw [mul_sub, ← hterm i (Finset.mem_univ _), sub_self]
        have hr0 : r i = 0 := by
          rcases mul_eq_zero.mp h0 with h0 | h0
          · exact h0
          · exact absurd h0 (sub_ne_zero.mpr hi.ne')
        rcases h i with h' | h'
        · exact absurd hr0 h'.ne'
        · exact h'
      refine Finset.sum_lt_sum (fun i _ ↦ ?_) ⟨i₀, Finset.mem_univ _, ?_⟩
      · rcases (hle i).lt_or_eq with hi | hi
        · exact (mul_lt_mul_of_pos_left hi (key i hi).2).le
        · rw [hi]
      · exact mul_lt_mul_of_pos_left hi₀' (key i₀ hi₀').2
  rk_sup_add_inf N N' := by
    have e := dimVec_sup_add_inf N N'
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have ei : ((dimVec (N ⊔ N') i : ℕ) : K) + dimVec (N ⊓ N') i = dimVec N i + dimVec N' i := by
      exact_mod_cast congrFun e i
    rw [← mul_add, ← mul_add, ei]
  deg_sup_add_inf N N' := by
    have e := dimVec_sup_add_inf N N'
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have ei : ((dimVec (N ⊔ N') i : ℕ) : K) + dimVec (N ⊓ N') i = dimVec N i + dimVec N' i := by
      exact_mod_cast congrFun e i
    rw [← mul_add, ← mul_add, ei]

variable (M : DoubledRep k Q V)

lemma chargeFunction_rk {r d : I → K} (h : ∀ i, 0 < r i ∨ (r i = 0 ∧ 0 < d i)) (N : M.subreps) :
    (M.chargeFunction r d h).rk N = ∑ i, r i * dimVec N i :=
  rfl

lemma chargeFunction_deg {r d : I → K} (h : ∀ i, 0 < r i ∨ (r i = 0 ∧ 0 < d i))
    (N : M.subreps) : (M.chargeFunction r d h).deg N = ∑ i, d i * dimVec N i :=
  rfl

/-- The charge of a subrepresentation takes finitely many values: the dimension vector is
bounded by that of `M`. -/
theorem finite_range_chargeFunction {r d : I → K} (h : ∀ i, 0 < r i ∨ (r i = 0 ∧ 0 < d i)) :
    (Set.range fun N ↦ ((M.chargeFunction r d h).rk N, (M.chargeFunction r d h).deg N)).Finite := by
  classical
  refine ((Set.Finite.pi (t := fun i ↦ Set.Iic (finrank k (V i)))
      fun i ↦ Set.finite_Iic _).image
    fun v : I → ℕ ↦ (∑ i, r i * (v i : K), ∑ i, d i * (v i : K))).subset ?_
  rintro _ ⟨N, rfl⟩
  refine ⟨dimVec N, fun i _ ↦ ?_, rfl⟩
  have := dimVec_mono (le_top : N ≤ ⊤) i
  rw [dimVec_top] at this
  exact this

/-- The subrepresentations of a finite-dimensional representation satisfy the ascending chain
condition. -/
instance : WellFoundedGT M.subreps :=
  ChargeFunction.wellFoundedGT_of_finite_range
    (M.chargeFunction (K := ℚ) (fun _ ↦ 1) (fun _ ↦ 0) (fun _ ↦ Or.inl one_pos))
    (M.finite_range_chargeFunction _)

/-- **Every charge has a Harder–Narasimhan filtration** on the subrepresentations of a
finite-dimensional representation, by the existence theorem for charge functions. By
`Order.ChargeFunction.HNChain.instSubsingleton` it is unique. -/
theorem nonempty_hnFiltration {r d : I → K} (h : ∀ i, 0 < r i ∨ (r i = 0 ∧ 0 < d i)) :
    Nonempty (M.chargeFunction r d h).HNFiltration :=
  (M.chargeFunction r d h).nonempty_hnFiltration_of_finite_range
    (M.finite_range_chargeFunction h)

end Charge

end DoubledRep

end Quiver.Preprojective
