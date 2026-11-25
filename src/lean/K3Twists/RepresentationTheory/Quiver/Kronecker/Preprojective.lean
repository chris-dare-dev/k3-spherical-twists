/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Order.CompleteSublattice

/-!
# Representations of the doubled Kronecker quiver

The doubled Kronecker quiver with arrow set `ι` has two vertices `0, 1`, arrows `a_i : 0 → 1`
and `b_i : 1 → 0` for `i : ι`. A representation over a field `k` on vector spaces `V₀, V₁` is a
family of linear maps `A_i : V₀ → V₁` and `B_i : V₁ → V₀`. The preprojective relations are

  `∑ i, B_i A_i = 0` and `∑ i, A_i B_i = 0`.

## Main definitions

* `Quiver.Kronecker.DoubledRep k ι V₀ V₁`: the maps `A_i`, `B_i`;
* `DoubledRep.IsPreprojective`: the two relations;
* `DoubledRep.IsNilpotent`: every path of length at least some `n` acts by zero;
* `DoubledRep.Hom M N`: the morphisms, pairs of linear maps intertwining the arrows, as a
  `k`-subspace; `dim End M` is `finrank k (Hom M M)`;
* `DoubledRep.subreps M`: the subrepresentations, pairs of subspaces `(U₀, U₁)` with
  `A_i U₀ ⊆ U₁` and `B_i U₁ ⊆ U₀`, a complete sublattice of `Submodule k V₀ × Submodule k V₁`;
* `DoubledRep.dimVec`: the dimension vector `(dim U₀, dim U₁)` of a subrepresentation;
* `DoubledRep.Iso`, `DoubledRep.Iso.mapSubrep`: isomorphisms of representations, and the
  isomorphism of lattices of subrepresentations they induce, which preserves dimension vectors.

## Main results

* `DoubledRep.dimVec_sup_add_inf`: the dimension vector is a valuation on subrepresentations,
  `d(N ⊔ N') + d(N ⊓ N') = d(N) + d(N')`;
* `DoubledRep.totalDim_lt_of_lt`: a strictly larger subrepresentation has strictly larger total
  dimension.

## The wall model

Let two spherical objects `S₀, S₁` of a K3 category become stable of one phase on a wall, with
`g = ext¹(S₀, S₁)`. Choosing dual bases of `Ext¹(S₀, S₁)` and `Ext¹(S₁, S₀)`, the iterated
extensions of `S₀` and `S₁` are the nilpotent representations of the doubled `g`-Kronecker
quiver satisfying the preprojective relations: an iterated extension is a twisted complex whose
differential is given by the arrows, its square vanishes by the relations (which come from the
Serre pairing), and the comparison is an equivalence because the `Ext`-algebra of the two spheres
is formal (Davison, arXiv:2106.07692, Proposition 7.8). A subobject of a wall object with
multiplicities `(i, j)` in `S₀, S₁` is then a subrepresentation of dimension vector `(i, j)`.
This equivalence is not formalized; statements that use it take it as a hypothesis.

## Implementation notes

Quiver representations are not in Mathlib. The file sits under `RepresentationTheory/`, the home
of Mathlib's representations and subrepresentations, and uses the namespace `Quiver.Kronecker` of
the real roots of the Kronecker quiver. A representation is a family of maps on given spaces, not
a bundled object of a category: the abelian category of representations (modules over the
preprojective algebra) is not built here, only the morphism spaces and the subobject lattice of a
representation, which is what the wall lemmas use.
-/

namespace Quiver.Kronecker

open Module

variable (k : Type*) [Field k] (ι : Type*) (V₀ V₁ : Type*) [AddCommGroup V₀] [Module k V₀]
  [AddCommGroup V₁] [Module k V₁]

/-- A representation of the doubled Kronecker quiver with arrow set `ι` on the spaces `V₀, V₁`:
linear maps `A i : V₀ → V₁` and `B i : V₁ → V₀`. -/
structure DoubledRep where
  /-- The arrows from vertex zero to vertex one. -/
  A : ι → V₀ →ₗ[k] V₁
  /-- The arrows from vertex one to vertex zero. -/
  B : ι → V₁ →ₗ[k] V₀

namespace DoubledRep

variable {k ι V₀ V₁}

/-- The preprojective relations `∑ B_i A_i = 0` and `∑ A_i B_i = 0`. -/
def IsPreprojective [Fintype ι] (M : DoubledRep k ι V₀ V₁) : Prop :=
  ∑ i, M.B i ∘ₗ M.A i = 0 ∧ ∑ i, M.A i ∘ₗ M.B i = 0

/-- The arrows as endomorphisms of `V₀ × V₁`: `Sum.inl i` acts by `A i` and `Sum.inr i` by
`B i`. A path is a product of arrows. -/
def arrow (M : DoubledRep k ι V₀ V₁) : ι ⊕ ι → Module.End k (V₀ × V₁)
  | .inl i => LinearMap.inr k V₀ V₁ ∘ₗ M.A i ∘ₗ LinearMap.fst k V₀ V₁
  | .inr i => LinearMap.inl k V₀ V₁ ∘ₗ M.B i ∘ₗ LinearMap.snd k V₀ V₁

@[simp]
lemma arrow_inl_apply (M : DoubledRep k ι V₀ V₁) (i : ι) (x : V₀ × V₁) :
    M.arrow (.inl i) x = (0, M.A i x.1) := rfl

@[simp]
lemma arrow_inr_apply (M : DoubledRep k ι V₀ V₁) (i : ι) (x : V₀ × V₁) :
    M.arrow (.inr i) x = (M.B i x.2, 0) := rfl

/-- A representation is nilpotent when every path of length at least some `n` acts by zero: the
product of the arrows along any word `w` with `n ≤ w.length` vanishes. -/
def IsNilpotent (M : DoubledRep k ι V₀ V₁) : Prop :=
  ∃ n : ℕ, ∀ w : List (ι ⊕ ι), n ≤ w.length → (w.map M.arrow).prod = 0

section Hom

variable {W₀ W₁ : Type*} [AddCommGroup W₀] [Module k W₀] [AddCommGroup W₁] [Module k W₁]

/-- The morphisms `M → N`: pairs `(f₀, f₁)` with `f₁ A_i = A_i f₀` and `f₀ B_i = B_i f₁` for
every `i`. They form a `k`-subspace of `(V₀ →ₗ W₀) × (V₁ →ₗ W₁)`. -/
def Hom (M : DoubledRep k ι V₀ V₁) (N : DoubledRep k ι W₀ W₁) :
    Submodule k ((V₀ →ₗ[k] W₀) × (V₁ →ₗ[k] W₁)) where
  carrier := {f | ∀ i, f.2 ∘ₗ M.A i = N.A i ∘ₗ f.1 ∧ f.1 ∘ₗ M.B i = N.B i ∘ₗ f.2}
  add_mem' {f g} hf hg i := by
    simp only [Prod.fst_add, Prod.snd_add, LinearMap.add_comp, LinearMap.comp_add, (hf i).1,
      (hf i).2, (hg i).1, (hg i).2, and_self]
  zero_mem' i := by simp
  smul_mem' c f hf i := by
    simp only [Prod.smul_fst, Prod.smul_snd, LinearMap.smul_comp, LinearMap.comp_smul, (hf i).1,
      (hf i).2, and_self]

lemma mem_Hom {M : DoubledRep k ι V₀ V₁} {N : DoubledRep k ι W₀ W₁}
    {f : (V₀ →ₗ[k] W₀) × (V₁ →ₗ[k] W₁)} :
    f ∈ Hom M N ↔ ∀ i, f.2 ∘ₗ M.A i = N.A i ∘ₗ f.1 ∧ f.1 ∘ₗ M.B i = N.B i ∘ₗ f.2 :=
  Iff.rfl

end Hom

section Subrep

/-- A pair of subspaces `(U₀, U₁)` is a subrepresentation of `M` when every `A i` maps `U₀` into
`U₁` and every `B i` maps `U₁` into `U₀`. -/
def IsSubrep (M : DoubledRep k ι V₀ V₁) (p : Submodule k V₀ × Submodule k V₁) : Prop :=
  ∀ i, p.1 ≤ p.2.comap (M.A i) ∧ p.2 ≤ p.1.comap (M.B i)

/-- The subrepresentations of `M`, a complete sublattice of the pairs of subspaces. -/
def subreps (M : DoubledRep k ι V₀ V₁) : CompleteSublattice (Submodule k V₀ × Submodule k V₁) :=
  CompleteSublattice.mk' {p | M.IsSubrep p}
    (fun s hs i ↦ by
      rw [Prod.fst_sSup, Prod.snd_sSup]
      refine ⟨sSup_le ?_, sSup_le ?_⟩
      · rintro _ ⟨p, hp, rfl⟩
        exact ((hs hp) i).1.trans (Submodule.comap_mono (le_sSup ⟨p, hp, rfl⟩))
      · rintro _ ⟨p, hp, rfl⟩
        exact ((hs hp) i).2.trans (Submodule.comap_mono (le_sSup ⟨p, hp, rfl⟩)))
    (fun s hs i ↦ by
      rw [Prod.fst_sInf, Prod.snd_sInf]
      refine ⟨fun x hx ↦ ?_, fun y hy ↦ ?_⟩
      · rw [Submodule.mem_comap, Submodule.mem_sInf]
        rintro _ ⟨p, hp, rfl⟩
        exact ((hs hp) i).1 (Submodule.mem_sInf.mp hx p.1 ⟨p, hp, rfl⟩)
      · rw [Submodule.mem_comap, Submodule.mem_sInf]
        rintro _ ⟨p, hp, rfl⟩
        exact ((hs hp) i).2 (Submodule.mem_sInf.mp hy p.2 ⟨p, hp, rfl⟩))

variable {M : DoubledRep k ι V₀ V₁}

lemma mem_subreps {p : Submodule k V₀ × Submodule k V₁} : p ∈ M.subreps ↔ M.IsSubrep p :=
  Iff.rfl

lemma A_mem (N : M.subreps) (i : ι) {x : V₀}
    (hx : x ∈ (N : Submodule k V₀ × Submodule k V₁).1) :
    M.A i x ∈ (N : Submodule k V₀ × Submodule k V₁).2 :=
  (N.2 i).1 hx

lemma B_mem (N : M.subreps) (i : ι) {y : V₁}
    (hy : y ∈ (N : Submodule k V₀ × Submodule k V₁).2) :
    M.B i y ∈ (N : Submodule k V₀ × Submodule k V₁).1 :=
  (N.2 i).2 hy

@[simp]
lemma coe_sup_fst (N N' : M.subreps) :
    ((N ⊔ N' : M.subreps) : Submodule k V₀ × Submodule k V₁).1 =
      (N : Submodule k V₀ × Submodule k V₁).1 ⊔ (N' : Submodule k V₀ × Submodule k V₁).1 :=
  rfl

@[simp]
lemma coe_sup_snd (N N' : M.subreps) :
    ((N ⊔ N' : M.subreps) : Submodule k V₀ × Submodule k V₁).2 =
      (N : Submodule k V₀ × Submodule k V₁).2 ⊔ (N' : Submodule k V₀ × Submodule k V₁).2 :=
  rfl

@[simp]
lemma coe_inf_fst (N N' : M.subreps) :
    ((N ⊓ N' : M.subreps) : Submodule k V₀ × Submodule k V₁).1 =
      (N : Submodule k V₀ × Submodule k V₁).1 ⊓ (N' : Submodule k V₀ × Submodule k V₁).1 :=
  rfl

@[simp]
lemma coe_inf_snd (N N' : M.subreps) :
    ((N ⊓ N' : M.subreps) : Submodule k V₀ × Submodule k V₁).2 =
      (N : Submodule k V₀ × Submodule k V₁).2 ⊓ (N' : Submodule k V₀ × Submodule k V₁).2 :=
  rfl

/-- The dimension vector `(dim U₀, dim U₁)` of a subrepresentation `(U₀, U₁)`. -/
noncomputable def dimVec (N : M.subreps) : ℕ × ℕ :=
  (finrank k (N : Submodule k V₀ × Submodule k V₁).1,
    finrank k (N : Submodule k V₀ × Submodule k V₁).2)

@[simp]
lemma dimVec_bot : dimVec (⊥ : M.subreps) = (0, 0) := by
  simp [dimVec]

@[simp]
lemma dimVec_top : dimVec (⊤ : M.subreps) = (finrank k V₀, finrank k V₁) := by
  simp [dimVec]

variable [FiniteDimensional k V₀] [FiniteDimensional k V₁]

/-- The dimension vector is a valuation on the lattice of subrepresentations. -/
theorem dimVec_sup_add_inf (N N' : M.subreps) :
    dimVec (N ⊔ N') + dimVec (N ⊓ N') = dimVec N + dimVec N' := by
  simp only [dimVec, coe_sup_fst, coe_sup_snd, coe_inf_fst, coe_inf_snd, Prod.mk_add_mk,
    Submodule.finrank_sup_add_finrank_inf_eq]

lemma dimVec_mono {N N' : M.subreps} (h : N ≤ N') :
    (dimVec N).1 ≤ (dimVec N').1 ∧ (dimVec N).2 ≤ (dimVec N').2 :=
  ⟨Submodule.finrank_mono (Prod.mk_le_mk.mp h).1, Submodule.finrank_mono (Prod.mk_le_mk.mp h).2⟩

/-- A strictly larger subrepresentation has strictly larger total dimension. -/
theorem totalDim_lt_of_lt {N N' : M.subreps} (h : N < N') :
    (dimVec N).1 + (dimVec N).2 < (dimVec N').1 + (dimVec N').2 := by
  have h' : (N : Submodule k V₀ × Submodule k V₁) < N' := h
  rw [Prod.lt_iff] at h'
  rcases h' with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
  · exact Nat.add_lt_add_of_lt_of_le (Submodule.finrank_lt_finrank_of_lt h₀)
      (Submodule.finrank_mono h₁)
  · exact Nat.add_lt_add_of_le_of_lt (Submodule.finrank_mono h₀)
      (Submodule.finrank_lt_finrank_of_lt h₁)

/-- A subrepresentation is determined, among those containing it, by its dimension vector. -/
theorem eq_of_le_of_dimVec_eq {N N' : M.subreps} (h : N ≤ N') (hd : dimVec N = dimVec N') :
    N = N' := by
  by_contra hne
  have := totalDim_lt_of_lt (lt_of_le_of_ne h hne)
  rw [hd] at this
  exact lt_irrefl _ this

end Subrep

section Iso

variable {W₀ W₁ : Type*} [AddCommGroup W₀] [Module k W₀] [AddCommGroup W₁] [Module k W₁]

/-- An isomorphism of representations: linear equivalences at the two vertices commuting with
every arrow. -/
structure Iso (M : DoubledRep k ι V₀ V₁) (N : DoubledRep k ι W₀ W₁) where
  /-- The equivalence at vertex zero. -/
  e₀ : V₀ ≃ₗ[k] W₀
  /-- The equivalence at vertex one. -/
  e₁ : V₁ ≃ₗ[k] W₁
  comm_A (i : ι) (x : V₀) : e₁ (M.A i x) = N.A i (e₀ x)
  comm_B (i : ι) (y : V₁) : e₀ (M.B i y) = N.B i (e₁ y)

namespace Iso

variable {M : DoubledRep k ι V₀ V₁} {N : DoubledRep k ι W₀ W₁}

/-- An isomorphism of representations induces an isomorphism of the lattices of
subrepresentations, `(U₀, U₁) ↦ (e₀ U₀, e₁ U₁)`. -/
def mapSubrep (u : Iso M N) : M.subreps ≃o N.subreps where
  toFun P := ⟨((P : Submodule k V₀ × Submodule k V₁).1.map (u.e₀ : V₀ →ₗ[k] W₀),
      (P : Submodule k V₀ × Submodule k V₁).2.map (u.e₁ : V₁ →ₗ[k] W₁)), fun i ↦ ⟨by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨M.A i x, A_mem P i hx, u.comm_A i x⟩, by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨M.B i y, B_mem P i hy, u.comm_B i y⟩⟩⟩
  invFun Q := ⟨((Q : Submodule k W₀ × Submodule k W₁).1.comap (u.e₀ : V₀ →ₗ[k] W₀),
      (Q : Submodule k W₀ × Submodule k W₁).2.comap (u.e₁ : V₁ →ₗ[k] W₁)), fun i ↦ ⟨by
    intro x hx
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at hx ⊢
    rw [u.comm_A]
    exact A_mem Q i hx, by
    intro y hy
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at hy ⊢
    rw [u.comm_B]
    exact B_mem Q i hy⟩⟩
  left_inv P := Subtype.ext (Prod.ext
    (Submodule.comap_map_eq_of_injective u.e₀.injective _)
    (Submodule.comap_map_eq_of_injective u.e₁.injective _))
  right_inv Q := Subtype.ext (Prod.ext
    (Submodule.map_comap_eq_of_surjective u.e₀.surjective _)
    (Submodule.map_comap_eq_of_surjective u.e₁.surjective _))
  map_rel_iff' {P Q} := by
    change ((P : Submodule k V₀ × Submodule k V₁).1.map (u.e₀ : V₀ →ₗ[k] W₀),
        (P : Submodule k V₀ × Submodule k V₁).2.map (u.e₁ : V₁ →ₗ[k] W₁)) ≤
      ((Q : Submodule k V₀ × Submodule k V₁).1.map (u.e₀ : V₀ →ₗ[k] W₀),
        (Q : Submodule k V₀ × Submodule k V₁).2.map (u.e₁ : V₁ →ₗ[k] W₁)) ↔
      (P : Submodule k V₀ × Submodule k V₁) ≤ Q
    rw [Prod.mk_le_mk, Submodule.map_le_map_iff_of_injective u.e₀.injective,
      Submodule.map_le_map_iff_of_injective u.e₁.injective]
    rfl

lemma coe_mapSubrep (u : Iso M N) (P : M.subreps) :
    (u.mapSubrep P : Submodule k W₀ × Submodule k W₁) =
      ((P : Submodule k V₀ × Submodule k V₁).1.map (u.e₀ : V₀ →ₗ[k] W₀),
        (P : Submodule k V₀ × Submodule k V₁).2.map (u.e₁ : V₁ →ₗ[k] W₁)) := rfl

/-- An isomorphism preserves dimension vectors of subrepresentations. -/
lemma dimVec_mapSubrep (u : Iso M N) (P : M.subreps) : dimVec (u.mapSubrep P) = dimVec P :=
  Prod.ext (LinearEquiv.finrank_map_eq u.e₀ _) (LinearEquiv.finrank_map_eq u.e₁ _)

end Iso

end Iso

end DoubledRep

end Quiver.Kronecker
