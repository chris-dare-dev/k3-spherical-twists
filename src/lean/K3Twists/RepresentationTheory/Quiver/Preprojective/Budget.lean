/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.RepresentationTheory.Quiver.Preprojective.CrawleyBoevey
import Mathlib.LinearAlgebra.Projection

/-!
# Extensions and the Mukai budget in the general wall model

For representations `A` on `V i` and `B` on `W i` of the double of a quiver `Q` (loops allowed)
and a one-cochain `ξ` of `(B, A)`, the **extension** `N = extension A B ξ` is the representation
on `V i × W i` with block upper triangular arrows `[[A_a, ξ_a], [0, B_a]]`. It satisfies the
preprojective relations exactly when `A` and `B` do and `ξ` is a cocycle
(`DoubledRep.isPreprojective_extension_iff`), and every representation with a subrepresentation
`P` is isomorphic to such an extension of `M ⧸ P` by `M|P` (`DoubledRep.exists_iso_extension`).

**Mukai's inequality in the model** (`DoubledRep.selfExtDim_add_le_add`):

  `e(A) + e(B) ≤ e(N) + 2 dim Hom(A, B)`,

so `e(A) + e(B) ≤ e(N)` when `Hom(A, B) = 0` (`DoubledRep.selfExtDim_add_le`; Bayer–Bridgeland,
arXiv:1310.8266, Lemma 2.5, for the triangulated statement). The proof is a dimension count. A
block upper triangular map `[[a, h], [0, b]]` with `a ∈ End A`, `b ∈ End B` is an endomorphism of
`N` exactly when `a ξ - ξ b = d₀ h`, so `dim End N` is at least the dimension of the kernel of
`(a, b, h) ↦ a ξ - ξ b - d₀ h`, whose image lies in the cocycles `Z¹(B, A)`
(`DoubledRep.finrank_ker_orbitMap_le`). Crawley-Boevey's formula for `(N, N)`, `(A, A)`, `(B, B)`
and `(B, A)` turns this into the inequality. The doubled Kronecker quiver
(`Quiver.Kronecker.DoubledRep.finrank_Ext1_extension`) has the equality with its defect; the
inequality is what the budget needs, and it holds with no hypothesis on `Hom(A, B)` once
`2 dim Hom(A, B)` is added.

**The Mukai budget lemma in the model** (`DoubledRep.sum_selfExtDim_subquotient_le`): along a flag
`0 = M_0 ≤ M_1 ≤ ⋯ ≤ M_n = M` of subrepresentations whose prefixes have no nonzero maps to the
next subquotient (a Hom-orthogonal tower), `∑_j e(M_{j+1}/M_j) ≤ e(M)`. This is model
superadditivity; it is stated for Hom-orthogonal towers, the hypothesis Mukai's lemma needs, and
it is a separate statement from the one-copy identity of the Kronecker model.

## Main definitions

* `DoubledRep.extension A B ξ`: the extension with class `ξ`;
* `DoubledRep.orbitMap`, `DoubledRep.blockMap`: the maps of the dimension count.

## Main results

* `DoubledRep.isPreprojective_extension_iff`, `DoubledRep.exists_iso_extension`;
* `DoubledRep.selfExtDim_add_le_add`, `DoubledRep.selfExtDim_add_le`: Mukai's inequality;
* `DoubledRep.selfExtDim_restrict_add_le`: one step of the budget, for subrepresentations;
* `DoubledRep.sum_selfExtDim_subquotient_le`: the budget along Hom-orthogonal flags.
-/

namespace Quiver.Preprojective.DoubledRep

open Module

variable {k : Type*} [Field k] {I : Type*} {Q : I → I → Type*}

/-! ### Block upper triangular maps -/

section Triangular

variable {V W V' W' : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup V'] [Module k V'] [AddCommGroup W'] [Module k W']

/-- The block upper triangular map `[[P, R], [0, S]] : V × W → V' × W'`,
`(x, y) ↦ (P x + R y, S y)`. -/
def triangular (P : V →ₗ[k] V') (R : W →ₗ[k] V') (S : W →ₗ[k] W') : V × W →ₗ[k] V' × W' :=
  (P.coprod R).prod (S ∘ₗ LinearMap.snd k V W)

@[simp]
lemma triangular_apply (P : V →ₗ[k] V') (R : W →ₗ[k] V') (S : W →ₗ[k] W') (x : V × W) :
    triangular P R S x = (P x.1 + R x.2, S x.2) :=
  rfl

end Triangular

/-! ### Extensions -/

section Extension

variable {V W : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)]
  (A : DoubledRep k Q V) (B : DoubledRep k Q W)

/-- The extension of `B` by `A` with class `ξ`: the representation on `V i × W i` with block upper
triangular arrows `[[A_a, ξ_a], [0, B_a]]`. -/
def extension (ξ : Cochain₁ k Q W V) : DoubledRep k Q (fun i ↦ V i × W i) where
  A a := triangular (A.A a) (ξ.1 _ _ a) (B.A a)
  B a := triangular (A.B a) (ξ.2 _ _ a) (B.B a)

variable (ξ : Cochain₁ k Q W V)

@[simp]
lemma extension_A_apply {i j : I} (a : Q i j) (x : V i × W i) :
    (extension A B ξ).A a x = (A.A a x.1 + ξ.1 i j a x.2, B.A a x.2) :=
  rfl

@[simp]
lemma extension_B_apply {i j : I} (a : Q i j) (x : V j × W j) :
    (extension A B ξ).B a x = (A.B a x.1 + ξ.2 i j a x.2, B.B a x.2) :=
  rfl

/-- The inclusion `A → N` of the extension is a morphism. -/
lemma inl_mem_Hom : (fun i ↦ LinearMap.inl k (V i) (W i)) ∈ Hom A (extension A B ξ) :=
  fun _ _ _ ↦ ⟨LinearMap.ext fun x ↦ by simp, LinearMap.ext fun y ↦ by simp⟩

/-- The projection `N → B` of the extension is a morphism. -/
lemma snd_mem_Hom : (fun i ↦ LinearMap.snd k (V i) (W i)) ∈ Hom (extension A B ξ) B :=
  fun _ _ _ ↦ ⟨LinearMap.ext fun x ↦ by simp, LinearMap.ext fun y ↦ by simp⟩

variable [Fintype I] [∀ i j, Fintype (Q i j)]

/-- The relation of the extension: its diagonal blocks are the relations of `A` and `B`, and its
off-diagonal block is `d₁ ξ`. -/
lemma extension_relation_apply (i : I) (x : V i × W i) :
    (extension A B ξ).relation i x =
      (A.relation i x.1 + d₁ B A ξ i x.2, B.relation i x.2) := by
  refine Prod.ext ?_ ?_
  · simp only [relation_apply, extension_A_apply, extension_B_apply, Prod.fst_sub,
      Prod.fst_sum, map_add, d₁_apply, LinearMap.sub_apply, LinearMap.sum_apply,
      LinearMap.add_apply, LinearMap.comp_apply, Finset.sum_add_distrib]
    abel
  · simp only [relation_apply, extension_A_apply, extension_B_apply, Prod.snd_sub, Prod.snd_sum]

/-- **An extension satisfies the preprojective relations exactly when `A` and `B` do and its
class is a cocycle.** -/
theorem isPreprojective_extension_iff :
    (extension A B ξ).IsPreprojective ↔
      A.IsPreprojective ∧ B.IsPreprojective ∧ ξ ∈ cocycles B A := by
  constructor
  · intro hN
    have e := fun i x ↦ (extension_relation_apply A B ξ i x).symm.trans
      (LinearMap.congr_fun (hN i) x)
    refine ⟨fun i ↦ LinearMap.ext fun x ↦ ?_, fun i ↦ LinearMap.ext fun y ↦ ?_, ?_⟩
    · simpa using congrArg Prod.fst (e i (x, 0))
    · simpa using congrArg Prod.snd (e i (0, y))
    · rw [mem_cocycles]
      refine funext fun i ↦ LinearMap.ext fun y ↦ ?_
      simpa using congrArg Prod.fst (e i (0, y))
  · rintro ⟨hA, hB, hξ⟩
    rw [mem_cocycles] at hξ
    intro i
    refine LinearMap.ext fun x ↦ ?_
    rw [extension_relation_apply, hA i, hB i, hξ]
    simp

end Extension

/-! ### Endomorphisms of an extension -/

section Orbit

variable {V W : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)]
  (A : DoubledRep k Q V) (B : DoubledRep k Q W) (ξ : Cochain₁ k Q W V)

/-- The map `(a, b, h) ↦ a ξ - ξ b - d₀ h` from `End A × End B × C⁰(B, A)` to the one-cochains of
`(B, A)`. Its kernel is the set of block upper triangular endomorphisms of the extension
(`DoubledRep.blockMap_mem_Hom`). -/
def orbitMap : (Hom A A × Hom B B × Cochain₀ k W V) →ₗ[k] Cochain₁ k Q W V where
  toFun x := (fun i j a ↦ (x.1 : Cochain₀ k V V) j ∘ₗ ξ.1 i j a -
      ξ.1 i j a ∘ₗ (x.2.1 : Cochain₀ k W W) i,
    fun i j a ↦ (x.1 : Cochain₀ k V V) i ∘ₗ ξ.2 i j a -
      ξ.2 i j a ∘ₗ (x.2.1 : Cochain₀ k W W) j) - d₀ B A x.2.2
  map_add' x y := by
    refine Prod.ext (funext fun i ↦ funext fun j ↦ funext fun a ↦ ?_)
      (funext fun i ↦ funext fun j ↦ funext fun a ↦ ?_) <;>
    · simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Submodule.coe_add,
        Pi.add_apply, Pi.sub_apply, LinearMap.add_comp, LinearMap.comp_add, map_add]
      abel
  map_smul' c x := by
    refine Prod.ext (funext fun i ↦ funext fun j ↦ funext fun a ↦ ?_)
      (funext fun i ↦ funext fun j ↦ funext fun a ↦ ?_) <;>
    · simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub, Submodule.coe_smul,
        Pi.smul_apply, Pi.sub_apply, LinearMap.smul_comp, LinearMap.comp_smul, map_smul,
        RingHom.id_apply, smul_sub]

lemma orbitMap_apply_fst (x : Hom A A × Hom B B × Cochain₀ k W V) (i j : I) (a : Q i j) :
    (orbitMap A B ξ x).1 i j a = (x.1 : Cochain₀ k V V) j ∘ₗ ξ.1 i j a -
      ξ.1 i j a ∘ₗ (x.2.1 : Cochain₀ k W W) i - (A.A a ∘ₗ x.2.2 i - x.2.2 j ∘ₗ B.A a) :=
  rfl

lemma orbitMap_apply_snd (x : Hom A A × Hom B B × Cochain₀ k W V) (i j : I) (a : Q i j) :
    (orbitMap A B ξ x).2 i j a = (x.1 : Cochain₀ k V V) i ∘ₗ ξ.2 i j a -
      ξ.2 i j a ∘ₗ (x.2.1 : Cochain₀ k W W) j - (A.B a ∘ₗ x.2.2 j - x.2.2 i ∘ₗ B.B a) :=
  rfl

/-- The block upper triangular maps `[[a, h], [0, b]]` at the vertices. -/
def blockMap :
    (Hom A A × Hom B B × Cochain₀ k W V) →ₗ[k]
      Cochain₀ k (fun i ↦ V i × W i) (fun i ↦ V i × W i) where
  toFun x i := triangular ((x.1 : Cochain₀ k V V) i) (x.2.2 i) ((x.2.1 : Cochain₀ k W W) i)
  map_add' x y := by
    funext i
    refine LinearMap.ext fun z ↦ Prod.ext ?_ ?_
    · simp only [triangular_apply, Prod.fst_add, Prod.snd_add, Submodule.coe_add, Pi.add_apply,
        LinearMap.add_apply]
      abel
    · simp only [triangular_apply, Prod.snd_add, Prod.fst_add, Submodule.coe_add, Pi.add_apply,
        LinearMap.add_apply]
  map_smul' c x := by
    funext i
    refine LinearMap.ext fun z ↦ Prod.ext ?_ ?_
    · simp only [triangular_apply, Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul,
        Pi.smul_apply, LinearMap.smul_apply, RingHom.id_apply, smul_add]
    · simp only [triangular_apply, Prod.smul_snd, Prod.smul_fst, Submodule.coe_smul,
        Pi.smul_apply, LinearMap.smul_apply, RingHom.id_apply]

lemma blockMap_apply (x : Hom A A × Hom B B × Cochain₀ k W V) (i : I) :
    blockMap A B x i =
      triangular ((x.1 : Cochain₀ k V V) i) (x.2.2 i) ((x.2.1 : Cochain₀ k W W) i) :=
  rfl

variable {A B} in
lemma blockMap_injective : Function.Injective (blockMap A B) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, h⟩ hx
  rw [LinearMap.mem_ker] at hx
  have e := fun i z ↦ LinearMap.congr_fun (congrFun hx i) z
  simp only [blockMap_apply, triangular_apply, Pi.zero_apply, LinearMap.zero_apply,
    Prod.mk_eq_zero] at e
  refine Prod.ext (Subtype.ext (funext fun i ↦ LinearMap.ext fun v ↦ ?_))
    (Prod.ext (Subtype.ext (funext fun i ↦ LinearMap.ext fun w ↦ ?_))
      (funext fun i ↦ LinearMap.ext fun w ↦ ?_))
  · simpa using (e i (v, 0)).1
  · simpa using (e i (0, w)).2
  · simpa using (e i (0, w)).1

/-- **Block upper triangular endomorphisms.** If `a ξ - ξ b = d₀ h`, then `[[a, h], [0, b]]` is an
endomorphism of the extension. -/
theorem blockMap_mem_Hom {x : Hom A A × Hom B B × Cochain₀ k W V}
    (hx : x ∈ LinearMap.ker (orbitMap A B ξ)) :
    blockMap A B x ∈ Hom (extension A B ξ) (extension A B ξ) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, h⟩ := x
  rw [LinearMap.mem_ker] at hx
  have h₁ : ∀ i j (q : Q i j) (w : W i),
      a j (ξ.1 i j q w) - ξ.1 i j q (b i w) - (A.A q (h i w) - h j (B.A q w)) = 0 :=
    fun i j q w ↦ by simpa [orbitMap_apply_fst] using LinearMap.congr_fun (congrFun (congrFun
      (congrFun (congrArg Prod.fst hx) i) j) q) w
  have h₂ : ∀ i j (q : Q i j) (w : W j),
      a i (ξ.2 i j q w) - ξ.2 i j q (b j w) - (A.B q (h j w) - h i (B.B q w)) = 0 :=
    fun i j q w ↦ by simpa [orbitMap_apply_snd] using LinearMap.congr_fun (congrFun (congrFun
      (congrFun (congrArg Prod.snd hx) i) j) q) w
  refine fun i j q ↦ ⟨LinearMap.ext fun z ↦ Prod.ext ?_ ?_, LinearMap.ext fun z ↦ Prod.ext ?_ ?_⟩
  · have hA := LinearMap.congr_fun (ha i j q).1 z.1
    simp only [LinearMap.comp_apply] at hA
    simp only [LinearMap.comp_apply, blockMap_apply, triangular_apply, extension_A_apply,
      map_add, hA]
    have := h₁ i j q z.2
    rw [sub_eq_zero] at this
    rw [← sub_eq_zero]
    rw [← sub_eq_zero] at this
    rw [← this]
    abel
  · have hB := LinearMap.congr_fun (hb i j q).1 z.2
    simpa [blockMap_apply, triangular_apply, extension_A_apply] using hB
  · have hA := LinearMap.congr_fun (ha i j q).2 z.1
    simp only [LinearMap.comp_apply] at hA
    simp only [LinearMap.comp_apply, blockMap_apply, triangular_apply, extension_B_apply,
      map_add, hA]
    have := h₂ i j q z.2
    rw [← sub_eq_zero]
    rw [← this]
    abel
  · have hB := LinearMap.congr_fun (hb i j q).2 z.2
    simpa [blockMap_apply, triangular_apply, extension_B_apply] using hB

variable [Fintype I] [∀ i j, Fintype (Q i j)]

variable {A B ξ} in
/-- The image of `orbitMap` consists of cocycles. -/
theorem range_orbitMap_le (hA : A.IsPreprojective) (hB : B.IsPreprojective)
    (hξ : ξ ∈ cocycles B A) : LinearMap.range (orbitMap A B ξ) ≤ cocycles B A := by
  rintro _ ⟨⟨⟨a, ha⟩, ⟨b, hb⟩, h⟩, rfl⟩
  have e : orbitMap A B ξ (⟨a, ha⟩, ⟨b, hb⟩, h) =
      map₁ (fun _ ↦ LinearMap.id) a ξ - map₁ b (fun _ ↦ LinearMap.id) ξ - d₀ B A h := by
    refine Prod.ext (funext fun i ↦ funext fun j ↦ funext fun q ↦ ?_)
      (funext fun i ↦ funext fun j ↦ funext fun q ↦ ?_) <;>
    simp [orbitMap_apply_fst, orbitMap_apply_snd]
  have hdd := LinearMap.congr_fun (d₁_comp_d₀ hB hA) h
  rw [LinearMap.comp_apply] at hdd
  rw [e, mem_cocycles, map_sub, map_sub, d₁_map₁ (id_mem_Hom B) ha, d₁_map₁ hb (id_mem_Hom A),
    hdd, mem_cocycles.mp hξ]
  simp

variable [∀ i, FiniteDimensional k (V i)] [∀ i, FiniteDimensional k (W i)]

omit [∀ i j, Fintype (Q i j)] in
variable {A B ξ} in
/-- **The dimension count for `End N`.** `dim End N` is at least the dimension of the kernel of
`orbitMap`. -/
theorem finrank_ker_orbitMap_le :
    finrank k (LinearMap.ker (orbitMap A B ξ)) ≤
      finrank k (Hom (extension A B ξ) (extension A B ξ)) := by
  let Θ : LinearMap.ker (orbitMap A B ξ) →ₗ[k] Hom (extension A B ξ) (extension A B ξ) :=
    (blockMap A B).restrict fun x hx ↦ blockMap_mem_Hom A B ξ hx
  refine LinearMap.finrank_le_finrank_of_injective (f := Θ) fun x y hxy ↦ ?_
  exact Subtype.ext (blockMap_injective (congrArg Subtype.val hxy))

end Orbit

/-! ### Mukai's inequality -/

section Mukai

variable [Fintype I] [∀ i j, Fintype (Q i j)]

/-- The Euler form is bilinear on the diagonal: `(x + y, x + y) = (x, x) + 2 (x, y) + (y, y)`. -/
lemma eulerForm_add_add (x y : I → ℤ) :
    eulerForm Q (fun i ↦ x i + y i) (fun i ↦ x i + y i) =
      eulerForm Q x x + 2 * eulerForm Q x y + eulerForm Q y y := by
  have h := eulerForm_comm Q x y
  simp only [eulerForm] at h ⊢
  have e₁ : ∑ i, 2 * (x i + y i) * (x i + y i) =
      ∑ i, 2 * x i * x i + 2 * ∑ i, 2 * x i * y i + ∑ i, 2 * y i * y i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have e₂ : ∑ i, ∑ j, (Fintype.card (Q i j) : ℤ) * ((x i + y i) * (x j + y j) +
      (x j + y j) * (x i + y i)) =
      ∑ i, ∑ j, (Fintype.card (Q i j) : ℤ) * (x i * x j + x j * x i) +
        2 * ∑ i, ∑ j, (Fintype.card (Q i j) : ℤ) * (x i * y j + x j * y i) +
          ∑ i, ∑ j, (Fintype.card (Q i j) : ℤ) * (y i * y j + y j * y i) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [e₁, e₂]
  ring

variable {V W : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)] [∀ i, FiniteDimensional k (V i)]
  [∀ i, FiniteDimensional k (W i)] {A : DoubledRep k Q V} {B : DoubledRep k Q W}
  {ξ : Cochain₁ k Q W V}

/-- **Mukai's inequality in the model, with the Hom term.** For an extension `N` of `B` by `A`
with the preprojective relations, `e(A) + e(B) ≤ e(N) + 2 dim Hom(A, B)`. -/
theorem selfExtDim_add_le_add (hA : A.IsPreprojective) (hB : B.IsPreprojective)
    (hξ : ξ ∈ cocycles B A) :
    selfExtDim A + selfExtDim B ≤ selfExtDim (extension A B ξ) + 2 * finrank k (Hom A B) := by
  have hN := (isPreprojective_extension_iff A B ξ).mpr ⟨hA, hB, hξ⟩
  have eN := finrank_Ext1_eq hN hN
  have eA := finrank_Ext1_eq hA hA
  have eB := finrank_Ext1_eq hB hB
  have eBA := finrank_Ext1_eq hB hA
  simp only [Module.finrank_prod, Nat.cast_add] at eN
  rw [eulerForm_add_add] at eN
  rw [eulerForm_comm Q (fun i ↦ (finrank k (W i) : ℤ))] at eBA
  have e₁ : finrank k (Ext1 B A) + finrank k (coboundaries B A) =
      finrank k (cocycles B A) := by
    rw [← Submodule.finrank_quotient_add_finrank
      ((coboundaries B A).comap (cocycles B A).subtype)]
    congr 1
    exact (Submodule.comapSubtypeEquivOfLe (coboundaries_le_cocycles hB hA)).finrank_eq.symm
  have e₃ : finrank k (coboundaries B A) + finrank k (Hom B A) =
      finrank k (Cochain₀ k W V) := by
    rw [← ker_d₀]
    exact LinearMap.finrank_range_add_finrank_ker _
  have hrn : finrank k (LinearMap.range (orbitMap A B ξ)) +
      finrank k (LinearMap.ker (orbitMap A B ξ)) =
        finrank k (Hom A A × Hom B B × Cochain₀ k W V) :=
    LinearMap.finrank_range_add_finrank_ker _
  have hle : finrank k (LinearMap.range (orbitMap A B ξ)) ≤ finrank k (cocycles B A) :=
    Submodule.finrank_mono (range_orbitMap_le hA hB hξ)
  have hend := finrank_ker_orbitMap_le (A := A) (B := B) (ξ := ξ)
  simp only [Module.finrank_prod] at hrn
  rw [selfExtDim, selfExtDim, selfExtDim]
  zify at eN eA eB eBA e₁ e₃ hrn hle hend ⊢
  linarith

/-- **Mukai's inequality in the model** (Bayer–Bridgeland, arXiv:1310.8266, Lemma 2.5, for
distinguished triangles): for an extension `N` of `B` by `A` with the preprojective relations and
`Hom(A, B) = 0`, `e(A) + e(B) ≤ e(N)`. -/
theorem selfExtDim_add_le (hA : A.IsPreprojective) (hB : B.IsPreprojective)
    (hξ : ξ ∈ cocycles B A) (hAB : Hom A B = ⊥) :
    selfExtDim A + selfExtDim B ≤ selfExtDim (extension A B ξ) := by
  have h := selfExtDim_add_le_add hA hB hξ
  rwa [hAB, finrank_bot, mul_zero, add_zero] at h

end Mukai

/-! ### Splitting a subrepresentation -/

section Split

variable {V : Type*} [AddCommGroup V] [Module k V] (p q : Submodule k V) (h : IsCompl p q)

/-- The section `V ⧸ p → V` with image the complement `q`. -/
private noncomputable def quotSection : (V ⧸ p) →ₗ[k] V :=
  q.subtype ∘ₗ (p.quotientEquivOfIsCompl q h : V ⧸ p →ₗ[k] q)

private lemma mk_quotSection (z : V ⧸ p) :
    (Submodule.Quotient.mk (quotSection p q h z) : V ⧸ p) = z :=
  Submodule.mk_quotientEquivOfIsCompl_apply h z

private lemma projectionOnto_quotSection (z : V ⧸ p) :
    p.projectionOnto q h (quotSection p q h z) = 0 :=
  Submodule.projectionOnto_apply_right h _

private lemma projectionOnto_add_quotSection (x : V) :
    (p.projectionOnto q h x : V) + quotSection p q h (Submodule.Quotient.mk x) = x := by
  simp only [quotSection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Submodule.quotientEquivOfIsCompl_apply_mk, Submodule.subtype_apply,
    Submodule.coe_projectionOnto_apply]
  exact Submodule.projection_add_projection_eq_self h x

/-- A complement `q` of `p` identifies `V` with `p × V ⧸ p`, `x ↦ (π x, [x])`. -/
private noncomputable def splitEquiv : V ≃ₗ[k] p × (V ⧸ p) :=
  .ofLinearMap ((p.projectionOnto q h).prod p.mkQ) (p.subtype.coprod (quotSection p q h))
    (LinearMap.ext fun z ↦ Prod.ext (by simp [projectionOnto_quotSection])
      (by simp [(Submodule.Quotient.mk_eq_zero p).mpr z.1.2, mk_quotSection]))
    (LinearMap.ext fun x ↦ projectionOnto_add_quotSection p q h x)

private lemma splitEquiv_apply (x : V) :
    splitEquiv p q h x = (p.projectionOnto q h x, Submodule.Quotient.mk x) :=
  rfl

end Split

section Subrep

variable [Fintype I] [∀ i j, Fintype (Q i j)] {V : I → Type*} [∀ i, AddCommGroup (V i)]
  [∀ i, Module k (V i)] (M : DoubledRep k Q V)

/-- **A subrepresentation presents `M` as an extension.** For a subrepresentation `P` of `M`,
complements of the subspaces of `P` identify `M` with the extension of `M ⧸ P` by `M|P` whose class
is `ξ_a = π ∘ M_a ∘ σ`, `π` the projection to `P` and `σ` the section of `M → M ⧸ P` along the
complements; the class is a cocycle when `M` satisfies the relations. -/
theorem exists_iso_extension (P : M.subreps) (hM : M.IsPreprojective) :
    ∃ ξ ∈ cocycles (M.quotient P) (M.restrict P),
      Nonempty (Iso M (extension (M.restrict P) (M.quotient P) ξ)) := by
  choose C hC using fun i ↦ ((P : ∀ i, Submodule k (V i)) i).exists_isCompl
  let ξ : Cochain₁ k Q (fun i ↦ V i ⧸ (P : ∀ i, Submodule k (V i)) i)
      (fun i ↦ (P : ∀ i, Submodule k (V i)) i) :=
    (fun i j a ↦ ((P : ∀ i, Submodule k (V i)) j).projectionOnto (C j) (hC j) ∘ₗ M.A a ∘ₗ
        quotSection _ (C i) (hC i),
      fun i j a ↦ ((P : ∀ i, Submodule k (V i)) i).projectionOnto (C i) (hC i) ∘ₗ M.B a ∘ₗ
        quotSection _ (C j) (hC j))
  let u : Iso M (extension (M.restrict P) (M.quotient P) ξ) :=
    { e := fun i ↦ splitEquiv _ (C i) (hC i)
      comm_A := fun {i j} a x ↦ by
        refine Prod.ext ?_ rfl
        conv_lhs => rw [splitEquiv_apply, ← projectionOnto_add_quotSection _ (C i) (hC i) x]
        rw [map_add, map_add, Submodule.projectionOnto_apply_of_mem_left (hC j)
          (A_mem P a (Submodule.projectionOnto _ (C i) (hC i) x).2)]
        rfl
      comm_B := fun {i j} a y ↦ by
        refine Prod.ext ?_ rfl
        conv_lhs => rw [splitEquiv_apply, ← projectionOnto_add_quotSection _ (C j) (hC j) y]
        rw [map_add, map_add, Submodule.projectionOnto_apply_of_mem_left (hC i)
          (B_mem P a (Submodule.projectionOnto _ (C j) (hC j) y).2)]
        rfl }
  exact ⟨ξ, ((isPreprojective_extension_iff _ _ ξ).mp (u.isPreprojective hM)).2.2, ⟨u⟩⟩

end Subrep

/-! ### The budget along flags -/

section Budget

variable {V W : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)]

/-- `Hom(-, Y)` vanishes on isomorphic representations together. -/
lemma Hom_eq_bot_of_iso {V' : I → Type*} [∀ i, AddCommGroup (V' i)] [∀ i, Module k (V' i)]
    {X : DoubledRep k Q V} {X' : DoubledRep k Q V'} {Y : DoubledRep k Q W} (u : Iso X X')
    (h : Hom X' Y = ⊥) : Hom X Y = ⊥ := by
  rw [Submodule.eq_bot_iff] at h ⊢
  intro f hf
  have h0 := h _ (comp_mem_Hom u.symm.mem_Hom hf)
  refine funext fun i ↦ LinearMap.ext fun x ↦ ?_
  have := LinearMap.congr_fun (congrFun h0 i) (u.e i x)
  simpa [Iso.symm] using this

variable {M : DoubledRep k Q V}

/-- The restriction of `M` to a subrepresentation equal to `⊤` is isomorphic to `M`. -/
def restrictIsoOfEqTop {P : M.subreps} (h : P = ⊤) : Iso (M.restrict P) M where
  e i := (LinearEquiv.ofEq _ ⊤ (by rw [h]; rfl)).trans (Submodule.topEquiv)
  comm_A _ _ := rfl
  comm_B _ _ := rfl

omit [Field k] in
/-- The induction of the budget on a sequence: if `a(m) + s(m) ≤ a(m + 1)` for `m < n`, then
`a(0) + ∑_{m<n} s(m) ≤ a(n)`. -/
private theorem add_sum_le_of_step {a s : ℕ → ℕ} {n : ℕ} (h : ∀ m < n, a m + s m ≤ a (m + 1)) :
    a 0 + ∑ j ∈ Finset.range n, s j ≤ a n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← add_assoc]
    exact (Nat.add_le_add_right (ih fun m hm ↦ h m (by lia)) _).trans (h n (by lia))

variable [Fintype I] [∀ i j, Fintype (Q i j)] [∀ i, FiniteDimensional k (V i)]

/-- **One step of the budget**: for subrepresentations `P ≤ P'` with `Hom(M|P, P'/P) = 0`,
`e(M|P) + e(P'/P) ≤ e(M|P')`, since `M|P'` is an extension of `P'/P` by `M|P`. -/
theorem selfExtDim_restrict_add_le (hM : M.IsPreprojective) {P P' : M.subreps} (hPP' : P ≤ P')
    (hHom : Hom (M.restrict P) (M.subquotient P P') = ⊥) :
    selfExtDim (M.restrict P) + selfExtDim (M.subquotient P P') ≤
      selfExtDim (M.restrict P') := by
  obtain ⟨ξ, hξ, ⟨u⟩⟩ := (M.restrict P').exists_iso_extension (M.subrepOf P P')
    (hM.restrict P')
  have hHom' := Hom_eq_bot_of_iso (restrictSubrepOfIso hPP') hHom
  have h := selfExtDim_add_le ((hM.restrict P').restrict _) ((hM.restrict P').quotient _) hξ
    hHom'
  rwa [← u.selfExtDim_eq, (restrictSubrepOfIso hPP').selfExtDim_eq] at h

/-- **The Mukai budget lemma in the model.** Let `M` satisfy the preprojective relations and
`M_0 ≤ M_1 ≤ ⋯ ≤ M_n = M` be subrepresentations such that no prefix `M_j` maps nonzero to the
next subquotient `M_{j+1}/M_j` (a Hom-orthogonal tower). Then `∑_j e(M_{j+1}/M_j) ≤ e(M)`. -/
theorem sum_selfExtDim_subquotient_le (hM : M.IsPreprojective) {n : ℕ} {c : ℕ → M.subreps}
    (hc : Monotone c) (hcn : c n = ⊤)
    (hHom : ∀ j < n, Hom (M.restrict (c j)) (M.subquotient (c j) (c (j + 1))) = ⊥) :
    ∑ j ∈ Finset.range n, selfExtDim (M.subquotient (c j) (c (j + 1))) ≤ selfExtDim M :=
  (Nat.le_add_left _ _).trans ((add_sum_le_of_step (a := fun j ↦ selfExtDim (M.restrict (c j)))
    fun m hm ↦ selfExtDim_restrict_add_le hM (hc (Nat.le_succ m)) (hHom m hm)).trans_eq
      (restrictIsoOfEqTop hcn).selfExtDim_eq)

end Budget

end Quiver.Preprojective.DoubledRep
