/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.RepresentationTheory.Quiver.Kronecker.Preprojective
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.LinearCombination

/-!
# No semirigid wall object with two copies of each simple

Let `S₀`, `S₁` be distinct spherical simples of one phase with `dim Ext¹(S₁, S₀) = 2`. Their
iterated extensions are the nilpotent representations of the doubled `2`-Kronecker quiver with
the preprojective relations (`RepresentationTheory/Quiver/Kronecker/Preprojective.lean`). The Mukai
square of a wall object with multiplicities `(a, b)` is `-2(a - b)²`, so a wall object `D` with
multiplicities `(2, 2)` has square `0`, and by Riemann–Roch it is semirigid (`e(D) = 2`) exactly
when `dim End D = 1`. This file proves that this never happens:

* `DoubledRep.two_le_finrank_Hom_of_twoTwo`: **every nilpotent representation with the
  preprojective relations, two arrows each way and dimension vector `(2, 2)` has
  `dim End ≥ 2`**, over any field. So there is no semirigid wall object with multiplicities
  `(2, 2)`.

The proof follows the notes on pairing-two walls ("Why doubling both simples gives a different
case"). A simple that occurs both in the socle and in the top gives a nonscalar endomorphism,
the composite `D ↠ S ↪ D` (`exists_ne_smul_id_of_socle_top₀`, `exists_ne_smul_id_of_socle_top₁`).
Nilpotence gives a nonzero socle and a nonzero top (`IsNilpotent.socle_ne_bot`,
`IsNilpotent.top_ne_top`), so up to exchanging the vertices (`DoubledRep.swap`) the socle lies at
vertex one and the top at vertex zero. Then:

* **the pencil** (`exists_ne_smul_id_of_B_eq_zero`): if every `B_i` vanishes, `D` is an extension
  of `S₀²` by `S₁²` given by two `2 × 2` matrices `A_i` with no common kernel whose images span.
  Some member of the pencil `A_i`, `A_j`, `A_i + A_j` is invertible: if `A_i` and `A_j` are
  singular their kernels are complementary lines, and then `A_i + A_j` is onto. Normalizing it to
  the identity leaves the centralizer of the other matrix inside `End D`, of dimension at least
  two;
* **the uniserial case** (`exists_ne_smul_id_of_B_ne_zero`): otherwise the socle and the top are
  lines, every `B_i` has rank one through the same line `r`, nilpotence puts every `A_i r` in the
  socle line, and the preprojective relations make the classes of the bottom and the top
  length-two pieces proportional; the projection onto the top piece followed by the inclusion of
  the bottom one is a nonscalar endomorphism.

## Main definitions

* `DoubledRep.swap`: the representation with the two vertices exchanged.
-/

open Module

namespace Quiver.Kronecker.DoubledRep

variable {k ι V₀ V₁ : Type*} [Field k] [AddCommGroup V₀] [Module k V₀] [AddCommGroup V₁]
  [Module k V₁]

/-! ### Exchanging the vertices -/

/-- The representation with the two vertices exchanged: `A` and `B` swap roles. -/
def swap (M : DoubledRep k ι V₀ V₁) : DoubledRep k ι V₁ V₀ :=
  ⟨M.B, M.A⟩

@[simp] lemma swap_A (M : DoubledRep k ι V₀ V₁) (i : ι) : M.swap.A i = M.B i := rfl

@[simp] lemma swap_B (M : DoubledRep k ι V₀ V₁) (i : ι) : M.swap.B i = M.A i := rfl

/-- An endomorphism of the exchanged representation is an endomorphism of `M`. -/
lemma mem_Hom_of_mem_Hom_swap {M : DoubledRep k ι V₀ V₁} {f : (V₁ →ₗ[k] V₁) × (V₀ →ₗ[k] V₀)}
    (hf : f ∈ Hom M.swap M.swap) : (f.2, f.1) ∈ Hom M M :=
  fun i ↦ ⟨(hf i).2, (hf i).1⟩

lemma IsPreprojective.swap [Fintype ι] {M : DoubledRep k ι V₀ V₁} (hM : M.IsPreprojective) :
    M.swap.IsPreprojective :=
  ⟨hM.2, hM.1⟩

/-! ### Nonscalar endomorphisms -/

/-- **A nonscalar endomorphism gives `dim End ≥ 2`**: it is linearly independent of the
identity. -/
theorem two_le_finrank_Hom_of_ne_smul_id [FiniteDimensional k V₀] [FiniteDimensional k V₁]
    [Nontrivial V₀] (M : DoubledRep k ι V₀ V₁) {f : (V₀ →ₗ[k] V₀) × (V₁ →ₗ[k] V₁)}
    (hf : f ∈ Hom M M) (hns : ∀ c : k, f ≠ c • (LinearMap.id, LinearMap.id)) :
    2 ≤ finrank k (Hom M M) := by
  have hid : ((LinearMap.id, LinearMap.id) : (V₀ →ₗ[k] V₀) × (V₁ →ₗ[k] V₁)) ≠ 0 := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : V₀)
    exact hv (by simpa using LinearMap.congr_fun (congrArg Prod.fst h) v)
  have hli : LinearIndependent k
      ![(⟨(LinearMap.id, LinearMap.id), M.id_mem_Hom⟩ : Hom M M), ⟨f, hf⟩] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hst' : s • ((LinearMap.id, LinearMap.id) : (V₀ →ₗ[k] V₀) × (V₁ →ₗ[k] V₁)) + t • f = 0 :=
      congrArg Subtype.val hst
    by_cases ht : t = 0
    · subst ht
      rw [zero_smul, add_zero] at hst'
      exact ⟨(smul_eq_zero.mp hst').resolve_right hid, rfl⟩
    · exfalso
      apply hns (-(t⁻¹ * s))
      have htf : t • f = -(s • ((LinearMap.id, LinearMap.id) :
          (V₀ →ₗ[k] V₀) × (V₁ →ₗ[k] V₁))) := eq_neg_of_add_eq_zero_right hst'
      calc f = t⁻¹ • (t • f) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        _ = _ := by rw [htf, smul_neg, smul_smul, neg_smul]
  simpa using hli.fintype_card_le_finrank

/-- **A simple `S₀` in both the socle and the top**: a vector `v ≠ 0` killed by every `A_i` and a
functional `l ≠ 0` killing every image of a `B_i` give the nonscalar endomorphism
`(l(·) v, 0)`. -/
theorem exists_ne_smul_id_of_socle_top₀ [Nontrivial V₁] (M : DoubledRep k ι V₀ V₁) {v : V₀}
    (hv0 : v ≠ 0) (hv : ∀ i, M.A i v = 0) {l : V₀ →ₗ[k] k} (hl0 : l ≠ 0)
    (hl : ∀ i, l ∘ₗ M.B i = 0) :
    ∃ f ∈ Hom M M, ∀ c : k, f ≠ c • (LinearMap.id, LinearMap.id) := by
  refine ⟨(l.smulRight v, 0), fun i ↦ ⟨LinearMap.ext fun x ↦ ?_, LinearMap.ext fun y ↦ ?_⟩,
    fun c hc ↦ ?_⟩
  · simp [hv]
  · have := LinearMap.congr_fun (hl i) y
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at this
    simp [this]
  · obtain ⟨u, hu⟩ := exists_ne (0 : V₁)
    have h2 := LinearMap.congr_fun (congrArg Prod.snd hc) u
    simp only [Prod.smul_snd, LinearMap.zero_apply, LinearMap.smul_apply, LinearMap.id_apply]
      at h2
    have hc0 : c = 0 := (smul_eq_zero.mp h2.symm).resolve_right hu
    subst hc0
    apply hl0
    refine LinearMap.ext fun x ↦ ?_
    have h1 := LinearMap.congr_fun (congrArg Prod.fst hc) x
    simp only [LinearMap.smulRight_apply, zero_smul, Prod.fst_zero, LinearMap.zero_apply] at h1
    exact (smul_eq_zero.mp h1).resolve_right hv0

/-- **A simple `S₁` in both the socle and the top**: `(0, m(·) u)`. -/
theorem exists_ne_smul_id_of_socle_top₁ [Nontrivial V₀] (M : DoubledRep k ι V₀ V₁) {u : V₁}
    (hu0 : u ≠ 0) (hu : ∀ i, M.B i u = 0) {m : V₁ →ₗ[k] k} (hm0 : m ≠ 0)
    (hm : ∀ i, m ∘ₗ M.A i = 0) :
    ∃ f ∈ Hom M M, ∀ c : k, f ≠ c • (LinearMap.id, LinearMap.id) := by
  obtain ⟨f, hf, hns⟩ := M.swap.exists_ne_smul_id_of_socle_top₀ hu0 hu hm0 hm
  refine ⟨(f.2, f.1), mem_Hom_of_mem_Hom_swap hf, fun c hc ↦ hns c ?_⟩
  exact Prod.ext (congrArg Prod.snd hc) (congrArg Prod.fst hc)

/-! ### Socle and top of a nilpotent representation -/

section Nilpotent

/-- In a nilpotent representation on a nonzero space some nonzero vector is killed by every
arrow, so the socle is nonzero at one of the vertices. -/
theorem IsNilpotent.socle_ne_bot [Nontrivial V₀] {M : DoubledRep k ι V₀ V₁}
    (hM : M.IsNilpotent) :
    (⨅ i, LinearMap.ker (M.A i)) ≠ ⊥ ∨ (⨅ i, LinearMap.ker (M.B i)) ≠ ⊥ := by
  classical
  let m := Nat.find hM
  have hm : ∀ w : List (ι ⊕ ι), m ≤ w.length → (w.map M.arrow).prod = 0 := Nat.find_spec hM
  have hne : (1 : Module.End k (V₀ × V₁)) ≠ 0 := one_ne_zero
  obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := by
    refine Nat.exists_eq_add_one.mpr (Nat.pos_of_ne_zero fun h0 ↦ hne ?_)
    simpa using hm [] (by omega)
  have hmin := Nat.find_min hM (show m' < m by omega)
  push Not at hmin
  obtain ⟨w, hw, hw0⟩ := hmin
  have hlen : w.length = m' := by
    by_contra hne'
    exact hw0 (hm w (by omega))
  obtain ⟨y, hy⟩ : ∃ y, (w.map M.arrow).prod y ≠ 0 := by
    by_contra h
    push Not at h
    exact hw0 (LinearMap.ext h)
  set x := (w.map M.arrow).prod y
  have hkill : ∀ a, M.arrow a x = 0 := fun a ↦ by
    have := LinearMap.congr_fun (hm (a :: w) (by simp [hlen]; omega)) y
    simpa [List.map_cons, List.prod_cons, mul_apply_eq_comp] using this
  by_cases hx1 : x.1 = 0
  · right
    refine (Submodule.ne_bot_iff _).mpr ⟨x.2, Submodule.mem_iInf _ |>.mpr fun i ↦ ?_, ?_⟩
    · have := congrArg Prod.fst (hkill (.inr i))
      simpa using this
    · intro hx2
      exact hy (Prod.ext hx1 hx2)
  · left
    refine (Submodule.ne_bot_iff _).mpr ⟨x.1, Submodule.mem_iInf _ |>.mpr fun i ↦ ?_, hx1⟩
    have := congrArg Prod.snd (hkill (.inl i))
    simpa using this

/-- The span of the images of the paths of length `m`. -/
private noncomputable def pathSpan (M : DoubledRep k ι V₀ V₁) (m : ℕ) :
    Submodule k (V₀ × V₁) :=
  ⨆ (w : List (ι ⊕ ι)) (_ : w.length = m), LinearMap.range ((w.map M.arrow).prod)

/-- In a nilpotent representation on a nonzero space the images of the arrows do not span, so
the top is nonzero at one of the vertices. -/
theorem IsNilpotent.top_ne_top [Nontrivial V₀] {M : DoubledRep k ι V₀ V₁}
    (hM : M.IsNilpotent) :
    (⨆ i, LinearMap.range (M.B i)) ≠ ⊤ ∨ (⨆ i, LinearMap.range (M.A i)) ≠ ⊤ := by
  by_contra h
  push Not at h
  obtain ⟨hB, hA⟩ := h
  -- the images of the arrows span
  have harrow : ⨆ a, LinearMap.range (M.arrow a) = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← LinearMap.sup_range_inl_inr]
    refine sup_le ?_ ?_
    · rw [LinearMap.range_eq_map, ← hB, Submodule.map_iSup]
      refine iSup_le fun i ↦ ?_
      rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
      exact Submodule.mem_iSup_of_mem (Sum.inr i) ⟨(0, y), rfl⟩
    · rw [LinearMap.range_eq_map, ← hA, Submodule.map_iSup]
      refine iSup_le fun i ↦ ?_
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact Submodule.mem_iSup_of_mem (Sum.inl i) ⟨(x, 0), rfl⟩
  -- so the images of the paths of every length span
  have hspan : ∀ m, pathSpan M m = ⊤ := by
    intro m
    induction m with
    | zero =>
      refine eq_top_iff.mpr (le_trans ?_ (le_iSup₂_of_le ([] : List (ι ⊕ ι)) rfl le_rfl))
      rw [List.map_nil, List.prod_nil, Module.End.one_eq_id, LinearMap.range_id]
    | succ m ih =>
      refine eq_top_iff.mpr ?_
      rw [← harrow]
      refine iSup_le fun a ↦ ?_
      rw [LinearMap.range_eq_map, ← ih, pathSpan, Submodule.map_iSup]
      refine iSup_le fun w ↦ ?_
      rw [Submodule.map_iSup]
      refine iSup_le fun hw ↦ ?_
      rw [← LinearMap.range_comp]
      refine le_iSup₂_of_le (a :: w) (by simp [hw]) (le_of_eq ?_)
      simp [List.map_cons, List.prod_cons, Module.End.mul_eq_comp]
  -- but the paths of length `n` vanish
  obtain ⟨n, hn⟩ := hM
  have hbot : pathSpan M n = ⊥ := by
    refine eq_bot_iff.mpr (iSup₂_le fun w hw ↦ ?_)
    rw [hn w hw.ge, LinearMap.range_zero]
  have htb : (⊤ : Submodule k (V₀ × V₁)) = ⊥ := (hspan n).symm.trans hbot
  obtain ⟨v, hv⟩ := exists_ne (0 : V₀)
  have h0 := (Submodule.eq_bot_iff _).mp htb (v, 0) Submodule.mem_top
  exact hv (congrArg Prod.fst h0)

/-- In a nilpotent representation every composite `B_j A_i` is nilpotent. -/
theorem IsNilpotent.isNilpotent_B_comp_A {M : DoubledRep k ι V₀ V₁} (hM : M.IsNilpotent)
    (i j : ι) : _root_.IsNilpotent (M.B j ∘ₗ M.A i) := by
  obtain ⟨n, hn⟩ := hM
  have hword : ∀ m : ℕ, ∀ v : V₀,
      ((List.flatten (List.replicate m [Sum.inr j, Sum.inl i])).map M.arrow).prod (v, 0) =
        (((M.B j ∘ₗ M.A i) ^ m) v, 0) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro v
      rw [List.replicate_succ, List.flatten_cons, List.map_append, List.prod_append,
        mul_apply_eq_comp, ih, pow_succ', mul_apply_eq_comp]
      simp
  refine ⟨n, LinearMap.ext fun v ↦ ?_⟩
  have h := congrArg Prod.fst (hword n v)
  rw [hn _ (by simp; omega)] at h
  simpa using h.symm

/-- In a nilpotent representation every composite `A_j B_i` is nilpotent. -/
theorem IsNilpotent.isNilpotent_A_comp_B {M : DoubledRep k ι V₀ V₁} (hM : M.IsNilpotent)
    (i j : ι) : _root_.IsNilpotent (M.A j ∘ₗ M.B i) := by
  obtain ⟨n, hn⟩ := hM
  have hword : ∀ m : ℕ, ∀ y : V₁,
      ((List.flatten (List.replicate m [Sum.inl j, Sum.inr i])).map M.arrow).prod (0, y) =
        (0, ((M.A j ∘ₗ M.B i) ^ m) y) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro y
      rw [List.replicate_succ, List.flatten_cons, List.map_append, List.prod_append,
        mul_apply_eq_comp, ih, pow_succ', mul_apply_eq_comp]
      simp
  refine ⟨n, LinearMap.ext fun y ↦ ?_⟩
  have h := congrArg Prod.snd (hword n y)
  rw [hn _ (by simp; omega)] at h
  simpa using h.symm

end Nilpotent

/-! ### The pencil -/

section Pencil

variable [FiniteDimensional k V₀] [FiniteDimensional k V₁]

omit [FiniteDimensional k V₀] [FiniteDimensional k V₁] in
/-- If every `A_l` lies in the pencil `e ∘ (a + bX)` of an isomorphism `e` and every `B_l`
vanishes, then `(f₀, e f₀ e⁻¹)` is an endomorphism for every `f₀` commuting with `X`. -/
lemma conj_mem_Hom (M : DoubledRep k ι V₀ V₁) (e : V₀ ≃ₗ[k] V₁) (X : Module.End k V₀)
    (hA : ∀ l, ∃ a b : k,
      M.A l = (e : V₀ →ₗ[k] V₁) ∘ₗ (a • LinearMap.id + b • X))
    (hB : ∀ l, M.B l = 0) {f₀ : Module.End k V₀} (hf₀ : Commute f₀ X) :
    (f₀, (e : V₀ →ₗ[k] V₁) ∘ₗ f₀ ∘ₗ (e.symm : V₁ →ₗ[k] V₀)) ∈ Hom M M := by
  intro l
  obtain ⟨a, b, hl⟩ := hA l
  refine ⟨LinearMap.ext fun x ↦ ?_, by simp [hB]⟩
  have hc := LinearMap.congr_fun hf₀.eq x
  simp only [mul_apply_eq_comp] at hc
  simp [hl, hc]

omit [FiniteDimensional k V₀] [FiniteDimensional k V₁] in
/-- On a space of dimension at least two every endomorphism commutes with a nonscalar one. -/
lemma exists_commute_ne_smul_id (h : 2 ≤ finrank k V₀) (X : Module.End k V₀) :
    ∃ f₀ : Module.End k V₀, Commute f₀ X ∧ ∀ c : k, f₀ ≠ c • LinearMap.id := by
  by_cases hX : ∃ c : k, X = c • LinearMap.id
  · obtain ⟨c, rfl⟩ := hX
    have : Nontrivial V₀ := Module.nontrivial_of_finrank_pos (R := k) (by omega)
    obtain ⟨v, hv⟩ := exists_ne (0 : V₀)
    have hlt : (k ∙ v) < ⊤ := by
      refine lt_top_iff_ne_top.mpr fun htop ↦ ?_
      have := finrank_span_singleton (K := k) hv
      rw [htop, finrank_top] at this
      omega
    obtain ⟨l, hl0, hle⟩ := (k ∙ v).exists_le_ker_of_lt_top hlt
    have hlv : l v = 0 := LinearMap.mem_ker.mp (hle (Submodule.mem_span_singleton_self v))
    refine ⟨l.smulRight v, ?_, fun c' hc' ↦ ?_⟩
    · rw [← Module.End.one_eq_id]
      exact (Commute.one_right _).smul_right c
    · have h1 := LinearMap.congr_fun hc' v
      simp only [LinearMap.smulRight_apply, hlv, zero_smul, LinearMap.smul_apply,
        LinearMap.id_apply] at h1
      have hc0 : c' = 0 := (smul_eq_zero.mp h1.symm).resolve_right hv
      subst hc0
      apply hl0
      refine LinearMap.ext fun x ↦ ?_
      have h2 := LinearMap.congr_fun hc' x
      simp only [LinearMap.smulRight_apply, zero_smul, LinearMap.zero_apply] at h2
      exact (smul_eq_zero.mp h2).resolve_right hv
  · push Not at hX
    exact ⟨X, Commute.refl X, hX⟩

/-- **The pencil case.** Two arrows `A_i`, `A_j : V₀ → V₁` between planes, with no common kernel
and spanning images, and no arrow back: some nonscalar endomorphism exists. -/
theorem exists_ne_smul_id_of_B_eq_zero (M : DoubledRep k ι V₀ V₁) {i j : ι}
    (hl : ∀ l, l = i ∨ l = j) (h₀ : finrank k V₀ = 2) (h₁ : finrank k V₁ = 2)
    (hB : ∀ l, M.B l = 0) (hsoc : LinearMap.ker (M.A i) ⊓ LinearMap.ker (M.A j) = ⊥)
    (him : LinearMap.range (M.A i) ⊔ LinearMap.range (M.A j) = ⊤) :
    ∃ f ∈ Hom M M, ∀ c : k, f ≠ c • (LinearMap.id, LinearMap.id) := by
  have hdim : finrank k V₀ = finrank k V₁ := by rw [h₀, h₁]
  -- some member of the pencil `A_i`, `A_j`, `A_i + A_j` is invertible
  obtain ⟨e, X, hA⟩ : ∃ (e : V₀ ≃ₗ[k] V₁) (X : Module.End k V₀), ∀ l, ∃ a b : k,
      M.A l = (e : V₀ →ₗ[k] V₁) ∘ₗ (a • LinearMap.id + b • X) := by
    by_cases hi : Function.Injective (M.A i)
    · let e := (M.A i).linearEquivOfInjective hi hdim
      refine ⟨e, (e.symm : V₁ →ₗ[k] V₀) ∘ₗ M.A j, fun l ↦ ?_⟩
      rcases hl l with rfl | rfl
      · exact ⟨1, 0, by ext x; simp [e]⟩
      · exact ⟨0, 1, by ext x; simp⟩
    by_cases hj : Function.Injective (M.A j)
    · let e := (M.A j).linearEquivOfInjective hj hdim
      refine ⟨e, (e.symm : V₁ →ₗ[k] V₀) ∘ₗ M.A i, fun l ↦ ?_⟩
      rcases hl l with rfl | rfl
      · exact ⟨0, 1, by ext x; simp⟩
      · exact ⟨1, 0, by ext x; simp [e]⟩
    -- both singular: their kernels are complementary lines, so `A_i + A_j` is onto
    have hki : LinearMap.ker (M.A i) ≠ ⊥ := fun h ↦ hi (LinearMap.ker_eq_bot.mp h)
    have hkj : LinearMap.ker (M.A j) ≠ ⊥ := fun h ↦ hj (LinearMap.ker_eq_bot.mp h)
    have hsup : LinearMap.ker (M.A i) ⊔ LinearMap.ker (M.A j) = ⊤ := by
      refine Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) ?_)
      have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker (M.A i))
        (LinearMap.ker (M.A j))
      rw [hsoc, finrank_bot] at h
      have hi' := Submodule.one_le_finrank_iff.mpr hki
      have hj' := Submodule.one_le_finrank_iff.mpr hkj
      omega
    have hsurj : Function.Surjective (M.A i + M.A j) := by
      rw [← LinearMap.range_eq_top, eq_top_iff, ← him]
      refine sup_le ?_ ?_
      · rintro _ ⟨x, rfl⟩
        obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ :=
          Submodule.mem_sup.mp (hsup ▸ Submodule.mem_top : x ∈ _ ⊔ _)
        refine ⟨x₂, ?_⟩
        rw [LinearMap.mem_ker] at hx₁ hx₂
        simp [hx₁, hx₂]
      · rintro _ ⟨x, rfl⟩
        obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ :=
          Submodule.mem_sup.mp (hsup ▸ Submodule.mem_top : x ∈ _ ⊔ _)
        refine ⟨x₁, ?_⟩
        rw [LinearMap.mem_ker] at hx₁ hx₂
        simp [hx₁, hx₂]
    have hinj : Function.Injective (M.A i + M.A j) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj
    let e := (M.A i + M.A j).linearEquivOfInjective hinj hdim
    have he : ∀ x, e x = M.A i x + M.A j x := fun x ↦ rfl
    refine ⟨e, (e.symm : V₁ →ₗ[k] V₀) ∘ₗ M.A i, fun l ↦ ?_⟩
    rcases hl l with hli | hlj
    · rw [hli]
      exact ⟨0, 1, by ext x; simp⟩
    · rw [hlj]
      refine ⟨1, -1, LinearMap.ext fun x ↦ ?_⟩
      change M.A j x = e ((1 : k) • x + (-1 : k) • e.symm (M.A i x))
      rw [one_smul, map_add, map_smul, LinearEquiv.apply_symm_apply, he, neg_one_smul]
      abel
  obtain ⟨f₀, hf₀, hns⟩ := exists_commute_ne_smul_id (h₀ ▸ le_rfl) X
  refine ⟨_, M.conj_mem_Hom e X hA hB hf₀, fun c hc ↦ hns c (congrArg Prod.fst hc)⟩

end Pencil

/-! ### The uniserial case -/

section Uniserial

variable [Fintype ι] [FiniteDimensional k V₀] [FiniteDimensional k V₁]

/-- A subspace of a plane other than `0` and the whole plane is a line. -/
private lemma finrank_eq_one_of_ne_bot_of_ne_top {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (hV : finrank k V = 2) {U : Submodule k V} (h0 : U ≠ ⊥)
    (h1 : U ≠ ⊤) : finrank k U = 1 := by
  have := Submodule.one_le_finrank_iff.mpr h0
  have := Submodule.finrank_lt h1
  omega

/-- A line `U` of a plane is the kernel of a nonzero functional. -/
private lemma exists_ker_eq {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (hV : finrank k V = 2) {U : Submodule k V} (hU : finrank k U = 1) :
    ∃ l : V →ₗ[k] k, l ≠ 0 ∧ LinearMap.ker l = U := by
  have hlt : U < ⊤ := lt_top_iff_ne_top.mpr fun h ↦ by
    rw [h, finrank_top] at hU
    omega
  obtain ⟨l, hl0, hle⟩ := U.exists_le_ker_of_lt_top hlt
  refine ⟨l, hl0, (Submodule.eq_of_le_of_finrank_eq hle ?_).symm⟩
  have := Module.Dual.finrank_ker_add_one_of_ne_zero hl0
  omega

/-- **The uniserial case.** If some `B_i` is nonzero, the socle at vertex one and the top at vertex
zero are proper (so lines), the images of the `A_i` span, the composites `B_j A_i` are nilpotent
and the preprojective relations hold, then some nonscalar endomorphism exists. -/
theorem exists_ne_smul_id_of_B_ne_zero (M : DoubledRep k ι V₀ V₁) {i j : ι} (hij : i ≠ j)
    (hl : ∀ l, l = i ∨ l = j) (h₀ : finrank k V₀ = 2) (h₁ : finrank k V₁ = 2)
    (hpre : M.IsPreprojective) (hnil : ∀ l l', _root_.IsNilpotent (M.B l' ∘ₗ M.A l))
    (hB : ∃ l, M.B l ≠ 0) (hsoc : (⨅ l, LinearMap.ker (M.B l)) ≠ ⊥)
    (htop : (⨆ l, LinearMap.range (M.B l)) ≠ ⊤) (him : (⨆ l, LinearMap.range (M.A l)) = ⊤) :
    ∃ f ∈ Hom M M, ∀ c : k, f ≠ c • (LinearMap.id, LinearMap.id) := by
  classical
  set K := ⨅ l, LinearMap.ker (M.B l) with hKdef
  set R := ⨆ l, LinearMap.range (M.B l) with hRdef
  obtain ⟨l₀, hl₀⟩ := hB
  have hK_le : ∀ l, K ≤ LinearMap.ker (M.B l) := fun l ↦ iInf_le _ l
  have hle_R : ∀ l, LinearMap.range (M.B l) ≤ R := fun l ↦ le_iSup (fun l ↦ LinearMap.range _) l
  -- the socle `K` and the image `R` are lines
  have hKtop : K ≠ ⊤ := by
    intro hK
    apply hl₀
    refine LinearMap.ext fun y ↦ ?_
    exact LinearMap.mem_ker.mp (hK_le l₀ (hK ▸ Submodule.mem_top))
  have hRbot : R ≠ ⊥ := by
    intro hR
    apply hl₀
    refine LinearMap.ext fun y ↦ ?_
    have := hle_R l₀ ⟨y, rfl⟩
    rw [hR, Submodule.mem_bot] at this
    exact this
  have hKdim := finrank_eq_one_of_ne_bot_of_ne_top h₁ hsoc hKtop
  have hRdim := finrank_eq_one_of_ne_bot_of_ne_top h₀ hRbot htop
  obtain ⟨κ, hκ0, hκK⟩ := exists_ker_eq h₁ hKdim
  obtain ⟨ψ₀, hψ0, hψR⟩ := exists_ker_eq h₀ hRdim
  obtain ⟨⟨r, hrR⟩, hr0, hrspan⟩ := finrank_eq_one_iff'.mp hRdim
  obtain ⟨⟨k₀, hk₀K⟩, hk₀0, hk₀span⟩ := finrank_eq_one_iff'.mp hKdim
  have hr0' : r ≠ 0 := fun h ↦ hr0 (Subtype.ext h)
  have hk₀0' : k₀ ≠ 0 := fun h ↦ hk₀0 (Subtype.ext h)
  have hmemR : ∀ x ∈ R, ∃ c : k, x = c • r := fun x hx ↦ by
    obtain ⟨c, hc⟩ := hrspan ⟨x, hx⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩
  have hmemK : ∀ y ∈ K, ∃ c : k, y = c • k₀ := fun y hy ↦ by
    obtain ⟨c, hc⟩ := hk₀span ⟨y, hy⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩
  have hψr : ψ₀ r = 0 := LinearMap.mem_ker.mp (hψR ▸ hrR)
  have hBk₀ : ∀ l, M.B l k₀ = 0 := fun l ↦ LinearMap.mem_ker.mp (hK_le l hk₀K)
  -- vectors off the two lines
  obtain ⟨u₂, hu₂⟩ : ∃ u, κ u = 1 := by
    obtain ⟨u, hu⟩ : ∃ u, κ u ≠ 0 := by
      by_contra h
      push Not at h
      exact hκ0 (LinearMap.ext h)
    exact ⟨(κ u)⁻¹ • u, by simp [hu]⟩
  obtain ⟨v₂, hv₂⟩ : ∃ v, ψ₀ v = 1 := by
    obtain ⟨v, hv⟩ : ∃ v, ψ₀ v ≠ 0 := by
      by_contra h
      push Not at h
      exact hψ0 (LinearMap.ext h)
    exact ⟨(ψ₀ v)⁻¹ • v, by simp [hv]⟩
  -- every `B_l` is `κ(·) b_l r`
  have hBκ : ∀ l y, M.B l y = κ y • M.B l u₂ := fun l y ↦ by
    have hmem : y - κ y • u₂ ∈ K := by
      rw [← hκK, LinearMap.mem_ker, map_sub, map_smul, hu₂, smul_eq_mul, mul_one, sub_self]
    have := LinearMap.mem_ker.mp (hK_le l hmem)
    rw [map_sub, map_smul, sub_eq_zero] at this
    exact this
  choose b hb using fun l ↦ hmemR (M.B l u₂) (hle_R l ⟨u₂, rfl⟩)
  have hBb : ∀ l y, M.B l y = (κ y * b l) • r := fun l y ↦ by
    rw [hBκ, hb, smul_smul]
  have hb0 : b l₀ ≠ 0 := by
    intro h0
    apply hl₀
    refine LinearMap.ext fun y ↦ ?_
    rw [hBb, h0, mul_zero, zero_smul, LinearMap.zero_apply]
  -- nilpotence puts every `A_l r` in the socle line
  have hAr : ∀ l, M.A l r ∈ K := fun l ↦ by
    rw [← hκK, LinearMap.mem_ker]
    obtain ⟨n, hn⟩ := hnil l l₀
    set c := κ (M.A l r) * b l₀
    have hpow : ∀ m : ℕ, ((M.B l₀ ∘ₗ M.A l) ^ m) r = c ^ m • r := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ', mul_apply_eq_comp, ih, map_smul, LinearMap.comp_apply, hBb, smul_smul,
          pow_succ]
    have h := hpow n
    rw [hn, LinearMap.zero_apply] at h
    have hc : c = 0 := eq_zero_of_pow_eq_zero ((smul_eq_zero.mp h.symm).resolve_right hr0')
    exact (mul_eq_zero.mp hc).resolve_right hb0
  choose x hx using fun l ↦ hmemK _ (hAr l)
  -- `κ ∘ A_l` kills the line `r`, so it is `z_l ψ₀`
  set z : ι → k := fun l ↦ κ (M.A l v₂)
  have hκA : ∀ l v, κ (M.A l v) = ψ₀ v * z l := fun l v ↦ by
    have hmem : v - ψ₀ v • v₂ ∈ R := by
      rw [← hψR, LinearMap.mem_ker, map_sub, map_smul, hv₂, smul_eq_mul, mul_one, sub_self]
    obtain ⟨c, hc⟩ := hmemR _ hmem
    have h1 : M.A l (v - ψ₀ v • v₂) = (c * x l) • k₀ := by rw [hc, map_smul, hx, smul_smul]
    have h2 : κ (M.A l (v - ψ₀ v • v₂)) = 0 := by
      rw [h1, map_smul, LinearMap.mem_ker.mp (hκK ▸ hk₀K), smul_zero]
    rw [map_sub, map_sub, map_smul, map_smul, smul_eq_mul, sub_eq_zero] at h2
    exact h2
  -- the preprojective relations: `∑ b_l z_l = 0` and `∑ b_l x_l = 0`
  have hz : ∑ l, z l * b l = 0 := by
    have := LinearMap.congr_fun hpre.1 v₂
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.zero_apply, hBb] at this
    rw [← Finset.sum_smul] at this
    exact (smul_eq_zero.mp this).resolve_right hr0'
  have hxs : ∑ l, b l * x l = 0 := by
    have := LinearMap.congr_fun hpre.2 u₂
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.zero_apply, hb, map_smul, hx,
      smul_smul] at this
    rw [← Finset.sum_smul] at this
    exact (smul_eq_zero.mp this).resolve_right hk₀0'
  -- `z ≠ 0`, since the images of the `A_l` span
  obtain ⟨l₁, hl₁⟩ : ∃ l, z l ≠ 0 := by
    by_contra h
    push Not at h
    apply hKtop
    rw [eq_top_iff, ← him, ← hκK]
    refine iSup_le fun l ↦ ?_
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker, hκA, h, mul_zero]
  -- `x` and `z` are proportional: both are orthogonal to `b ≠ 0` in a plane
  have hdet : x i * z j = x j * z i := by
    have hsum : ∀ f : ι → k, ∑ l, f l = f i + f j := fun f ↦ by
      rw [show (Finset.univ : Finset ι) = {i, j} from (Finset.eq_univ_of_forall
        (fun l ↦ by rcases hl l with rfl | rfl <;> simp)).symm, Finset.sum_pair hij]
    rw [hsum] at hz hxs
    have hbij : b i ≠ 0 ∨ b j ≠ 0 := by
      rcases hl l₀ with rfl | rfl
      · exact Or.inl hb0
      · exact Or.inr hb0
    rcases hbij with hbi | hbj
    · have : b i * (x i * z j - x j * z i) = 0 := by linear_combination z j * hxs - x j * hz
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hbi)
    · have : b j * (x i * z j - x j * z i) = 0 := by linear_combination x i * hz - z i * hxs
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hbj)
  set c' := x l₁ / z l₁
  have hxz : ∀ l, x l = c' * z l := fun l ↦ by
    have : x l * z l₁ = x l₁ * z l := by
      rcases hl l with rfl | rfl <;> rcases hl l₁ with rfl | rfl
      · ring
      · exact hdet
      · exact hdet.symm
      · ring
    rw [show c' = x l₁ / z l₁ from rfl, div_mul_eq_mul_div, eq_div_iff hl₁]
    exact this
  -- the endomorphism: project to the top piece, include the bottom one
  refine ⟨(ψ₀.smulRight r, κ.smulRight (c' • k₀)), fun l ↦ ⟨LinearMap.ext fun v ↦ ?_,
    LinearMap.ext fun y ↦ ?_⟩, fun c hc ↦ ?_⟩
  · simp only [LinearMap.comp_apply, LinearMap.smulRight_apply, map_smul, hx, hκA, hxz, smul_smul]
    congr 1
    ring
  · have hψB : ψ₀ (M.B l y) = 0 := by rw [hBb, map_smul, hψr, smul_zero]
    simp [hψB, hBk₀]
  · have h1 := LinearMap.congr_fun (congrArg Prod.fst hc) r
    simp only [LinearMap.smulRight_apply, hψr, zero_smul, Prod.smul_fst, LinearMap.smul_apply,
      LinearMap.id_apply] at h1
    have hc0 : c = 0 := (smul_eq_zero.mp h1.symm).resolve_right hr0'
    subst hc0
    have h2 := LinearMap.congr_fun (congrArg Prod.fst hc) v₂
    simp only [LinearMap.smulRight_apply, hv₂, one_smul, zero_smul, Prod.fst_zero,
      LinearMap.zero_apply] at h2
    exact hr0' h2

end Uniserial

/-! ### The exclusion -/

section Exclusion

variable [Fintype ι] [FiniteDimensional k V₀] [FiniteDimensional k V₁]

omit [Fintype ι] in
/-- Infima and suprema over two indices. -/
private lemma iInf_eq_inf_of_two {α : Type*} [CompleteLattice α] {i j : ι}
    (hl : ∀ l, l = i ∨ l = j) (f : ι → α) : ⨅ l, f l = f i ⊓ f j :=
  le_antisymm (le_inf (iInf_le _ i) (iInf_le _ j))
    (le_iInf fun l ↦ (hl l).elim (fun h ↦ h ▸ inf_le_left) (fun h ↦ h ▸ inf_le_right))

omit [Fintype ι] in
private lemma iSup_eq_sup_of_two {α : Type*} [CompleteLattice α] {i j : ι}
    (hl : ∀ l, l = i ∨ l = j) (f : ι → α) : ⨆ l, f l = f i ⊔ f j :=
  le_antisymm (iSup_le fun l ↦ (hl l).elim (fun h ↦ h ▸ le_sup_left) (fun h ↦ h ▸ le_sup_right))
    (sup_le (le_iSup _ i) (le_iSup _ j))

/-- The case with the socle at vertex one and the top at vertex zero. -/
private theorem exists_ne_smul_id_main (M : DoubledRep k ι V₀ V₁) {i j : ι} (hij : i ≠ j)
    (hl : ∀ l, l = i ∨ l = j) (h₀ : finrank k V₀ = 2) (h₁ : finrank k V₁ = 2)
    (hpre : M.IsPreprojective) (hnil : ∀ l l', _root_.IsNilpotent (M.B l' ∘ₗ M.A l))
    (hs₀ : (⨅ l, LinearMap.ker (M.A l)) = ⊥) (ht₁ : (⨆ l, LinearMap.range (M.A l)) = ⊤)
    (hs₁ : (⨅ l, LinearMap.ker (M.B l)) ≠ ⊥) (ht₀ : (⨆ l, LinearMap.range (M.B l)) ≠ ⊤) :
    ∃ f ∈ Hom M M, ∀ c : k, f ≠ c • (LinearMap.id, LinearMap.id) := by
  by_cases hB : ∀ l, M.B l = 0
  · exact M.exists_ne_smul_id_of_B_eq_zero hl h₀ h₁ hB
      (by rw [← iInf_eq_inf_of_two hl (fun l ↦ LinearMap.ker (M.A l))]; exact hs₀)
      (by rw [← iSup_eq_sup_of_two hl (fun l ↦ LinearMap.range (M.A l))]; exact ht₁)
  · push Not at hB
    exact M.exists_ne_smul_id_of_B_ne_zero hij hl h₀ h₁ hpre hnil hB hs₁ ht₀ ht₁

/-- **No semirigid wall object with multiplicities `(2, 2)`.** A nilpotent representation of the
doubled `2`-Kronecker quiver with the preprojective relations and dimension vector `(2, 2)` has
`dim End ≥ 2`, over any field. In the wall model of two spherical simples with
`dim Ext¹ = 2`, a wall object of multiplicities `(2, 2)` has Mukai square `0`, so
`e = 2 dim End ≥ 4`: it is never semirigid. -/
theorem two_le_finrank_Hom_of_twoTwo (M : DoubledRep k ι V₀ V₁) (hι : Fintype.card ι = 2)
    (h₀ : finrank k V₀ = 2) (h₁ : finrank k V₁ = 2) (hpre : M.IsPreprojective)
    (hnil : M.IsNilpotent) : 2 ≤ finrank k (Hom M M) := by
  classical
  obtain ⟨i, j, hij, huniv⟩ :=
    (Finset.card_eq_two (s := (Finset.univ : Finset ι))).mp (by rwa [Finset.card_univ])
  have hl : ∀ l, l = i ∨ l = j := fun l ↦ by
    have := Finset.mem_univ l
    rw [huniv] at this
    simpa using this
  have : Nontrivial V₀ := Module.nontrivial_of_finrank_pos (R := k) (by omega)
  have : Nontrivial V₁ := Module.nontrivial_of_finrank_pos (R := k) (by omega)
  suffices ∃ f ∈ Hom M M, ∀ c : k, f ≠ c • (LinearMap.id, LinearMap.id) by
    obtain ⟨f, hf, hns⟩ := this
    exact M.two_le_finrank_Hom_of_ne_smul_id hf hns
  -- a simple type in both the socle and the top
  have hsocvec : ∀ {W : Submodule k V₀}, W ≠ ⊥ → ∃ v ∈ W, v ≠ 0 := fun hW ↦
    (Submodule.ne_bot_iff _).mp hW
  by_cases c₀ : (⨅ l, LinearMap.ker (M.A l)) ≠ ⊥ ∧ (⨆ l, LinearMap.range (M.B l)) ≠ ⊤
  · obtain ⟨v, hv, hv0⟩ := hsocvec c₀.1
    obtain ⟨l, hl0, hle⟩ := (⨆ l, LinearMap.range (M.B l)).exists_le_ker_of_lt_top
      (lt_top_iff_ne_top.mpr c₀.2)
    exact M.exists_ne_smul_id_of_socle_top₀ hv0
      (fun i ↦ LinearMap.mem_ker.mp (Submodule.mem_iInf _ |>.mp hv i)) hl0
      (fun i ↦ LinearMap.range_le_ker_iff.mp ((le_iSup (fun l ↦ LinearMap.range (M.B l)) i).trans
        hle))
  by_cases c₁ : (⨅ l, LinearMap.ker (M.B l)) ≠ ⊥ ∧ (⨆ l, LinearMap.range (M.A l)) ≠ ⊤
  · obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp c₁.1
    obtain ⟨m, hm0, hle⟩ := (⨆ l, LinearMap.range (M.A l)).exists_le_ker_of_lt_top
      (lt_top_iff_ne_top.mpr c₁.2)
    exact M.exists_ne_smul_id_of_socle_top₁ hu0
      (fun i ↦ LinearMap.mem_ker.mp (Submodule.mem_iInf _ |>.mp hu i)) hm0
      (fun i ↦ LinearMap.range_le_ker_iff.mp ((le_iSup (fun l ↦ LinearMap.range (M.A l)) i).trans
        hle))
  have hsoc := hnil.socle_ne_bot
  have htop := hnil.top_ne_top
  by_cases hs₀ : (⨅ l, LinearMap.ker (M.A l)) = ⊥
  · have hs₁ : (⨅ l, LinearMap.ker (M.B l)) ≠ ⊥ := hsoc.resolve_left (not_not.mpr hs₀)
    have ht₁ : (⨆ l, LinearMap.range (M.A l)) = ⊤ := by
      by_contra h
      exact c₁ ⟨hs₁, h⟩
    have ht₀ : (⨆ l, LinearMap.range (M.B l)) ≠ ⊤ := htop.resolve_right (not_not.mpr ht₁)
    exact M.exists_ne_smul_id_main hij hl h₀ h₁ hpre (fun l l' ↦ hnil.isNilpotent_B_comp_A l l')
      hs₀ ht₁ hs₁ ht₀
  · -- the mirror case: exchange the vertices
    have ht₀ : (⨆ l, LinearMap.range (M.B l)) = ⊤ := by
      by_contra h
      exact c₀ ⟨hs₀, h⟩
    have ht₁ : (⨆ l, LinearMap.range (M.A l)) ≠ ⊤ := htop.resolve_left (not_not.mpr ht₀)
    have hs₁ : (⨅ l, LinearMap.ker (M.B l)) = ⊥ := by
      by_contra h
      exact c₁ ⟨h, ht₁⟩
    obtain ⟨f, hf, hns⟩ := M.swap.exists_ne_smul_id_main hij hl h₁ h₀ hpre.swap
      (fun l l' ↦ hnil.isNilpotent_A_comp_B l l') hs₁ ht₀ hs₀ ht₁
    refine ⟨(f.2, f.1), mem_Hom_of_mem_Hom_swap hf, fun c hc ↦ hns c ?_⟩
    exact Prod.ext (congrArg Prod.snd hc) (congrArg Prod.fst hc)

end Exclusion

end Quiver.Kronecker.DoubledRep
