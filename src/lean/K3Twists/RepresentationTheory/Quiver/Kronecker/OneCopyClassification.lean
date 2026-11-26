/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.Dual.PairOrbit
import K3Twists.RepresentationTheory.Quiver.Kronecker.TwoExtensions

/-!
# Semirigid wall objects with one copy of a spherical simple

Let `S`, `U` be distinct spherical simples of one phase with `dim Ext¹(U, S) = 2`, and model the
wall objects in which `U` occurs once and `S` occurs `p` times as in
`RepresentationTheory/Quiver/Kronecker/TwoExtensions.lean`: nilpotent representations
`M : DoubledRep k ι V k` with the preprojective relations, `|ι| = 2`, `dim V = p`. By
Riemann–Roch such an `M` is semirigid (`e(M) = 2`) exactly when `dim End M + p(2 - p) = 2`, and
for `p ≥ 2` it then has rank-one classes: `A_i = α_i φ`, `B_i 1 = β_i w` with `∑ α_i β_i = 0` and
`φ(w) = 0` (`DoubledRep.oneCopy_two_rankOne`).

This file finishes the classification of these objects (the Proposition "All multiplicities with
one copy of a simple" of the notes on pairing-two walls, in the model).

* `DoubledRep.lengthThree α β`: the length-three object `M_α` on `(k², k)`, `A_i(x, y) = α_i y`,
  `B_i t = (β_i t, 0)`, uniserial with composition factors `S, U, S`; `DoubledRep.addSimple M W`:
  the sum of `M` with `dim W` copies of the simple `S` at vertex zero.
* `DoubledRep.nonempty_iso_lengthThree_addSimple`: **the decomposition.** A semirigid `M` with
  `p ≥ 2` is isomorphic to `M_α ⊕ S^{p-2}`, where `kα` is the line of its classes `A_i` and `β` is
  orthogonal to `α`. The proof is the transitivity of `GL(V)` on pairs `(φ, w)` with `φ(w) = 0`
  (`LinearMap.exists_linearEquiv_of_apply_eq_zero`).
* `DoubledRep.lengthThree_addSimple_isPreprojective`, `lengthThree_addSimple_isNilpotent`,
  `lengthThree_addSimple_semirigid`: conversely every `M_α ⊕ S^{m}` with `β ⊥ α`, `α, β ≠ 0` and
  `g = 2` is a semirigid wall object, so the classification is exact.
* `DoubledRep.Iso.range_evalA_eq`: an isomorphism of representations with a line at vertex one
  preserves the line of the classes `A_i`, with no relation used.
* `DoubledRep.nonempty_iso_iff_range_evalA_eq`: **the isomorphism class is determined by the
  line.** Two semirigid wall objects with the same `p ≥ 2` are isomorphic iff their classes `A_i`
  span the same line.

The notes parametrize `M_α` by the line `[α] ∈ ℙ(Ext¹(U, S))` of the class of its length-two
subobject; in the model that is the line of the classes `B_i`, which for `g = 2` is the orthogonal
of the line of the classes `A_i` used here (`DoubledRep.mem_span_of_sum_mul_eq_zero`), so the two
parametrizations agree.
-/

open Module

namespace Quiver.Kronecker.DoubledRep

variable {k ι : Type*} [Field k]

/-! ### The length-three object and the simple summands -/

section Model

variable {V₀ V₁ : Type*} [AddCommGroup V₀] [Module k V₀] [AddCommGroup V₁] [Module k V₁]

/-- `M ⊕ S ⊗ W`: the direct sum of `M` with `dim W` copies of the simple `S` at vertex zero. -/
def addSimple (M : DoubledRep k ι V₀ V₁) (W : Type*) [AddCommGroup W] [Module k W] :
    DoubledRep k ι (V₀ × W) V₁ where
  A i := M.A i ∘ₗ LinearMap.fst k V₀ W
  B i := LinearMap.inl k V₀ W ∘ₗ M.B i

@[simp]
lemma addSimple_A_apply (M : DoubledRep k ι V₀ V₁) (W : Type*) [AddCommGroup W] [Module k W]
    (i : ι) (x : V₀ × W) : (M.addSimple W).A i x = M.A i x.1 :=
  rfl

@[simp]
lemma addSimple_B_apply (M : DoubledRep k ι V₀ V₁) (W : Type*) [AddCommGroup W] [Module k W]
    (i : ι) (y : V₁) : (M.addSimple W).B i y = (M.B i y, 0) :=
  rfl

/-- **The length-three object** `M_α` on `(k², k)`: `A_i(x, y) = α_i y` and `B_i t = (β_i t, 0)`.
For `α, β ≠ 0` it is uniserial with composition factors `S, U, S`: its socle is the line `k × 0`
at vertex zero, the image of the classes `B_i`, and its top is the quotient by `k × 0 ⊕ k`. -/
def lengthThree (α β : ι → k) : DoubledRep k ι (k × k) k where
  A i := α i • LinearMap.snd k k k
  B i := β i • LinearMap.inl k k k

@[simp]
lemma lengthThree_A_apply (α β : ι → k) (i : ι) (x : k × k) :
    (lengthThree α β).A i x = α i * x.2 :=
  rfl

@[simp]
lemma lengthThree_B_apply (α β : ι → k) (i : ι) (t : k) :
    (lengthThree α β).B i t = (β i * t, 0) := by
  simp [lengthThree]

variable [Fintype ι]

/-- `M_α ⊕ S^m` satisfies the preprojective relations exactly when `∑ α_i β_i = 0`; here the
direction that is used. -/
theorem lengthThree_addSimple_isPreprojective {α β : ι → k} (h : ∑ i, α i * β i = 0)
    (W : Type*) [AddCommGroup W] [Module k W] :
    ((lengthThree α β).addSimple W).IsPreprojective := by
  refine ⟨LinearMap.ext fun x ↦ ?_, LinearMap.ext fun t ↦ ?_⟩
  · simp only [LinearMap.sum_apply, LinearMap.comp_apply, addSimple_A_apply, addSimple_B_apply,
      lengthThree_A_apply, lengthThree_B_apply, LinearMap.zero_apply]
    have : ∑ i, ((β i * (α i * x.1.2), (0 : k)), (0 : W)) =
        (((∑ i, α i * β i) * x.1.2, 0), 0) := by
      rw [Prod.ext_iff]
      refine ⟨Prod.ext ?_ ?_, ?_⟩
      · simp only [Prod.fst_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ ↦ by ring
      · simp [Prod.snd_sum, Prod.fst_sum]
      · simp [Prod.snd_sum]
    rw [this, h, zero_mul]
    rfl
  · simp [lengthThree]

omit [Fintype ι] in
/-- `M_α ⊕ S^m` is nilpotent: every path of length three acts by zero, since `A_i B_j = 0`. -/
theorem lengthThree_addSimple_isNilpotent (α β : ι → k) (W : Type*) [AddCommGroup W]
    [Module k W] : ((lengthThree α β).addSimple W).IsNilpotent := by
  set M := (lengthThree α β).addSimple W
  have h3 : ∀ a b c : ι ⊕ ι, M.arrow a * M.arrow b * M.arrow c = 0 := by
    intro a b c
    refine LinearMap.ext fun x ↦ ?_
    rcases a with i | i <;> rcases b with j | j <;> rcases c with l | l <;>
      simp [M, mul_apply_eq_comp]
  refine ⟨3, fun w hw ↦ ?_⟩
  obtain ⟨a, b, c, w', rfl⟩ : ∃ a b c w', w = a :: b :: c :: w' := by
    match w, hw with
    | a :: b :: c :: w', _ => exact ⟨a, b, c, w', rfl⟩
  simp only [List.map_cons, List.prod_cons, ← mul_assoc, h3, zero_mul]

end Model

/-! ### The line of the classes `A_i` -/

section Line

variable {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- **An isomorphism preserves the line of the classes `A_i`.** For representations with a line at
vertex one, the equivalence at vertex one is multiplication by a nonzero scalar `c`, and
`evalA ∘ e₀ = c • evalA`, so the two images agree. No relation is used. -/
theorem Iso.range_evalA_eq {M : DoubledRep k ι V k} {N : DoubledRep k ι W k} (u : Iso M N) :
    LinearMap.range M.evalA = LinearMap.range N.evalA := by
  set c : k := u.e₁ 1
  have hc : c ≠ 0 := fun h ↦ one_ne_zero (u.e₁.injective (by rw [map_zero]; exact h))
  have he₁ : ∀ t, u.e₁ t = c * t := fun t ↦ by
    rw [show t = t • (1 : k) by simp, map_smul, smul_eq_mul, smul_eq_mul, mul_one, mul_comm]
  have hN : ∀ x, N.evalA (u.e₀ x) = c • M.evalA x := fun x ↦ funext fun i ↦ by
    simp only [evalA_apply, Pi.smul_apply, smul_eq_mul, ← u.comm_A, he₁]
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    refine ⟨u.e₀ (c⁻¹ • x), ?_⟩
    rw [hN, map_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]
  · rintro _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := u.e₀.surjective y
    exact ⟨c • x, by rw [hN, map_smul]⟩

/-- In the rank-one form `A_i = α_i φ` with `φ ≠ 0`, the classes `A_i` span the line `kα`. -/
lemma range_evalA_eq_span_of_rankOne {M : DoubledRep k ι V k} {φ : V →ₗ[k] k} {α : ι → k}
    (hφ : φ ≠ 0) (hA : ∀ i v, M.A i v = α i * φ v) : LinearMap.range M.evalA = k ∙ α := by
  obtain ⟨v₀, hv₀⟩ : ∃ v, φ v ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ (LinearMap.ext h)
  refine le_antisymm ?_ ?_
  · rintro _ ⟨v, rfl⟩
    exact Submodule.mem_span_singleton.mpr ⟨φ v, funext fun i ↦ by simp [hA, mul_comm]⟩
  · rw [Submodule.span_singleton_le_iff_mem]
    exact ⟨(φ v₀)⁻¹ • v₀, funext fun i ↦ by simp [hA, hv₀]⟩

variable [Fintype ι]

/-- **For `g = 2` the orthogonal of a nonzero `α` is a line**: two vectors `β ≠ 0` and `β'`
orthogonal to `α` for `∑ α_i β_i` are proportional. -/
theorem mem_span_of_sum_mul_eq_zero (hι : Fintype.card ι = 2) {α β β' : ι → k} (hα : α ≠ 0)
    (hβ : β ≠ 0) (h : ∑ i, α i * β i = 0) (h' : ∑ i, α i * β' i = 0) : β' ∈ k ∙ β := by
  classical
  let f : Module.Dual k (ι → k) := Fintype.linearCombination k α
  have hf : ∀ γ, f γ = ∑ i, α i * γ i := fun γ ↦ by
    simp [f, Fintype.linearCombination_apply, mul_comm]
  have hf0 : f ≠ 0 := by
    obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hα (funext hc)
    intro h0
    have := LinearMap.congr_fun h0 (Pi.single i 1)
    rw [hf] at this
    simp [Pi.single_apply, hi] at this
  have hker : finrank k (LinearMap.ker f) = 1 := by
    have := Module.Dual.finrank_ker_add_one_of_ne_zero hf0
    rw [Module.finrank_fintype_fun_eq_card, hι] at this
    omega
  have hβk : β ∈ LinearMap.ker f := by rw [LinearMap.mem_ker, hf]; exact h
  have hβ'k : β' ∈ LinearMap.ker f := by rw [LinearMap.mem_ker, hf]; exact h'
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_ne_zero' (⟨β, hβk⟩ : LinearMap.ker f)
    (fun h0 ↦ hβ (congrArg Subtype.val h0))).mp hker ⟨β', hβ'k⟩
  exact Submodule.mem_span_singleton.mpr ⟨c, congrArg Subtype.val hc⟩

end Line

/-! ### The classification -/

section Classification

variable [Fintype ι] {V W : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup W] [Module k W] [FiniteDimensional k W]

/-- The model space `k² × k^{p-2}` of `M_α ⊕ S^{p-2}` has dimension `p` for `p ≥ 2`. -/
lemma finrank_lengthThree_space {p : ℕ} (hp : 2 ≤ p) :
    finrank k ((k × k) × (Fin (p - 2) → k)) = p := by
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_self, Module.finrank_fin_fun]
  omega

/-- **The decomposition `M ≅ M_α ⊕ S^{p-2}`.** A semirigid wall object with one copy of the
spherical simple `U` and `p ≥ 2` copies of `S` (a nilpotent representation with the preprojective
relations and `dim End M + p(g - p) = 2`) is isomorphic to `M_α ⊕ S^{p-2}` for the line `kα`
spanned by its classes `A_i` and some `β ≠ 0` orthogonal to `α`. -/
theorem nonempty_iso_lengthThree_addSimple {M : DoubledRep k ι V k} (hpre : M.IsPreprojective)
    (hnil : M.IsNilpotent)
    (he : (finrank k (Hom M M) : ℤ) + finrank k V * (Fintype.card ι - finrank k V) = 2)
    (hp : 2 ≤ finrank k V) :
    Fintype.card ι = 2 ∧ ∃ α β : ι → k, α ≠ 0 ∧ β ≠ 0 ∧ ∑ i, α i * β i = 0 ∧
      LinearMap.range M.evalA = k ∙ α ∧
      Nonempty (Iso ((lengthThree α β).addSimple (Fin (finrank k V - 2) → k)) M) := by
  obtain ⟨hg, φ, α, w, β, hφ, hα, hw, hβ, hA, hB, hαβ, hφw⟩ :=
    M.oneCopy_two_rankOne hpre hnil he hp
  refine ⟨hg, α, β, hα, hβ, hαβ, range_evalA_eq_span_of_rankOne hφ hA, ?_⟩
  let φT : ((k × k) × (Fin (finrank k V - 2) → k)) →ₗ[k] k :=
    LinearMap.snd k k k ∘ₗ LinearMap.fst k (k × k) _
  let wT : ((k × k) × (Fin (finrank k V - 2) → k)) :=
    ((1, 0), 0)
  have hφT : φT ≠ 0 := fun h0 ↦ one_ne_zero (LinearMap.congr_fun h0 ((0, 1), 0))
  have hwT : wT ≠ 0 := fun h0 ↦ by
    simpa [wT] using congrArg (fun x : ((k × k) × (Fin (finrank k V - 2) → k)) ↦ x.1.1) h0
  have hφwT : φT wT = 0 := rfl
  have hdimT : finrank k ((k × k) × (Fin (finrank k V - 2) → k)) = finrank k V :=
    finrank_lengthThree_space hp
  obtain ⟨e, he₁, hew⟩ := LinearMap.exists_linearEquiv_of_apply_eq_zero
    (V := ((k × k) × (Fin (finrank k V - 2) → k))) (V' := V) hdimT hφT hwT hφwT hφ hw hφw
  refine ⟨⟨e, LinearEquiv.refl k k, fun i x ↦ ?_, fun i t ↦ ?_⟩⟩
  · rw [LinearEquiv.refl_apply, hA, he₁]
    rfl
  · have hx : ((lengthThree α β).addSimple (Fin (finrank k V - 2) → k)).B i t =
        (β i * t) • wT := by
      simp [wT]
    rw [hx, map_smul, hew, LinearEquiv.refl_apply, M.B_apply, hB, smul_smul, mul_comm]

/-- **The converse**: `M_α ⊕ S^m` with `α, β ≠ 0` and `β ⊥ α` is a semirigid wall object when
`g = 2`: `dim End + p(2 - p) = 2` with `p = m + 2`. -/
theorem lengthThree_addSimple_semirigid {α β : ι → k} (hα : α ≠ 0) (hβ : β ≠ 0)
    (hι : Fintype.card ι = 2) (m : ℕ) :
    (finrank k (Hom ((lengthThree α β).addSimple (Fin m → k))
        ((lengthThree α β).addSimple (Fin m → k))) : ℤ) +
      finrank k ((k × k) × (Fin m → k)) *
        (Fintype.card ι - finrank k ((k × k) × (Fin m → k))) = 2 := by
  set T := (k × k) × (Fin m → k)
  let φT : T →ₗ[k] k := LinearMap.snd k k k ∘ₗ LinearMap.fst k (k × k) _
  let wT : T := ((1, 0), 0)
  have h := ((lengthThree α β).addSimple (Fin m → k)).oneCopy_of_rankOne φT α wT β
    (fun h0 ↦ one_ne_zero (LinearMap.congr_fun h0 ((0, 1), 0)))
    hα (fun h0 ↦ by simpa [wT] using congrArg (fun x : T ↦ x.1.1) h0) hβ
    (fun i v ↦ by simp [φT]) (fun i ↦ by simp [wT])
  rw [h, hι]
  norm_num

/-- **The isomorphism class is determined by the line.** Two semirigid wall objects with one copy
of `U` and the same number `p ≥ 2` of copies of `S` are isomorphic iff their classes `A_i` span the
same line. -/
theorem nonempty_iso_iff_range_evalA_eq {M : DoubledRep k ι V k} {N : DoubledRep k ι W k}
    (hpreM : M.IsPreprojective) (hnilM : M.IsNilpotent)
    (heM : (finrank k (Hom M M) : ℤ) + finrank k V * (Fintype.card ι - finrank k V) = 2)
    (hpreN : N.IsPreprojective) (hnilN : N.IsNilpotent)
    (heN : (finrank k (Hom N N) : ℤ) + finrank k W * (Fintype.card ι - finrank k W) = 2)
    (hdim : finrank k V = finrank k W) (hp : 2 ≤ finrank k V) :
    Nonempty (Iso M N) ↔ LinearMap.range M.evalA = LinearMap.range N.evalA := by
  refine ⟨fun ⟨u⟩ ↦ u.range_evalA_eq, fun hline ↦ ?_⟩
  obtain ⟨hg, φ, α, w, β, hφ, hα, hw, hβ, hA, hB, hαβ, hφw⟩ :=
    M.oneCopy_two_rankOne hpreM hnilM heM hp
  obtain ⟨-, φ', α', w', β', hφ', hα', hw', hβ', hA', hB', hαβ', hφw'⟩ :=
    N.oneCopy_two_rankOne hpreN hnilN heN (hdim ▸ hp)
  -- the two lines of classes `A_i` agree, so `α' = c α` with `c ≠ 0`
  rw [range_evalA_eq_span_of_rankOne hφ hA, range_evalA_eq_span_of_rankOne hφ' hA'] at hline
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hline ▸ Submodule.mem_span_singleton_self α')
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hα' (by rw [← hc, zero_smul])
  -- the classes `B_i` are orthogonal to `α` on both sides, so `β' = d β` with `d ≠ 0`
  have hαβ'' : ∑ i, α i * β' i = 0 := by
    have : ∑ i, α' i * β' i = c * ∑ i, α i * β' i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [← hc, Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [this] at hαβ'
    exact (mul_eq_zero.mp hαβ').resolve_left hc0
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp
    (mem_span_of_sum_mul_eq_zero hg hα hβ hαβ hαβ'')
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hβ' (by rw [← hd, zero_smul])
  -- the orbit lemma for `(φ, w)` and `(c φ', d w')`
  have hcφ' : c • φ' ≠ 0 := smul_ne_zero hc0 hφ'
  have hdw' : d • w' ≠ 0 := smul_ne_zero hd0 hw'
  obtain ⟨e, he₁, hew⟩ := LinearMap.exists_linearEquiv_of_apply_eq_zero hdim hφ hw hφw hcφ' hdw'
    (by simp [hφw'])
  refine ⟨⟨e, LinearEquiv.refl k k, fun i x ↦ ?_, fun i t ↦ ?_⟩⟩
  · rw [LinearEquiv.refl_apply, hA, hA', ← he₁ x, ← hc]
    simp only [Pi.smul_apply, smul_eq_mul, LinearMap.smul_apply]
    ring
  · rw [M.B_apply, hB, LinearEquiv.refl_apply, N.B_apply, hB', ← hd]
    simp only [smul_smul, Pi.smul_apply, smul_eq_mul, map_smul, hew]
    congr 1
    ring

end Classification

end Quiver.Kronecker.DoubledRep
