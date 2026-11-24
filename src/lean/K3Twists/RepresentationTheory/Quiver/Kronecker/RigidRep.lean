/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.RepresentationTheory.Quiver.Kronecker.Preprojective

/-!
# A rigid preprojective representation with arrows in both directions

Let `ι` be a nonempty finite type with `g` elements, `W = k^ι` with basis `e_i`, and

  `H' = (W ⊗ W)/⟨∑ e_i ⊗ e_i⟩`,  `V₀ = H' ⊕ k·u`,  `V₁ = W`,
  `A_i(h + s u) = s e_i`,  `B_i(w) = [e_i ⊗ w]`.

This is a representation of the doubled `g`-Kronecker quiver of dimension vector `(g², g)`.

## Main results

* `rigidRep_isPreprojective`: the preprojective relations hold;
* `rigidRep_A_comp_B`, `rigidRep_isNilpotent`: `A_j B_i = 0`, so every path of length three
  vanishes;
* `finrank_rigidRep_End`: `dim End = g²`, the Tits form `q(g², g) = g⁴ + g² - g·g²·g`. An
  endomorphism acts by one scalar on `W` and on `H'`, with an arbitrary extra `H'`-component in
  the image of `u` (`RigidRep.eq_endOf`);
* `RigidRep.eq_top_or`: a subrepresentation `(U₀, U₁)` is everything, or `U₀ ⊆ H'`, with
  `U₀ = H'` if `U₁ = W` and `dim U₀ ≥ g·dim U₁` otherwise: `U₀` contains the image of
  `W ⊗ U₁`, of dimension `g·dim U₁` because the defining tensor `∑ e_i ⊗ e_i` has full rank;
* `RigidRep.dimVec_mem`: the dimension vector `(i, j)` of a subrepresentation is `(g², g)` or
  `(g² - 1, g)`, or satisfies `j < g` and `g·j ≤ i ≤ g² - 1`;
* `RigidRep.dimVec_upper`, `RigidRep.dimVec_upper_eq`: the points `(i + j, j)` lie on or below
  the path `(0, 0) → (g² + g - 1, g) → (g² + g, g)`, and only `0` and `(H', W)` lie on its
  slanted edge;
* `RigidRep.dimVec_lower`, `RigidRep.dimVec_lower_eq`: they lie on or above the path
  `(0, 0) → (g² - 1, 0) → (g² + g, g)`, and only `(H', 0)` and `M` lie on its slanted edge;
* `RigidRep.dimVec_upperCorner`, `RigidRep.dimVec_lowerCorner`: the corners are the
  subrepresentations `(H', W)` and `(H', 0)`, of dimension vectors `(g² - 1, g)` and
  `(g² - 1, 0)`.

## Implementation notes

`W ⊗ W` is modeled as the arrays `ι → ι → k`, that is `ι → W`: the tensor `e_i ⊗ w` is the array
whose row `i` is `w` and whose other rows vanish, so `∑ e_i ⊗ e_i` is the identity array
`RigidRep.diag`. The vertex-zero space is `H' × k`, with `u = (0, 1)`.
-/

namespace Quiver.Kronecker

open Module

variable (k : Type*) [Field k] (ι : Type*) [DecidableEq ι]

namespace RigidRep

/-- The identity tensor `∑ e_i ⊗ e_i`: the array whose row `i` is `e_i`. -/
def diag : ι → ι → k := fun i ↦ Pi.single i 1

/-- The quotient `H' = (W ⊗ W)/⟨∑ e_i ⊗ e_i⟩`. -/
abbrev H : Type _ := (ι → ι → k) ⧸ Submodule.span k {diag k ι}

end RigidRep

open RigidRep

/-- The rigid representation of dimension vector `(g², g)` with arrows in both directions:
`V₀ = H' × k`, `V₁ = W`, `A_i (h, s) = s e_i` and `B_i w = ([e_i ⊗ w], 0)`. -/
noncomputable def rigidRep : DoubledRep k ι (H k ι × k) (ι → k) where
  A i := LinearMap.smulRight (LinearMap.snd k (H k ι) k) (Pi.single i 1)
  B i := LinearMap.inl k (H k ι) k ∘ₗ (Submodule.span k {diag k ι}).mkQ ∘ₗ
    LinearMap.single k (fun _ : ι ↦ ι → k) i

variable {k ι}

@[simp]
lemma rigidRep_A_apply (i : ι) (v : H k ι × k) :
    (rigidRep k ι).A i v = v.2 • Pi.single i 1 := rfl

@[simp]
lemma rigidRep_B_apply (i : ι) (w : ι → k) :
    (rigidRep k ι).B i w = (Submodule.Quotient.mk (Pi.single i w), 0) := rfl

/-- `A_j B_i = 0`: every path of length two starting at vertex one vanishes. -/
theorem rigidRep_A_comp_B (i j : ι) : (rigidRep k ι).A j ∘ₗ (rigidRep k ι).B i = 0 := by
  ext w
  simp

/-- Every path of length three vanishes, so the representation is nilpotent. -/
theorem rigidRep_isNilpotent : (rigidRep k ι).IsNilpotent := by
  refine ⟨3, fun w hw ↦ ?_⟩
  rcases w with _ | ⟨a, _ | ⟨b, _ | ⟨c, w⟩⟩⟩
  · simp at hw
  · simp at hw
  · simp at hw
  have h3 : (rigidRep k ι).arrow a * ((rigidRep k ι).arrow b * (rigidRep k ι).arrow c) = 0 := by
    refine LinearMap.ext fun x ↦ ?_
    rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;> simp
  rw [List.map_cons, List.map_cons, List.map_cons, List.prod_cons, List.prod_cons,
    List.prod_cons, ← mul_assoc, ← mul_assoc, mul_assoc _ _ ((rigidRep k ι).arrow c), h3,
    zero_mul]

namespace RigidRep

variable [Fintype ι]

lemma sum_single_eq (w : ι → k) : ∑ i, w i • (Pi.single i 1 : ι → k) = w := by
  conv_rhs => rw [← Finset.univ_sum_single w]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Pi.single_smul', smul_eq_mul, mul_one]

/-- A subspace of `W` containing every `e_i` is `W`. -/
lemma eq_top_of_single_mem {U : Submodule k (ι → k)} (h : ∀ i, (Pi.single i 1 : ι → k) ∈ U) :
    U = ⊤ := by
  refine eq_top_iff.mpr fun w _ ↦ ?_
  rw [← sum_single_eq w]
  exact U.sum_mem fun i _ ↦ U.smul_mem _ (h i)

omit [DecidableEq ι] in
lemma mk_sum {M : Type*} [AddCommGroup M] [Module k M] (p : Submodule k M) (f : ι → M) :
    (Submodule.Quotient.mk (∑ i, f i) : M ⧸ p) = ∑ i, Submodule.Quotient.mk (f i) :=
  map_sum p.mkQ f Finset.univ

omit [Fintype ι] in
lemma mk_diag : (Submodule.Quotient.mk (diag k ι) : H k ι) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_span_singleton_self _)

omit [Fintype ι] in
lemma diag_ne_zero [Nonempty ι] : diag k ι ≠ 0 := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  intro h
  have := congrFun (congrFun h i) i
  simp [diag] at this

/-- `dim H' = g² - 1`. -/
lemma finrank_H [Nonempty ι] : finrank k (H k ι) = Fintype.card ι ^ 2 - 1 := by
  have h : finrank k (H k ι) + finrank k (Submodule.span k {diag k ι}) =
      finrank k (ι → ι → k) := Submodule.finrank_quotient_add_finrank _
  rw [finrank_span_singleton (diag_ne_zero (k := k)), Module.finrank_pi_fintype] at h
  simp only [Module.finrank_pi, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  rw [sq]
  omega

/-- A subspace of `H'` containing every class `[e_i ⊗ w]` is `H'`. -/
lemma mem_of_forall_mk_single_mem {U : Submodule k (H k ι)}
    (h : ∀ i (w : ι → k), (Submodule.Quotient.mk (Pi.single i w) : H k ι) ∈ U) (x : H k ι) :
    x ∈ U := by
  induction x using Submodule.Quotient.induction_on with
  | H m =>
    rw [← Finset.univ_sum_single m, ← Submodule.mkQ_apply, map_sum]
    exact U.sum_mem fun i _ ↦ h i (m i)

end RigidRep

variable [Fintype ι]

/-- The preprojective relations hold. -/
theorem rigidRep_isPreprojective : (rigidRep k ι).IsPreprojective := by
  refine ⟨LinearMap.ext fun v ↦ ?_, LinearMap.ext fun w ↦ ?_⟩
  · have hsum : ∑ i, (Pi.single i (v.2 • Pi.single i (1 : k)) : ι → ι → k) = v.2 • diag k ι :=
      Finset.univ_sum_single (v.2 • diag k ι)
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, rigidRep_A_apply, rigidRep_B_apply,
      LinearMap.zero_apply]
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_sum, Prod.fst_zero, ← mk_sum, hsum, Submodule.Quotient.mk_smul, mk_diag,
        smul_zero]
    · rw [Prod.snd_sum]
      simp
  · simp

/-! ### Endomorphisms -/

namespace RigidRep

/-- The endomorphism `endOf (c, h₀)`: multiplication by `c` on `W` and on `H'`, and
`u ↦ c u + h₀`. -/
noncomputable def endOf : k × H k ι →ₗ[k] Module.End k (H k ι × k) × Module.End k (ι → k) :=
  (LinearMap.fst k k (H k ι)).smulRight (LinearMap.id, LinearMap.id) +
    LinearMap.inl k _ _ ∘ₗ (LinearMap.smulRightₗ (LinearMap.snd k (H k ι) k) ∘ₗ
      LinearMap.inl k (H k ι) k) ∘ₗ LinearMap.snd k k (H k ι)

omit [Fintype ι] in
lemma endOf_fst_apply (p : k × H k ι) (v : H k ι × k) :
    (endOf p).1 v = (p.1 • v.1 + v.2 • p.2, p.1 • v.2) := by
  ext <;> simp [endOf]

omit [Fintype ι] in
lemma endOf_snd_apply (p : k × H k ι) (w : ι → k) : (endOf p).2 w = p.1 • w := by
  simp [endOf]

omit [Fintype ι] in
lemma endOf_mem (p : k × H k ι) : endOf p ∈ DoubledRep.Hom (rigidRep k ι) (rigidRep k ι) := by
  refine fun i ↦ ⟨LinearMap.ext fun v ↦ ?_, LinearMap.ext fun w ↦ ?_⟩
  · simp only [LinearMap.comp_apply, rigidRep_A_apply, endOf_fst_apply, endOf_snd_apply,
      smul_smul, smul_eq_mul]
  · simp only [LinearMap.comp_apply, rigidRep_B_apply, endOf_fst_apply, endOf_snd_apply,
      zero_smul, add_zero, smul_zero, Pi.single_smul', Submodule.Quotient.mk_smul]

omit [Fintype ι] in
lemma endOf_injective [Nonempty ι] : Function.Injective (endOf (k := k) (ι := ι)) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro p hp
  rw [LinearMap.mem_ker] at hp
  obtain ⟨i⟩ := ‹Nonempty ι›
  have h₁ := congrFun (LinearMap.congr_fun (congrArg Prod.snd hp) (Pi.single i 1)) i
  have h₀ := LinearMap.congr_fun (congrArg Prod.fst hp) (0, 1)
  simp only [endOf_snd_apply, Prod.snd_zero, LinearMap.zero_apply, Pi.smul_apply,
    Pi.single_eq_same, smul_eq_mul, mul_one, Pi.zero_apply] at h₁
  simp only [endOf_fst_apply, smul_zero, one_smul, zero_add, Prod.fst_zero,
    LinearMap.zero_apply, Prod.mk_eq_zero] at h₀
  exact Prod.ext h₁ h₀.1

/-- Every endomorphism is some `endOf (c, h₀)`: it is the scalar `c` on `W`, read off from the
image of `u`, and then the scalar `c` on `H'`, which is spanned by the classes `B_i w`. -/
lemma eq_endOf [Nonempty ι] {f : Module.End k (H k ι × k) × Module.End k (ι → k)}
    (hf : f ∈ DoubledRep.Hom (rigidRep k ι) (rigidRep k ι)) :
    f = endOf ((f.1 (0, 1)).2, (f.1 (0, 1)).1) := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  set c := (f.1 (0, 1)).2
  -- `f₁ e_i = c e_i`, from `f₁ A_i = A_i f₀` at `u`.
  have hA : ∀ i, f.2 (Pi.single i 1) = c • Pi.single i 1 := fun i ↦ by
    have := LinearMap.congr_fun ((hf i).1) (0, 1)
    simpa using this
  have h₁ : f.2 = c • LinearMap.id := by
    refine LinearMap.ext fun w ↦ ?_
    have hw := sum_single_eq w
    calc f.2 w = f.2 (∑ i, w i • Pi.single i 1) := by rw [hw]
      _ = c • ∑ i, w i • Pi.single i 1 := by
        simp only [map_sum, map_smul, hA, Finset.smul_sum, smul_comm c]
      _ = (c • LinearMap.id) w := by rw [hw]; rfl
  -- `f₀` maps `H'` into `H'`, from `f₁ A_i = A_i f₀` on `H'`.
  have hsnd : ∀ h : H k ι, (f.1 (h, 0)).2 = 0 := fun h ↦ by
    have := congrFun (LinearMap.congr_fun ((hf i₀).1) (h, 0)) i₀
    simpa using this.symm
  -- `f₀` is `c` on `H'`, from `f₀ B_i = B_i f₁`.
  have hfst : ∀ h : H k ι, f.1 (h, 0) = (c • h, 0) := fun h ↦ by
    have hmem := mem_of_forall_mk_single_mem
      (U := LinearMap.ker ((LinearMap.fst k (H k ι) k) ∘ₗ f.1 ∘ₗ LinearMap.inl k (H k ι) k -
        c • LinearMap.id)) (fun i w ↦ by
          have := LinearMap.congr_fun ((hf i).2) w
          simp only [LinearMap.comp_apply, rigidRep_B_apply, h₁, LinearMap.smul_apply,
            LinearMap.id_apply, Pi.single_smul', Submodule.Quotient.mk_smul] at this
          simp [LinearMap.mem_ker, this]) h
    rw [LinearMap.mem_ker] at hmem
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.inl_apply,
      LinearMap.fst_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hmem
    exact Prod.ext hmem (hsnd h)
  refine Prod.ext (LinearMap.ext fun v ↦ ?_) (LinearMap.ext fun w ↦ ?_)
  · have hv : v = (v.1, 0) + v.2 • ((0 : H k ι), (1 : k)) := by
      ext <;> simp
    rw [hv, map_add, map_smul, hfst, endOf_fst_apply]
    ext <;> simp [c, mul_comm]
  · rw [h₁, endOf_snd_apply]
    rfl

end RigidRep

open RigidRep in
/-- `dim End = g²`: the endomorphisms are the pairs `endOf (c, h₀)`, `c ∈ k`, `h₀ ∈ H'`. -/
theorem finrank_rigidRep_End [Nonempty ι] :
    finrank k (DoubledRep.Hom (rigidRep k ι) (rigidRep k ι)) = Fintype.card ι ^ 2 := by
  have hrange : LinearMap.range (endOf (k := k) (ι := ι)) =
      DoubledRep.Hom (rigidRep k ι) (rigidRep k ι) := by
    refine le_antisymm ?_ fun f hf ↦ ?_
    · rintro _ ⟨p, rfl⟩
      exact endOf_mem p
    · exact ⟨_, (eq_endOf hf).symm⟩
  rw [← hrange, LinearMap.finrank_range_of_inj endOf_injective, Module.finrank_prod,
    Module.finrank_self, finrank_H]
  have : 1 ≤ Fintype.card ι ^ 2 := Nat.one_le_pow _ _ Fintype.card_pos
  omega

/-! ### Subrepresentations -/

namespace RigidRep

/-- The subrepresentation `(H', W)`: the corner of the upper boundary. -/
def upperCorner : (rigidRep k ι).subreps :=
  ⟨(LinearMap.range (LinearMap.inl k (H k ι) k), ⊤), fun i ↦
    ⟨fun _ _ ↦ Submodule.mem_top, fun w _ ↦ ⟨_, (rigidRep_B_apply i w).symm⟩⟩⟩

/-- The subrepresentation `(H', 0)`: the corner of the lower boundary. -/
def lowerCorner : (rigidRep k ι).subreps :=
  ⟨(LinearMap.range (LinearMap.inl k (H k ι) k), ⊥), fun i ↦
    ⟨by rintro _ ⟨h, rfl⟩; simp, fun w hw ↦ by simp [(Submodule.mem_bot k).mp hw]⟩⟩

/-- If the vertex-one subspace is `W`, the vertex-zero subspace contains `H'`. -/
lemma inl_mem_of_snd_eq_top {N : (rigidRep k ι).subreps}
    (hN : (N : Submodule k (H k ι × k) × Submodule k (ι → k)).2 = ⊤) (h : H k ι) :
    ((h, 0) : H k ι × k) ∈ (N : Submodule k (H k ι × k) × Submodule k (ι → k)).1 := by
  have := mem_of_forall_mk_single_mem (U := (N : Submodule k (H k ι × k) × _).1.comap
    (LinearMap.inl k (H k ι) k)) (fun i w ↦ by
      have := DoubledRep.B_mem N i (hN ▸ Submodule.mem_top : w ∈ _)
      simpa using this) h
  simpa using this

/-- If the vertex-one subspace `U₁` is not `W`, then the vertex-zero subspace has dimension at
least `g·dim U₁`: the arrays with rows in `U₁` (the image of `W ⊗ U₁`) map injectively to `H'`,
since the identity array has rows spanning `W`. -/
lemma card_mul_finrank_le {N : (rigidRep k ι).subreps}
    (hN : (N : Submodule k (H k ι × k) × Submodule k (ι → k)).2 ≠ ⊤) :
    Fintype.card ι * finrank k (N : Submodule k (H k ι × k) × Submodule k (ι → k)).2 ≤
      finrank k (N : Submodule k (H k ι × k) × Submodule k (ι → k)).1 := by
  set U₀ := (N : Submodule k (H k ι × k) × Submodule k (ι → k)).1
  set U₁ := (N : Submodule k (H k ι × k) × Submodule k (ι → k)).2
  let Φ : (ι → U₁) →ₗ[k] H k ι × k := LinearMap.inl k (H k ι) k ∘ₗ
    (Submodule.span k {diag k ι}).mkQ ∘ₗ LinearMap.pi fun i ↦ U₁.subtype ∘ₗ LinearMap.proj i
  have hΦ : ∀ u, Φ u ∈ U₀ := fun u ↦ by
    have hu : Φ u = ∑ i, (rigidRep k ι).B i (u i) := by
      refine Prod.ext ?_ ?_
      · rw [Prod.fst_sum]
        simp only [rigidRep_B_apply]
        rw [← mk_sum, Finset.univ_sum_single (fun i ↦ (u i : ι → k))]
        rfl
      · rw [Prod.snd_sum]
        simp [Φ]
    rw [hu]
    exact U₀.sum_mem fun i _ ↦ DoubledRep.B_mem N i (u i).2
  have hinj : Function.Injective (LinearMap.codRestrict U₀ Φ hΦ) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro u hu
    rw [LinearMap.mem_ker, Subtype.ext_iff, LinearMap.codRestrict_apply] at hu
    simp only [Φ, LinearMap.comp_apply, LinearMap.inl_apply, Submodule.mkQ_apply,
      ZeroMemClass.coe_zero, Prod.mk_eq_zero, Submodule.Quotient.mk_eq_zero, and_true,
      Submodule.mem_span_singleton] at hu
    obtain ⟨c, hc⟩ := hu
    by_cases h0 : c = 0
    · funext i
      have := congrFun hc i
      simp only [h0, zero_smul, Pi.zero_apply, LinearMap.pi_apply, LinearMap.comp_apply,
        LinearMap.proj_apply, Submodule.subtype_apply] at this
      exact Subtype.ext this.symm
    · refine absurd (eq_top_of_single_mem fun i ↦ ?_) hN
      have := congrFun hc i
      simp only [Pi.smul_apply, diag, LinearMap.pi_apply, LinearMap.comp_apply,
        LinearMap.proj_apply, Submodule.subtype_apply] at this
      rw [← (U₁.smul_mem_iff h0), this]
      exact (u i).2
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul] at this

/-- **The subrepresentations.** A subrepresentation `(U₀, U₁)` is everything, or `U₀ ⊆ H'`; in
the second case `U₀ = H'` if `U₁ = W`, and `dim U₀ ≥ g·dim U₁` otherwise. -/
theorem eq_top_or (N : (rigidRep k ι).subreps) :
    N = ⊤ ∨ ((N : Submodule k (H k ι × k) × Submodule k (ι → k)).1 ≤
        LinearMap.range (LinearMap.inl k (H k ι) k) ∧
      ((N : Submodule k (H k ι × k) × Submodule k (ι → k)).2 = ⊤ →
        N = upperCorner) ∧
      ((N : Submodule k (H k ι × k) × Submodule k (ι → k)).2 ≠ ⊤ →
        Fintype.card ι * finrank k (N : Submodule k (H k ι × k) × Submodule k (ι → k)).2 ≤
          finrank k (N : Submodule k (H k ι × k) × Submodule k (ι → k)).1)) := by
  set U₀ := (N : Submodule k (H k ι × k) × Submodule k (ι → k)).1 with hU₀
  set U₁ := (N : Submodule k (H k ι × k) × Submodule k (ι → k)).2 with hU₁
  by_cases hv : ∃ v ∈ U₀, v.2 ≠ 0
  · -- A vector with nonzero `u`-component generates everything.
    obtain ⟨v, hv, hv2⟩ := hv
    left
    have htop₁ : U₁ = ⊤ := eq_top_of_single_mem fun i ↦ by
      have := DoubledRep.A_mem N i hv
      rwa [rigidRep_A_apply, U₁.smul_mem_iff hv2] at this
    have hinl : ∀ h : H k ι, ((h, 0) : H k ι × k) ∈ U₀ := inl_mem_of_snd_eq_top htop₁
    have hu : (((0 : H k ι), (1 : k)) : H k ι × k) ∈ U₀ := by
      have h1 : (((0 : H k ι), v.2) : H k ι × k) ∈ U₀ := by
        have := U₀.sub_mem hv (hinl v.1)
        rwa [show v - (v.1, 0) = ((0 : H k ι), v.2) from Prod.ext (sub_self _) (sub_zero _)]
          at this
      have := U₀.smul_mem v.2⁻¹ h1
      simpa [hv2] using this
    have htop₀ : U₀ = ⊤ := eq_top_iff.mpr fun x _ ↦ by
      have hx : x = (x.1, 0) + x.2 • ((0 : H k ι), (1 : k)) := by ext <;> simp
      rw [hx]
      exact U₀.add_mem (hinl x.1) (U₀.smul_mem _ hu)
    exact Subtype.ext (Prod.ext htop₀ htop₁)
  · simp only [not_exists, not_and, not_not] at hv
    right
    have hle : U₀ ≤ LinearMap.range (LinearMap.inl k (H k ι) k) := fun x hx ↦
      ⟨x.1, Prod.ext rfl (hv x hx).symm⟩
    refine ⟨hle, fun htop ↦ Subtype.ext (Prod.ext (le_antisymm hle ?_) htop),
      card_mul_finrank_le⟩
    rintro _ ⟨h, rfl⟩
    exact inl_mem_of_snd_eq_top htop h

variable [Nonempty ι]

lemma finrank_range_inl : finrank k (LinearMap.range (LinearMap.inl k (H k ι) k)) =
    Fintype.card ι ^ 2 - 1 := by
  rw [LinearMap.finrank_range_of_inj LinearMap.inl_injective, finrank_H]

lemma finrank_V₀ : finrank k (H k ι × k) = Fintype.card ι ^ 2 := by
  rw [Module.finrank_prod, finrank_H, Module.finrank_self]
  have : 1 ≤ Fintype.card ι ^ 2 := Nat.one_le_pow _ _ Fintype.card_pos
  omega

/-- The upper corner `(H', W)` has dimension vector `(g² - 1, g)`. -/
theorem dimVec_upperCorner :
    DoubledRep.dimVec (upperCorner : (rigidRep k ι).subreps) =
      (Fintype.card ι ^ 2 - 1, Fintype.card ι) := by
  show (finrank k (LinearMap.range (LinearMap.inl k (H k ι) k)),
    finrank k (⊤ : Submodule k (ι → k))) = _
  rw [finrank_range_inl, finrank_top, Module.finrank_pi]

/-- The lower corner `(H', 0)` has dimension vector `(g² - 1, 0)`. -/
theorem dimVec_lowerCorner :
    DoubledRep.dimVec (lowerCorner : (rigidRep k ι).subreps) = (Fintype.card ι ^ 2 - 1, 0) := by
  show (finrank k (LinearMap.range (LinearMap.inl k (H k ι) k)),
    finrank k (⊥ : Submodule k (ι → k))) = _
  rw [finrank_range_inl, finrank_bot]

/-- The whole representation has dimension vector `(g², g)`. -/
theorem dimVec_top :
    DoubledRep.dimVec (⊤ : (rigidRep k ι).subreps) = (Fintype.card ι ^ 2, Fintype.card ι) := by
  rw [DoubledRep.dimVec_top, finrank_V₀, Module.finrank_pi]

/-- **The dimension vectors of subrepresentations.** With `g = |ι|`, the dimension vector
`(i, j)` of a subrepresentation is `(g², g)` or `(g² - 1, g)`, or satisfies `j < g` and
`g·j ≤ i ≤ g² - 1`. -/
theorem dimVec_mem (N : (rigidRep k ι).subreps) :
    DoubledRep.dimVec N = (Fintype.card ι ^ 2, Fintype.card ι) ∨
      DoubledRep.dimVec N = (Fintype.card ι ^ 2 - 1, Fintype.card ι) ∨
      ((DoubledRep.dimVec N).2 < Fintype.card ι ∧
        Fintype.card ι * (DoubledRep.dimVec N).2 ≤ (DoubledRep.dimVec N).1 ∧
        (DoubledRep.dimVec N).1 ≤ Fintype.card ι ^ 2 - 1) := by
  rcases eq_top_or N with rfl | ⟨hle, htop, hne⟩
  · exact Or.inl dimVec_top
  · by_cases h : (N : Submodule k (H k ι × k) × Submodule k (ι → k)).2 = ⊤
    · rw [htop h]
      exact Or.inr (Or.inl dimVec_upperCorner)
    · refine Or.inr (Or.inr ⟨?_, hne h, ?_⟩)
      · have := Submodule.finrank_lt h
        rwa [Module.finrank_pi] at this
      · have := Submodule.finrank_mono hle
        rwa [finrank_range_inl] at this

omit [Nonempty ι] in
lemma eq_bot_of_dimVec {N : (rigidRep k ι).subreps} (h : DoubledRep.dimVec N = (0, 0)) :
    N = ⊥ := by
  simp only [DoubledRep.dimVec, Prod.mk.injEq, Submodule.finrank_eq_zero] at h
  exact Subtype.ext (Prod.ext h.1 h.2)

/-! ### The two boundaries of the polygon

Plot a subrepresentation of dimension vector `(i, j)` at `(i + j, j)`. With `g = |ι|`, the upper
boundary of the convex hull is `(0, 0) → (g² + g - 1, g) → (g² + g, g)` through `(H', W)`, and
the lower boundary is `(0, 0) → (g² - 1, 0) → (g² + g, g)` through `(H', 0)`. -/

omit [DecidableEq ι] in
private lemma one_le_card_sq : 1 ≤ Fintype.card ι ^ 2 := Nat.one_le_pow _ _ Fintype.card_pos

/-- Every point lies on or below the upper path: below the edge from `0` to `(g² + g - 1, g)`,
which is `(g² + g - 1) j ≤ g (i + j)`, and below the edge `j = g`. -/
theorem dimVec_upper (N : (rigidRep k ι).subreps) :
    (Fintype.card ι ^ 2 - 1 + Fintype.card ι) * (DoubledRep.dimVec N).2 ≤
        Fintype.card ι * ((DoubledRep.dimVec N).1 + (DoubledRep.dimVec N).2) ∧
      (DoubledRep.dimVec N).2 ≤ Fintype.card ι := by
  have h1 := one_le_card_sq (ι := ι)
  rcases dimVec_mem N with h | h | ⟨hj, hi, hi'⟩ <;>
    [rw [h]; rw [h]; skip] <;> refine ⟨?_, by omega⟩ <;> zify [h1] at * <;> nlinarith

/-- The only points on the slanted upper edge are `0` and the corner `(H', W)`. -/
theorem dimVec_upper_eq {N : (rigidRep k ι).subreps}
    (h : (Fintype.card ι ^ 2 - 1 + Fintype.card ι) * (DoubledRep.dimVec N).2 =
      Fintype.card ι * ((DoubledRep.dimVec N).1 + (DoubledRep.dimVec N).2)) :
    N = ⊥ ∨ N = upperCorner := by
  have h1 := one_le_card_sq (ι := ι)
  have hn := Fintype.card_pos (α := ι)
  rcases eq_top_or N with rfl | ⟨hle, htop, hne⟩
  · rw [dimVec_top] at h
    zify [h1] at h
    nlinarith
  · by_cases hU : (N : Submodule k (H k ι × k) × Submodule k (ι → k)).2 = ⊤
    · exact Or.inr (htop hU)
    · left
      have hj := Submodule.finrank_lt hU
      have hi := hne hU
      have hi' := Submodule.finrank_mono hle
      rw [Module.finrank_pi] at hj
      rw [finrank_range_inl] at hi'
      simp only [DoubledRep.dimVec] at h ⊢
      zify [h1] at h hi hi'
      have hj0 : finrank k (N : Submodule k (H k ι × k) × Submodule k (ι → k)).2 = 0 := by
        zify; nlinarith
      have hn' : (0 : ℤ) < Fintype.card ι := by exact_mod_cast hn
      have hi0 : finrank k (N : Submodule k (H k ι × k) × Submodule k (ι → k)).1 = 0 := by
        rw [hj0] at h; push_cast at h; zify; nlinarith
      exact eq_bot_of_dimVec (by simp [DoubledRep.dimVec, hj0, hi0])

/-- Every point lies on or above the lower path: above the edge `j = 0`, and above the edge from
`(g² - 1, 0)` to `(g² + g, g)`, which is `g i ≤ g (g² - 1) + j`. -/
theorem dimVec_lower (N : (rigidRep k ι).subreps) :
    Fintype.card ι * (DoubledRep.dimVec N).1 ≤
      Fintype.card ι * (Fintype.card ι ^ 2 - 1) + (DoubledRep.dimVec N).2 := by
  have h1 := one_le_card_sq (ι := ι)
  rcases dimVec_mem N with h | h | ⟨hj, hi, hi'⟩ <;> [rw [h]; rw [h]; skip] <;>
    zify [h1] at * <;> nlinarith

/-- The only points on the slanted lower edge are the corner `(H', 0)` and the whole
representation. -/
theorem dimVec_lower_eq {N : (rigidRep k ι).subreps}
    (h : Fintype.card ι * (DoubledRep.dimVec N).1 =
      Fintype.card ι * (Fintype.card ι ^ 2 - 1) + (DoubledRep.dimVec N).2) :
    N = lowerCorner ∨ N = ⊤ := by
  have h1 := one_le_card_sq (ι := ι)
  have hn := Fintype.card_pos (α := ι)
  rcases eq_top_or N with rfl | ⟨hle, htop, -⟩
  · exact Or.inr rfl
  · by_cases hU : (N : Submodule k (H k ι × k) × Submodule k (ι → k)).2 = ⊤
    · rw [htop hU, dimVec_upperCorner] at h
      simp only at h
      zify [h1] at h
      nlinarith
    · left
      have hi' := Submodule.finrank_mono hle
      rw [finrank_range_inl] at hi'
      simp only [DoubledRep.dimVec] at h
      zify [h1] at h hi'
      have hj0 : finrank k (N : Submodule k (H k ι × k) × Submodule k (ι → k)).2 = 0 := by
        zify; nlinarith
      have hi0 : finrank k (N : Submodule k (H k ι × k) × Submodule k (ι → k)).1 =
          finrank k (LinearMap.range (LinearMap.inl k (H k ι) k)) := by
        rw [finrank_range_inl, hj0] at *; zify [h1]; nlinarith
      exact Subtype.ext (Prod.ext (Submodule.eq_of_le_of_finrank_eq hle hi0)
        (Submodule.finrank_eq_zero.mp hj0))

/-- The points on the horizontal lower edge `j = 0` are the subrepresentations of `(H', 0)`. -/
theorem le_lowerCorner_of_dimVec_snd {N : (rigidRep k ι).subreps}
    (h : (DoubledRep.dimVec N).2 = 0) : N ≤ lowerCorner := by
  rcases eq_top_or N with rfl | ⟨hle, -, -⟩
  · rw [dimVec_top] at h
    exact absurd h Fintype.card_ne_zero
  · exact Prod.mk_le_mk.mpr ⟨hle, (Submodule.finrank_eq_zero.mp h).le⟩

end RigidRep

end Quiver.Kronecker
