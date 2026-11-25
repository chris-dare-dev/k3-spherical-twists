/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.RepresentationTheory.Quiver.Kronecker.Ext
import K3Twists.RepresentationTheory.Quiver.Kronecker.HarderNarasimhan
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# A rigid wall object is determined by its incoming flag

The proposition on rigid wall groups of the research draft *Harder–Narasimhan towers of spherical
twist words on a Picard-rank-one K3 surface* says that a rigid wall object is determined up to
isomorphism by its ordered list of isotypic HN quotients on the incoming side. The draft's proof:
the HN prefixes of a rigid object are rigid, by Mukai's inequality; a prefix `A` has no maps to the
next quotient `B`, since the incoming phases of `A` are higher; for an extension `ξ` with rigid
middle term `N`, `v ↦ i v p` injects `Ext¹(B, A)/(End(A) ξ + ξ End(B))` into `Ext¹(N, N) = 0`, so
the orbit of `ξ` under `Aut(A) × Aut(B)` has full tangent space; in characteristic zero a
full-dimensional orbit is open in the irreducible space `Ext¹(B, A)`, so two extensions with rigid
middle terms have the same orbit; induction on the flag finishes the proof.

In the quiver model every step but the open-orbit one is proved from Mathlib: the injection and
Mukai's inequality in `Ext.lean`, and here that an HN prefix has no maps to the next factor, that
the prefixes are rigid, and the induction. The open-orbit step needs algebraic groups acting on
varieties, which Mathlib cannot use yet; it is the hypothesis `OpenOrbitHypotheses`, and no other
input is used.

## Main definitions

* `OpenOrbitHypotheses k ι`: over an algebraically closed field of characteristic zero, two classes
  of `Ext¹(B, A)` whose `Aut(A) × Aut(B)`-orbits have full tangent space lie in one orbit.

## Main results

* `Hom_restrict_subquotient_eq_bot`: a prefix `M_j` of an HN filtration has no maps to the next
  factor `M_{j+1}/M_j` (from `exists_subreps_of_mem_Hom`: a nonzero map would give subobjects
  `K < M_j ≤ I` with `w(K) + w(I) = 2 w(M_j)`, while `M_j` is the only maximizer of a weight `w`);
* `subsingleton_Ext1_restrict_of_chain`: the prefixes of such a flag of a rigid representation are
  rigid, by Mukai's inequality;
* `nonempty_iso_extension`: two extensions `0 → A → N → B → 0` and `0 → A' → N' → B' → 0` with
  `A ≅ A'`, `B ≅ B'`, `Hom(A, B) = 0` and `N`, `N'` rigid are isomorphic;
* `nonempty_iso_of_chain`, `nonempty_iso_of_hnFiltration`: **a rigid wall object is determined by
  its incoming flag**: two rigid representations with the relations whose HN filtrations for one
  charge have isomorphic factors, in order, are isomorphic.

## Compared with the draft

* The factors need not be isotypic, nor their constituents stable or marked: the induction only
  uses that consecutive factors match up to isomorphism and that each prefix has no maps to the
  next factor, which every HN filtration gives.
* The draft assumes characteristic zero for the open-orbit step. That step only needs that a class
  `ξ` with `End(A) ξ + ξ End(B) = Ext¹(B, A)` has an open orbit; since the orbit map factors
  through the orbit, a smooth variety, its differential lands in the tangent space of the orbit,
  and the orbit has full dimension in every characteristic. The hypothesis keeps the draft's
  assumption.
-/

universe u

namespace Quiver.Kronecker

open Module Order

/-! ### The open-orbit input -/

/-- **The open-orbit input of the proposition on rigid wall groups.** For finite-dimensional
representations `A`, `B` with the preprojective relations over an algebraically closed field of
characteristic zero, the group `Aut(A) × Aut(B)` acts on `Ext¹(B, A)` by `(α, β) ξ = α ξ β⁻¹`, and
the tangent space at `ξ` to the orbit is `End(A) ξ + ξ End(B)` (`DoubledRep.orbitTangent`, lifted
to cocycles). The field says that two classes with full tangent space lie in one orbit.

The vertex spaces range over one universe `u`; the uniqueness theorems use the field in the
universe of the given wall object. Mathlib cannot prove the field yet: it needs algebraic groups
acting on varieties, with dimensions and tangent spaces of orbits. -/
structure OpenOrbitHypotheses (k : Type*) [Field k] [IsAlgClosed k] [CharZero k] (ι : Type*)
    [Fintype ι] : Prop where
  /-- Two classes `ξ, ξ'` of `Ext¹(B, A)` with `End(A) ξ + ξ End(B) = Ext¹(B, A)` lie in one
  orbit of `Aut(A) × Aut(B)`: there are automorphisms `α`, `β` with `α ξ - ξ' β` a coboundary.
  Source: the orbits of an algebraic group acting on a variety are smooth and open in their
  closures (Borel, *Linear Algebraic Groups*, 2nd ed., Proposition I.1.8; Humphreys, *Linear
  Algebraic Groups*, §8.3). `Aut(A) × Aut(B)`, the units of `End(A) × End(B)`, is a connected
  algebraic group; its orbit map at `ξ` has differential `(a, b) ↦ a ξ - ξ b`, whose image
  `End(A) ξ + ξ End(B)` lies in the tangent space of the orbit. A full tangent space makes the
  orbit full-dimensional, hence open and dense in the irreducible affine space `Ext¹(B, A)`, and two
  such orbits meet. This is the step "in characteristic zero a full-dimensional orbit is open in
  this irreducible extension space" of the draft's proposition on rigid wall groups. -/
  exists_aut_of_le_orbitTangent :
    ∀ {V₀ V₁ W₀ W₁ : Type u} [AddCommGroup V₀] [Module k V₀] [FiniteDimensional k V₀]
      [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁]
      [AddCommGroup W₀] [Module k W₀] [FiniteDimensional k W₀]
      [AddCommGroup W₁] [Module k W₁] [FiniteDimensional k W₁]
      (A : DoubledRep k ι V₀ V₁) (B : DoubledRep k ι W₀ W₁)
      (ξ ξ' : (ι → W₀ →ₗ[k] V₁) × (ι → W₁ →ₗ[k] V₀)),
      A.IsPreprojective → B.IsPreprojective →
      ξ ∈ DoubledRep.cocycles₁ B A → ξ' ∈ DoubledRep.cocycles₁ B A →
      DoubledRep.cocycles₁ B A ≤ DoubledRep.orbitTangent A B ξ →
      DoubledRep.cocycles₁ B A ≤ DoubledRep.orbitTangent A B ξ' →
      ∃ (α : DoubledRep.Iso A A) (β : DoubledRep.Iso B B),
        DoubledRep.postcomp ξ ((α.e₀ : V₀ →ₗ[k] V₀), (α.e₁ : V₁ →ₗ[k] V₁)) -
          DoubledRep.precomp ξ' ((β.e₀ : W₀ →ₗ[k] W₀), (β.e₁ : W₁ →ₗ[k] W₁)) ∈
            DoubledRep.coboundaries₁ B A

namespace DoubledRep

/-! ### Restrictions and subquotients -/

section Subquotient

variable {k ι : Type*} [Field k] {V₀ V₁ : Type*} [AddCommGroup V₀] [Module k V₀]
  [AddCommGroup V₁] [Module k V₁] {M : DoubledRep k ι V₀ V₁}

/-- An isomorphism of a restriction to `⊤` with the representation. -/
def restrictTopIso {P : M.subreps} (hP : P = ⊤) : Iso (M.restrict P) M where
  e₀ := LinearEquiv.ofTop _ (by rw [hP]; rfl)
  e₁ := LinearEquiv.ofTop _ (by rw [hP]; rfl)
  comm_A _ _ := rfl
  comm_B _ _ := rfl

/-- Two restrictions to zero subrepresentations are isomorphic. -/
def restrictBotIso {V₀' V₁' : Type*} [AddCommGroup V₀'] [Module k V₀'] [AddCommGroup V₁']
    [Module k V₁'] {M' : DoubledRep k ι V₀' V₁'} {P : M.subreps} {P' : M'.subreps} (hP : P = ⊥)
    (hP' : P' = ⊥) : Iso (M.restrict P) (M'.restrict P') :=
  have : Subsingleton (P : Submodule k V₀ × Submodule k V₁).1 := by
    subst hP
    exact inferInstanceAs (Subsingleton (⊥ : Submodule k V₀))
  have : Subsingleton (P : Submodule k V₀ × Submodule k V₁).2 := by
    subst hP
    exact inferInstanceAs (Subsingleton (⊥ : Submodule k V₁))
  have : Subsingleton (P' : Submodule k V₀' × Submodule k V₁').1 := by
    subst hP'
    exact inferInstanceAs (Subsingleton (⊥ : Submodule k V₀'))
  have : Subsingleton (P' : Submodule k V₀' × Submodule k V₁').2 := by
    subst hP'
    exact inferInstanceAs (Subsingleton (⊥ : Submodule k V₁'))
  { e₀ := LinearEquiv.ofSubsingleton _ _
    e₁ := LinearEquiv.ofSubsingleton _ _
    comm_A _ _ := Subsingleton.elim _ _
    comm_B _ _ := Subsingleton.elim _ _ }

end Subquotient

/-! ### A prefix has no maps to the next HN factor -/

section HomVanishing

variable {k ι : Type*} [Field k] {V₀ V₁ : Type*} [AddCommGroup V₀] [Module k V₀]
  [AddCommGroup V₁] [Module k V₁] {M : DoubledRep k ι V₀ V₁}

variable [FiniteDimensional k V₀] [FiniteDimensional k V₁]

/-- **The kernel and the image of a map from a prefix to the next subquotient.** For `P ≤ Q` and
a morphism `f : M|P → Q/P`, the kernel of `f` and the preimage in `M` of its image are
subrepresentations `K ≤ P ≤ I` with `dim K + dim I = 2 dim P` at each vertex, and `K = P` only for
`f = 0`. -/
theorem exists_subreps_of_mem_Hom {P Q : M.subreps} (h : P ≤ Q)
    {f : ((P : Submodule k V₀ × Submodule k V₁).1 →ₗ[k]
        (Q : Submodule k V₀ × Submodule k V₁).1 ⧸ (M.subrepOf P Q).1.1) ×
      ((P : Submodule k V₀ × Submodule k V₁).2 →ₗ[k]
        (Q : Submodule k V₀ × Submodule k V₁).2 ⧸ (M.subrepOf P Q).1.2)}
    (hf : f ∈ Hom (M.restrict P) (M.subquotient P Q)) :
    ∃ K I : M.subreps, K ≤ P ∧ P ≤ I ∧ dimVec K + dimVec I = dimVec P + dimVec P ∧
      (K = P → f = 0) := by
  change f ∈ Hom (M.restrict P) ((M.restrict Q).quotient (M.subrepOf P Q)) at hf
  refine ⟨mapRestrict (kerSubrep hf), mapRestrict (comapQuotient (rangeSubrep hf)),
    mapRestrict_le _, ?_, ?_, fun hK ↦ eq_zero_of_kerSubrep_eq_top hf
      (mapRestrict_eq_self_iff.mp hK)⟩
  · exact (mapRestrict_subrepOf h).symm.le.trans (mapRestrict_mono (le_comapQuotient _))
  · have e := dimVec_kerSubrep_add_dimVec_rangeSubrep hf
    have hR : dimVec (M.subrepOf P Q) = dimVec P := by
      rw [← dimVec_mapRestrict, mapRestrict_subrepOf h]
    rw [dimVec_mapRestrict, dimVec_mapRestrict, dimVec_comapQuotient, hR]
    refine Prod.ext ?_ ?_
    · have := congrArg Prod.fst e
      simp only [dimVec, Prod.fst_add] at this ⊢
      omega
    · have := congrArg Prod.snd e
      simp only [dimVec, Prod.snd_add] at this ⊢
      omega

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **A prefix of an HN filtration has no maps to the next factor**: the incoming phases of the
prefix `M_j` are higher than that of `M_{j+1}/M_j`, so `Hom(M_j, M_{j+1}/M_j) = 0`. -/
theorem Hom_restrict_subquotient_eq_bot {r₀ r₁ : K} (h₀ : 0 < r₀) (h₁ : 0 < r₁) (d₀ d₁ : K)
    (F : (M.slopeFunction h₀ h₁ d₀ d₁).HNFiltration) {j : ℕ} (hj : j < F.n) :
    Hom (M.restrict (F.c j)) (M.subquotient (F.c j) (F.c (j + 1))) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  obtain ⟨K', I, -, -, hdim, hKf⟩ := exists_subreps_of_mem_Hom (F.c_mono (Nat.le_succ j)) hf
  refine hKf ?_
  obtain ⟨θ, hθ₁, hθ₂⟩ := F.exists_slope_between ⟨j, Nat.lt_succ_of_lt hj⟩
  have hK := F.weight_le ⟨j, Nat.lt_succ_of_lt hj⟩ (fun i hi ↦ (hθ₁ i hi).le)
    (fun i hi ↦ (hθ₂ i hi).le) K'
  have hI := F.weight_le ⟨j, Nat.lt_succ_of_lt hj⟩ (fun i hi ↦ (hθ₁ i hi).le)
    (fun i hi ↦ (hθ₂ i hi).le) I
  rw [← F.c_of_le hj.le] at hK hI
  refine F.eq_of_weight_eq ⟨j, Nat.lt_succ_of_lt hj⟩ hθ₁ hθ₂ ?_ |>.trans (F.c_of_le hj.le).symm
  rw [← F.c_of_le hj.le]
  have e₀ : ((dimVec K').1 : K) + (dimVec I).1 = (dimVec (F.c j)).1 + (dimVec (F.c j)).1 := by
    exact_mod_cast congrArg Prod.fst hdim
  have e₁ : ((dimVec K').2 : K) + (dimVec I).2 = (dimVec (F.c j)).2 + (dimVec (F.c j)).2 := by
    exact_mod_cast congrArg Prod.snd hdim
  have hsum : (M.slopeFunction h₀ h₁ d₀ d₁).weight θ K' +
      (M.slopeFunction h₀ h₁ d₀ d₁).weight θ I =
        (M.slopeFunction h₀ h₁ d₀ d₁).weight θ (F.c j) +
          (M.slopeFunction h₀ h₁ d₀ d₁).weight θ (F.c j) := by
    simp only [SlopeFunction.weight, slopeFunction_rk, slopeFunction_deg]
    linear_combination (d₀ - θ * r₀) * e₀ + (d₁ - θ * r₁) * e₁
  linarith

end HomVanishing

/-! ### Rigid prefixes -/

section RigidPrefixes

variable {k ι : Type*} [Field k] [Fintype ι] {V₀ V₁ : Type*} [AddCommGroup V₀] [Module k V₀]
  [FiniteDimensional k V₀] [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁]
  {M : DoubledRep k ι V₀ V₁}

/-- The prefixes of a flag of a rigid representation are rigid, when each prefix has no maps to
the next subquotient (Mukai's inequality, `rigid_of_rigid_extension`). -/
theorem subsingleton_Ext1_restrict_of_chain (hM : M.IsPreprojective)
    (hrig : Subsingleton (Ext1 M M)) {n : ℕ} {c : ℕ → M.subreps} (hc : Monotone c) (hcn : c n = ⊤)
    (hHom : ∀ j < n, Hom (M.restrict (c j)) (M.subquotient (c j) (c (j + 1))) = ⊥) :
    ∀ j ≤ n, Subsingleton (Ext1 (M.restrict (c j)) (M.restrict (c j))) := by
  have key : ∀ m ≤ n, Subsingleton (Ext1 (M.restrict (c (n - m))) (M.restrict (c (n - m)))) := by
    intro m
    induction m with
    | zero =>
      intro _
      exact (restrictTopIso (by rw [Nat.sub_zero, hcn])).symm.subsingleton_Ext1 hrig
    | succ m ih =>
      intro hm
      have hsucc : n - (m + 1) + 1 = n - m := by omega
      obtain ⟨ξ, hξ, ⟨u⟩⟩ := exists_iso_extension_of_le hM (hc (Nat.le_succ (n - (m + 1))))
      have hN := ih (by omega)
      rw [← hsucc] at hN
      exact (rigid_of_rigid_extension (hM.restrict _) ((hM.restrict _).quotient _) hξ
        (hHom _ (by omega)) (u.subsingleton_Ext1 hN)).1
  intro j hj
  have := key (n - j) (Nat.sub_le n j)
  rwa [Nat.sub_sub_self hj] at this

end RigidPrefixes

/-! ### Uniqueness -/

section Uniqueness

variable {k ι : Type*} [Field k] [IsAlgClosed k] [CharZero k] [Fintype ι]

/-- **Two extensions with rigid middle terms are isomorphic.** Let `0 → A → N → B → 0` and
`0 → A' → N' → B' → 0` be extensions of representations with the relations, with `A ≅ A'`,
`B ≅ B'`, `Hom(A, B) = 0` and `N`, `N'` rigid. Then `N ≅ N'`. Transported to `(B, A)`, both classes
have full tangent space `End(A) ξ + ξ End(B) = Ext¹(B, A)` (`cocycles₁_le_orbitTangent`, from the
injection), so by the open-orbit input they lie in one orbit of `Aut(A) × Aut(B)`, and
`[[α, h], [0, β]]` is an isomorphism (`extensionIso`). -/
theorem nonempty_iso_extension {V₀ V₁ W₀ W₁ : Type u} [AddCommGroup V₀] [Module k V₀]
    [FiniteDimensional k V₀] [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁]
    [AddCommGroup W₀] [Module k W₀] [FiniteDimensional k W₀] [AddCommGroup W₁] [Module k W₁]
    [FiniteDimensional k W₁] {V₀' V₁' W₀' W₁' : Type*} [AddCommGroup V₀'] [Module k V₀']
    [AddCommGroup V₁'] [Module k V₁'] [AddCommGroup W₀'] [Module k W₀'] [AddCommGroup W₁']
    [Module k W₁'] (hyp : OpenOrbitHypotheses.{u} k ι) {A : DoubledRep k ι V₀ V₁}
    {B : DoubledRep k ι W₀ W₁} {A' : DoubledRep k ι V₀' V₁'} {B' : DoubledRep k ι W₀' W₁'}
    (hA : A.IsPreprojective) (hB : B.IsPreprojective) (hAB : Hom A B = ⊥)
    {ξ : (ι → W₀ →ₗ[k] V₁) × (ι → W₁ →ₗ[k] V₀)}
    {ξ' : (ι → W₀' →ₗ[k] V₁') × (ι → W₁' →ₗ[k] V₀')} (hξ : ξ ∈ cocycles₁ B A)
    (hξ' : ξ' ∈ cocycles₁ B' A') (α : Iso A A') (β : Iso B B')
    (hN : Subsingleton (Ext1 (extension A B ξ) (extension A B ξ)))
    (hN' : Subsingleton (Ext1 (extension A' B' ξ') (extension A' B' ξ'))) :
    Nonempty (Iso (extension A B ξ) (extension A' B' ξ')) := by
  let u := isoTransportClass (ξ := ξ') α.symm β.symm
  obtain ⟨a, b, h, hh⟩ := hyp.exists_aut_of_le_orbitTangent A B ξ _ hA hB hξ
    (transportClass_mem_cocycles₁ α.symm β.symm hξ') (cocycles₁_le_orbitTangent hAB hN)
    (cocycles₁_le_orbitTangent hAB (u.subsingleton_Ext1 hN'))
  exact ⟨(extensionIso a b h hh.symm).trans u.symm⟩

variable {V₀ V₁ : Type u} [AddCommGroup V₀] [Module k V₀] [FiniteDimensional k V₀]
  [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁] {V₀' V₁' : Type*} [AddCommGroup V₀']
  [Module k V₀'] [FiniteDimensional k V₀'] [AddCommGroup V₁'] [Module k V₁']
  [FiniteDimensional k V₁'] {M : DoubledRep k ι V₀ V₁} {M' : DoubledRep k ι V₀' V₁'}

/-- **Uniqueness along a flag.** Let `M`, `M'` be rigid representations with the relations and
`0 = M₀ ≤ ⋯ ≤ M_n = M`, `0 = M'₀ ≤ ⋯ ≤ M'_n = M'` flags whose subquotients `M_{j+1}/M_j` and
`M'_{j+1}/M'_j` are isomorphic and admit no maps from the prefixes `M_j`, `M'_j`. Then `M ≅ M'`:
by induction on `j`, `M_j ≅ M'_j`, from `nonempty_iso_extension` applied to the extensions
`0 → M_j → M_{j+1} → M_{j+1}/M_j → 0`, whose middle terms are rigid by Mukai's inequality. -/
theorem nonempty_iso_of_chain (hyp : OpenOrbitHypotheses.{u} k ι) (hM : M.IsPreprojective)
    (hM' : M'.IsPreprojective) (hrig : Subsingleton (Ext1 M M))
    (hrig' : Subsingleton (Ext1 M' M')) {n : ℕ} {c : ℕ → M.subreps} {c' : ℕ → M'.subreps}
    (hc : Monotone c) (hc' : Monotone c') (hc₀ : c 0 = ⊥) (hc₀' : c' 0 = ⊥) (hcn : c n = ⊤)
    (hcn' : c' n = ⊤)
    (hHom : ∀ j < n, Hom (M.restrict (c j)) (M.subquotient (c j) (c (j + 1))) = ⊥)
    (hHom' : ∀ j < n, Hom (M'.restrict (c' j)) (M'.subquotient (c' j) (c' (j + 1))) = ⊥)
    (hQ : ∀ j < n,
      Nonempty (Iso (M.subquotient (c j) (c (j + 1))) (M'.subquotient (c' j) (c' (j + 1))))) :
    Nonempty (Iso M M') := by
  have hrigc := subsingleton_Ext1_restrict_of_chain hM hrig hc hcn hHom
  have hrigc' := subsingleton_Ext1_restrict_of_chain hM' hrig' hc' hcn' hHom'
  have up : ∀ j ≤ n, Nonempty (Iso (M.restrict (c j)) (M'.restrict (c' j))) := by
    intro j
    induction j with
    | zero => exact fun _ ↦ ⟨restrictBotIso hc₀ hc₀'⟩
    | succ j ih =>
      intro hj
      obtain ⟨α⟩ := ih (by omega)
      obtain ⟨β⟩ := hQ j (by omega)
      obtain ⟨ξ, hξ, ⟨u⟩⟩ := exists_iso_extension_of_le hM (hc (Nat.le_succ j))
      obtain ⟨ξ', hξ', ⟨u'⟩⟩ := exists_iso_extension_of_le hM' (hc' (Nat.le_succ j))
      obtain ⟨w⟩ := nonempty_iso_extension hyp (hM.restrict _) ((hM.restrict _).quotient _)
        (hHom j (by omega)) hξ hξ' α β (u.subsingleton_Ext1 (hrigc (j + 1) hj))
        (u'.subsingleton_Ext1 (hrigc' (j + 1) hj))
      exact ⟨(u.trans w).trans u'.symm⟩
  obtain ⟨w⟩ := up n le_rfl
  exact ⟨((restrictTopIso hcn).symm.trans w).trans (restrictTopIso hcn')⟩

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **A rigid wall object is determined by its incoming flag** (the proposition on rigid wall
groups, in the quiver model). Let `M`, `M'` be rigid representations with the preprojective
relations, and `F`, `F'` their HN filtrations for one charge `slopeFunction r d` (the incoming
side), with the same number of factors and isomorphic factors `F_{j+1}/F_j ≅ F'_{j+1}/F'_j`. Then
`M ≅ M'`, given the open-orbit input. -/
theorem nonempty_iso_of_hnFiltration (hyp : OpenOrbitHypotheses.{u} k ι)
    (hM : M.IsPreprojective) (hM' : M'.IsPreprojective) (hrig : Subsingleton (Ext1 M M))
    (hrig' : Subsingleton (Ext1 M' M')) {r₀ r₁ : K} (h₀ : 0 < r₀) (h₁ : 0 < r₁) (d₀ d₁ : K)
    (F : (M.slopeFunction h₀ h₁ d₀ d₁).HNFiltration)
    (F' : (M'.slopeFunction h₀ h₁ d₀ d₁).HNFiltration) (hn : F.n = F'.n)
    (hQ : ∀ j < F.n, Nonempty (Iso (M.subquotient (F.c j) (F.c (j + 1)))
      (M'.subquotient (F'.c j) (F'.c (j + 1))))) :
    Nonempty (Iso M M') :=
  nonempty_iso_of_chain hyp hM hM' hrig hrig' F.c_mono F'.c_mono F.c_zero F'.c_zero F.c_n
    (by rw [hn]; exact F'.c_n) (fun _ hj ↦ Hom_restrict_subquotient_eq_bot h₀ h₁ d₀ d₁ F hj)
    (fun _ hj ↦ Hom_restrict_subquotient_eq_bot h₀ h₁ d₀ d₁ F' (hn ▸ hj)) hQ

end Uniqueness

end DoubledRep

end Quiver.Kronecker
