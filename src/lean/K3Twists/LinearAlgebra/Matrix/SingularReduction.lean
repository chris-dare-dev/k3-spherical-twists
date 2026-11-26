/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Reducing singular letter matrices to invertible ones

Let matrices `A_a` over a normed field be assigned to the letters `a` of an alphabet, and let the
letters map to a group `G` by `g`, with an involution `a ↦ a'` of the alphabet such that
`g(a') = g(a)⁻¹`. Suppose a function `λ` on `G` gives the spectral radius of every product:
`ρ(A_{a₁} ⋯ A_{a_j}) = λ(g(a₁) ⋯ g(a_j))` for every word, including all spellings of one element
of `G`. Then there are invertible matrices `C_a` with the same property (`singular_reduction`).

The proof: among the words `e` representing the identity of `G` choose one with `rank A_e`
minimal, and let `U = im A_e`. For a letter `a` the word `e a e a' e` represents the identity, so
`rank (A_e A_a A_e) ≥ rank A_e`: `A_e A_a` maps `U` onto `U`, and its restriction `C_a` is
invertible. A word `a₁ ⋯ a_j` and the word `e a₁ e a₂ ⋯ e a_j` represent the same element of
`G`; the product of the second has image in `U` and restricts there to `C_{a₁} ⋯ C_{a_j}`, and an
endomorphism with image in `U` has the nonzero eigenvalues of its restriction to `U`
(`Module.End.spectralRadius_restrict`). The empty word needs `ρ(1) = λ(1)`; no hypothesis
`λ(1) ≠ 0` is used, since `λ(1) = ρ(1)` is one of the assumed equalities.

## Main results

* `Module.End.mem_spectrum_restrict_iff`, `Module.End.spectralRadius_restrict`: an endomorphism of
  a finite-dimensional space with range in `U` and its restriction to `U` have the same nonzero
  eigenvalues and the same spectral radius.
* `Matrix.exists_mem_spectrum_norm_eq`: a positive spectral radius of a matrix is the modulus of
  an eigenvalue.
* `Matrix.singular_reduction`: invertible letter matrices with the same spectral radii.
-/

open Module

open scoped ENNReal NNReal

variable {𝕜 : Type*} [NormedField 𝕜]

/-- Spectral radii are invariant under algebra isomorphisms. -/
lemma spectralRadius_algEquiv {A B : Type*} [Ring A] [Ring B] [Algebra 𝕜 A] [Algebra 𝕜 B]
    (f : A ≃ₐ[𝕜] B) (a : A) : spectralRadius 𝕜 (f a) = spectralRadius 𝕜 a := by
  rw [spectralRadius_eq_of_unital, spectralRadius_eq_of_unital, AlgEquiv.spectrum_eq]

section Restrict

variable {V : Type*} [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]

/-- If `X` has range in `U`, a nonzero `μ` is an eigenvalue of the restriction of `X` to `U` if
and only if it is an eigenvalue of `X`: an eigenvector `v = μ⁻¹ X v` lies in `U`. -/
theorem Module.End.mem_spectrum_restrict_iff {X : End 𝕜 V} {U : Submodule 𝕜 V}
    (hX : ∀ x, X x ∈ U) {μ : 𝕜} (hμ : μ ≠ 0) :
    μ ∈ spectrum 𝕜 (X.restrict (fun x (_ : x ∈ U) => hX x)) ↔ μ ∈ spectrum 𝕜 X := by
  rw [← Module.End.hasEigenvalue_iff_mem_spectrum, ← Module.End.hasEigenvalue_iff_mem_spectrum]
  constructor
  · intro h
    obtain ⟨u, hu⟩ := h.exists_hasEigenvector
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hu
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := (u : V)) ?_
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
    refine ⟨?_, fun h0 => hu.2 (Subtype.ext h0)⟩
    have := congrArg Subtype.val hu.1
    simpa using this
  · intro h
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hv
    have hvU : v ∈ U := by
      have : v = μ⁻¹ • X v := by rw [hv.1, smul_smul, inv_mul_cancel₀ hμ, one_smul]
      rw [this]
      exact U.smul_mem _ (hX v)
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := (⟨v, hvU⟩ : U)) ?_
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
    exact ⟨Subtype.ext (by simpa using hv.1),
      fun h0 => hv.2 (by simpa using congrArg Subtype.val h0)⟩

/-- **An endomorphism with range in `U` has the spectral radius of its restriction to `U`.** -/
theorem Module.End.spectralRadius_restrict {X : End 𝕜 V} {U : Submodule 𝕜 V}
    (hX : ∀ x, X x ∈ U) :
    spectralRadius 𝕜 (X.restrict (fun x (_ : x ∈ U) => hX x)) = spectralRadius 𝕜 X := by
  rw [spectralRadius_eq_of_unital, spectralRadius_eq_of_unital]
  apply le_antisymm
  · refine iSup₂_le fun k hk => ?_
    rcases eq_or_ne k 0 with rfl | hk0
    · simp
    · exact le_iSup₂ (f := fun k (_ : k ∈ spectrum 𝕜 X) => (‖k‖₊ : ℝ≥0∞)) k
        ((Module.End.mem_spectrum_restrict_iff hX hk0).1 hk)
  · refine iSup₂_le fun k hk => ?_
    rcases eq_or_ne k 0 with rfl | hk0
    · simp
    · exact le_iSup₂ (f := fun k (_ : k ∈ spectrum 𝕜 (X.restrict (fun x (_ : x ∈ U) => hX x))) =>
        (‖k‖₊ : ℝ≥0∞)) k ((Module.End.mem_spectrum_restrict_iff hX hk0).2 hk)

end Restrict

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A matrix and its linear map have the same spectral radius. -/
lemma spectralRadius_mulVecLin (M : Matrix n n 𝕜) :
    spectralRadius 𝕜 M.mulVecLin = spectralRadius 𝕜 M := by
  rw [← Matrix.toLin'_apply']
  exact spectralRadius_algEquiv (Matrix.toLinAlgEquiv' (R := 𝕜) (n := n)) M

/-- **A positive spectral radius is attained.** If `ρ(M) = x > 0`, some eigenvalue of `M` has
modulus `x`; the spectrum of a matrix is finite. -/
theorem exists_mem_spectrum_norm_eq (M : Matrix n n 𝕜) {x : ℝ} (hx : 0 < x)
    (h : spectralRadius 𝕜 M = ENNReal.ofReal x) : ∃ z ∈ spectrum 𝕜 M, ‖z‖ = x := by
  have hfin : (spectrum 𝕜 M).Finite := Matrix.finite_spectrum M
  rcases (spectrum 𝕜 M).eq_empty_or_nonempty with he | hne
  · exfalso
    rw [spectralRadius_eq_of_unital, he] at h
    simp only [Set.mem_empty_iff_false, iSup_false, iSup_bot] at h
    exact (ENNReal.ofReal_pos.2 hx).ne' h.symm
  obtain ⟨z, hz, hmax⟩ := Set.exists_max_image _ (fun k : 𝕜 => ‖k‖) hfin hne
  refine ⟨z, hz, ?_⟩
  have hsr : spectralRadius 𝕜 M = (‖z‖₊ : ℝ≥0∞) := by
    rw [spectralRadius_eq_of_unital]
    apply le_antisymm
    · refine iSup₂_le fun k hk => ?_
      exact ENNReal.coe_le_coe.2 (hmax k hk)
    · exact le_iSup₂ (f := fun k (_ : k ∈ spectrum 𝕜 M) => (‖k‖₊ : ℝ≥0∞)) z hz
  have e : (‖z‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖z‖ := by rw [ofReal_norm, eNorm_eq_nnNorm]
  rw [hsr, e] at h
  exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg z) hx.le).1 h

/-- **The singular reduction.** Let `g : ι → G` map the letters to a group, with an involution
`a ↦ a'` of the letters such that `g(a') = g(a)⁻¹`, and let `λ : G → ℝ` give the spectral radius of
every product of the letter matrices `A_a`: `ρ(A_{a₁} ⋯ A_{a_j}) = λ(g(a₁) ⋯ g(a_j))` for every
word. Then there are invertible letter matrices `C_a`, of size the least rank of a product
representing the identity, with the same spectral radii on every word. -/
theorem singular_reduction {ι G : Type*} [Group G] (g : ι → G) (inv : ι → ι)
    (hinv : ∀ a, g (inv a) = (g a)⁻¹) (A : ι → Matrix n n 𝕜) (lam : G → ℝ)
    (h6 : ∀ w : List ι, spectralRadius 𝕜 (w.map A).prod = ENNReal.ofReal (lam (w.map g).prod)) :
    ∃ (m : ℕ) (C : ι → Matrix (Fin m) (Fin m) 𝕜), (∀ a, IsUnit (C a)) ∧
      ∀ w : List ι, spectralRadius 𝕜 (w.map C).prod = ENNReal.ofReal (lam (w.map g).prod) := by
  classical
  -- a word `e` representing the identity, of least rank
  have hP : ∃ r, ∃ e : List ι, (e.map g).prod = 1 ∧ ((e.map A).prod).rank = r :=
    ⟨_, [], by simp, rfl⟩
  obtain ⟨e, he1, her⟩ := Nat.find_spec hP
  have hmin : ∀ e' : List ι, (e'.map g).prod = 1 → Nat.find hP ≤ ((e'.map A).prod).rank :=
    fun e' he' => Nat.find_min' hP ⟨e', he', rfl⟩
  set E := (e.map A).prod with hE
  set U : Submodule 𝕜 (n → 𝕜) := LinearMap.range E.mulVecLin with hU
  have hrank : Module.finrank 𝕜 U = Nat.find hP := her
  -- the letters `A_e A_a` map `U` into itself
  have hfU : ∀ a x, (E * A a).mulVecLin x ∈ U := fun a x => by
    rw [Matrix.mulVecLin_mul, LinearMap.comp_apply]
    exact LinearMap.mem_range_self _ _
  let C' : ι → Module.End 𝕜 U := fun a =>
    (E * A a).mulVecLin.restrict (fun x (_ : x ∈ U) => hfU a x)
  -- and restrict to invertible maps of `U`
  have hbij : ∀ a, Function.Bijective (C' a) := by
    intro a
    have hword : ((e ++ [a] ++ e ++ [inv a] ++ e).map g).prod = 1 := by
      simp [List.map_append, List.prod_append, he1, hinv]
    have hprod :
        ((e ++ [a] ++ e ++ [inv a] ++ e).map A).prod = (E * A a * E) * (A (inv a) * E) := by
      simp [List.map_append, List.prod_append, hE, mul_assoc]
    have hr : Nat.find hP ≤ (E * A a * E).rank := by
      have := hmin _ hword
      rw [hprod] at this
      exact this.trans (Matrix.rank_mul_le_left _ _)
    have hmap : U.map (E * A a).mulVecLin = U := by
      apply Submodule.eq_of_le_of_finrank_le
      · rintro _ ⟨x, -, rfl⟩
        exact hfU a x
      · rw [hrank]
        have : LinearMap.range (E * A a * E).mulVecLin = U.map (E * A a).mulVecLin := by
          rw [Matrix.mulVecLin_mul (E * A a) E, LinearMap.range_comp]
        calc Nat.find hP ≤ (E * A a * E).rank := hr
          _ = Module.finrank 𝕜 (U.map (E * A a).mulVecLin) := by rw [Matrix.rank, this]
    have hsurj : Function.Surjective (C' a) := by
      intro y
      have : (y : n → 𝕜) ∈ U.map (E * A a).mulVecLin := by rw [hmap]; exact y.2
      obtain ⟨x, hx, hxy⟩ := this
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
    exact ⟨LinearMap.injective_iff_surjective.2 hsurj, hsurj⟩
  -- products of the restricted letters
  have hcoe : ∀ (w : List ι) (u : U),
      (((w.map C').prod u : U) : n → 𝕜) = ((w.map fun a => E * A a).prod).mulVecLin u := by
    intro w
    induction w with
    | nil => intro u; simp
    | cons a w ih =>
      intro u
      rw [List.map_cons, List.prod_cons, mul_apply_eq_comp, List.map_cons, List.prod_cons]
      change (E * A a).mulVecLin (((w.map C').prod u : U) : n → 𝕜) = _
      rw [ih u]
      simp only [Matrix.mulVecLin_mul, LinearMap.comp_apply]
  have hF : ∀ w : List ι,
      (w.map fun a => E * A a).prod = ((w.flatMap fun a => e ++ [a]).map A).prod := by
    intro w
    induction w with
    | nil => simp
    | cons a w ih =>
      simp only [List.map_cons, List.prod_cons, List.flatMap_cons, List.map_append,
        List.prod_append, List.map_nil, List.prod_nil, one_mul, ih, mul_assoc]
      rfl
  have hG : ∀ w : List ι, ((w.flatMap fun a => e ++ [a]).map g).prod = (w.map g).prod := by
    intro w
    induction w with
    | nil => simp
    | cons a w ih => simp [List.flatMap_cons, List.map_append, List.prod_append, ih, he1]
  have hrange : ∀ (a : ι) (w : List ι) x,
      (((a :: w).map fun a => E * A a).prod).mulVecLin x ∈ U := by
    intro a w x
    rw [List.map_cons, List.prod_cons, mul_assoc, Matrix.mulVecLin_mul, LinearMap.comp_apply]
    exact LinearMap.mem_range_self _ _
  -- spectral radii of the restricted products
  have hρ : ∀ w : List ι,
      spectralRadius 𝕜 (w.map C').prod = ENNReal.ofReal (lam (w.map g).prod) := by
    intro w
    cases w with
    | nil =>
      have h0 := h6 []
      simp only [List.map_nil, List.prod_nil] at h0 ⊢
      rcases isEmpty_or_nonempty n with hn | hn
      · have : Subsingleton U := by
          constructor
          intro x y
          exact Subtype.ext (Subsingleton.elim _ _)
        rw [spectrum.SpectralRadius.of_subsingleton, ← h0, spectrum.SpectralRadius.of_subsingleton]
      · rw [spectrum.spectralRadius_one] at h0
        have hpos : 0 < Nat.find hP := by
          rcases Nat.eq_zero_or_pos (Nat.find hP) with h | h
          · exfalso
            have hUbot : U = ⊥ := Submodule.finrank_eq_zero.1 (hrank.trans h)
            have hE0 : E = 0 := by
              have : E.mulVecLin = 0 := LinearMap.range_eq_bot.1 hUbot
              rw [← Matrix.toLin'_apply'] at this
              exact Matrix.toLin'.injective (this.trans (map_zero _).symm)
            have := h6 e
            rw [← hE, hE0, spectrum.spectralRadius_zero, he1, ← h0] at this
            exact zero_ne_one this
          · exact h
        have : Nontrivial U := Module.nontrivial_of_finrank_pos (hrank ▸ hpos)
        rw [← h0, spectralRadius_eq_of_unital, spectrum.one_eq]
        simp
    | cons a w =>
      have heq : ((a :: w).map C').prod =
          (((a :: w).map fun a => E * A a).prod).mulVecLin.restrict
            (fun x (_ : x ∈ U) => hrange a w x) := by
        apply LinearMap.ext
        intro u
        apply Subtype.ext
        rw [hcoe, LinearMap.restrict_apply]
      rw [heq, Module.End.spectralRadius_restrict, spectralRadius_mulVecLin, hF, h6, hG]
  -- back to matrices through a basis of `U`
  let b := Module.finBasis 𝕜 U
  let φ := LinearMap.toMatrixAlgEquiv b
  refine ⟨Module.finrank 𝕜 U, fun a => φ (C' a),
    fun a => ((Module.End.isUnit_iff _).2 (hbij a)).map φ, fun w => ?_⟩
  have hprod : (w.map fun a => φ (C' a)).prod = φ (w.map C').prod := by
    rw [map_list_prod, List.map_map]
    rfl
  rw [hprod, spectralRadius_eq_of_unital, AlgEquiv.spectrum_eq, ← spectralRadius_eq_of_unital,
    hρ]

end Matrix
