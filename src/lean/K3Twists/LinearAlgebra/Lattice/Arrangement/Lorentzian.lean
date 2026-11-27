/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.Lattice.Arrangement

/-!
# Two roots with pairing above two: a Lorentzian complement

Let `V` be a finite-dimensional real space with a symmetric nondegenerate form `B` of signature
`(2, n)` (`sigPos B = 2`), and let `δ₁`, `δ₂` be roots (`B(δᵢ, δᵢ) = -2`) with `|B(δ₁, δ₂)| > 2`.
The stratum trichotomy of `LinearAlgebra/Lattice/Arrangement.lean` says that no positive period
vanishes on both roots. This file proves the sharper form of the indefinite case:

* `Mukai.sigPos_orthogonal_pair_eq_one`: **the orthogonal complement `W^⊥` of
  `W = span(δ₁, δ₂)` has exactly one positive direction**, `sigPos(B|_{W^⊥}) = 1`. The span `W`
  has signature `(1, 1)`: `u = δ₁ + (a/2)δ₂` has `B(u, u) = a²/2 - 2 > 0` and is orthogonal to
  `δ₂`, of square `-2`. A positive plane in `W^⊥` together with `u` would be a positive
  three-space in `V`, and a negative semidefinite `W^⊥` together with `δ₂` would be a negative
  semidefinite subspace of dimension `dim V - 1` (`QuadraticForm.sigPos_add_finrank_le_of_nonpos`).

The span `W` is nondegenerate as soon as `⟨δ₁, δ₂⟩² ≠ 4`, and then so is `W^⊥`, which completes
the signature:

* `Mukai.restrict_orthogonal_pair_nondegenerate`: **`B` is nondegenerate on `W^⊥`** for
  `⟨δ₁, δ₂⟩² ≠ 4`, since `V = W ⊕ W^⊥`. For linearly independent roots this is an equivalence
  (`Mukai.restrict_orthogonal_pair_nondegenerate_iff`): at `⟨δ₁, δ₂⟩ = ±2` the isotropic vector
  `δ₁ ± δ₂` lies in `W ∩ W^⊥`, the radical of `W^⊥`, and every positive semidefinite plane of
  `W^⊥` contains it (`Mukai.add_smul_mem_of_le_orthogonal_pair`).
* `Mukai.sigNeg_orthogonal_pair`, `Mukai.finrank_orthogonal_pair`: **`W^⊥` has signature
  `(1, n - 1)`**: `sigNeg(B|_{W^⊥}) + 1 = sigNeg B` and `dim W^⊥ + 2 = dim V`. For the Mukai
  lattice of a K3 surface of Picard rank `ρ`, `n = ρ`.
* `Mukai.exists_neg_of_le_orthogonal_pair`: **`W^⊥` contains no positive semidefinite plane**:
  every subspace of `W^⊥` of dimension at least two contains a vector of negative square. The
  negative definite part of `W^⊥` has codimension one, so it meets every such subspace
  (`QuadraticForm.exists_neg_of_two_le_finrank`).

So for `|⟨δ₁, δ₂⟩| > 2` the complement `W^⊥` is Lorentzian of signature `(1, n - 1)`, with no
positive plane and no positive semidefinite plane: no positive period is orthogonal to both roots,
and neither is any limit of positive periods. At `|⟨δ₁, δ₂⟩| = 2` every positive semidefinite
plane of `W^⊥` passes through the radical vector `δ₁ ± δ₂`, and the radical vector together with a
positive vector of `W^⊥`, when there is one, spans such a plane.
-/

open Module

/-! ### A codimension-one negative definite part meets every plane -/

namespace QuadraticForm

variable {U : Type*} [AddCommGroup U] [Module ℝ U] [FiniteDimensional ℝ U]

omit [FiniteDimensional ℝ U] in
/-- **The quadratic form of a nondegenerate symmetric bilinear form has zero radical.** -/
lemma radical_toQuadraticMap_eq_bot (B : LinearMap.BilinForm ℝ U) (hB : ∀ x y, B x y = B y x)
    (hnd : ∀ w, (∀ y, B w y = 0) → w = 0) : B.toQuadraticMap.radical = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun x hx => hnd x fun y => ?_
  have h := LinearMap.congr_fun (show _ ∧ _ from hx).2 y
  rw [QuadraticMap.polarBilin_apply_apply, LinearMap.BilinMap.polar_toQuadraticMap,
    LinearMap.zero_apply, hB y x] at h
  linarith

/-- **A nondegenerate form with one positive direction is negative on every plane.** If `Q` has
zero radical and `sigPos Q = 1`, every subspace of dimension at least two contains a vector `x`
with `Q x < 0`: the negative definite part has dimension `dim U - 1` and meets it. -/
theorem exists_neg_of_two_le_finrank (Q : QuadraticForm ℝ U) (hrad : Q.radical = ⊥)
    (hsig : sigPos Q = 1) {P : Submodule ℝ U} (hP : 2 ≤ finrank ℝ P) : ∃ x ∈ P, Q x < 0 := by
  have hsum := sigPos_add_sigNeg_add_radical (Q := Q)
  rw [hrad, finrank_bot, add_zero, hsig] at hsum
  obtain ⟨N, hNdim, hN⟩ := exists_finrank_eq_sigNeg_and_negDef Q
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq P N
  have hle := Submodule.finrank_le (P ⊔ N)
  have hinf : P ⊓ N ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at hsup
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinf
  obtain ⟨hxP, hxN⟩ := Submodule.mem_inf.mp hx
  refine ⟨x, hxP, ?_⟩
  have h : 0 < -(Q x) := hN ⟨x, hxN⟩ (fun h => hx0 (congrArg Subtype.val h))
  linarith

end QuadraticForm

namespace Mukai

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- The orthogonal complement of a subspace `W` of dimension at most two that contains two roots
with `|⟨δ₁, δ₂⟩| > 2` has one positive direction, in signature `(2, n)`. -/
theorem sigPos_orthogonal_eq_one_of_two_lt (B : LinearMap.BilinForm ℝ V)
    (hB : ∀ x y, B x y = B y x) (hnd : ∀ w, (∀ y, B w y = 0) → w = 0)
    (hsig : sigPos B.toQuadraticMap = 2) {δ₁ δ₂ : V} (h₁ : B δ₁ δ₁ = -2) (h₂ : B δ₂ δ₂ = -2)
    (ha : 4 < B δ₁ δ₂ ^ 2) {W : Submodule ℝ V} (hδ₁W : δ₁ ∈ W) (hδ₂W : δ₂ ∈ W)
    (hWdim : finrank ℝ W ≤ 2) : sigPos (B.restrict (B.orthogonal W)).toQuadraticMap = 1 := by
  obtain ⟨Wp, hWp⟩ : ∃ Wp, Wp = B.orthogonal W := ⟨_, rfl⟩
  rw [← hWp]
  have horth : ∀ x ∈ Wp, ∀ w ∈ W, B w x = 0 := fun x hx w hw => by
    rw [hWp] at hx
    exact hx w hw
  -- the positive vector `u` of `W`, orthogonal to `δ₂`
  obtain ⟨a, haB⟩ : ∃ a, a = B δ₁ δ₂ := ⟨_, rfl⟩
  rw [← haB] at ha
  obtain ⟨u, hudef⟩ : ∃ u, u = δ₁ + (a / 2) • δ₂ := ⟨_, rfl⟩
  have huW : u ∈ W := hudef ▸ W.add_mem hδ₁W (W.smul_mem _ hδ₂W)
  have huu : 0 < B u u := by
    rw [hudef]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h₁,
      h₂, hB δ₂ δ₁, ← haB]
    nlinarith
  have hu0 : u ≠ 0 := fun h => by simp [h] at huu
  have hsq : ∀ x ∈ Wp, ∀ y ∈ W, ∀ t : ℝ, B (x + t • y) (x + t • y) = B x x + t ^ 2 * B y y :=
    fun x hx y hy t => by
      have h1 : B y x = 0 := horth x hx y hy
      have h2 : B x y = 0 := by rw [hB]; exact h1
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h1,
        h2]
      ring
  -- `dim W^⊥ ≥ dim V - 2`
  have hnd' : B.Nondegenerate := ⟨hnd, fun y hy => hnd y fun x => by rw [hB]; exact hy x⟩
  have hWpdim : finrank ℝ V ≤ finrank ℝ Wp + 2 := by
    have h := LinearMap.BilinForm.finrank_orthogonal hnd' W
    rw [← hWp] at h
    have hle := Submodule.finrank_le W
    omega
  apply le_antisymm
  · -- a positive plane of `W^⊥` and `u` would span a positive three-space
    by_contra hlt
    push Not at hlt
    obtain ⟨P, hPdim, hPpos⟩ := exists_finrank_eq_sigPos_and_posDef
      (B.restrict Wp).toQuadraticMap
    obtain ⟨P', hP'⟩ : ∃ P' : Submodule ℝ V, P' = P.map Wp.subtype := ⟨_, rfl⟩
    have hP'dim : finrank ℝ P' = finrank ℝ P := by
      rw [hP']
      exact Submodule.finrank_map_subtype_eq Wp P
    have hP'Wp : ∀ x ∈ P', x ∈ Wp := fun x hx => by
      rw [hP'] at hx
      obtain ⟨y, -, rfl⟩ := hx
      exact y.2
    have hP'pos : ∀ x ∈ P', x ≠ 0 → 0 < B x x := fun x hx hx0 => by
      rw [hP'] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      have hy0 : (⟨y, hy⟩ : P) ≠ 0 := fun h => hx0 (by
        have := congrArg (fun z : P => ((z : Wp) : V)) h
        simpa using this)
      have := hPpos ⟨y, hy⟩ hy0
      simpa using this
    have hdisj : P' ⊓ (ℝ ∙ u) = ⊥ := by
      refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
      obtain ⟨hxP, hxu⟩ := Submodule.mem_inf.mp hx
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hxu
      have := horth _ (hP'Wp _ hxP) u huW
      rw [map_smul, smul_eq_mul] at this
      rw [(mul_eq_zero.mp this).resolve_right huu.ne', zero_smul]
    have hpos : (B.toQuadraticMap.restrict (P' ⊔ ℝ ∙ u)).PosDef := by
      intro z hz
      obtain ⟨x, hx, w, hw, hxw⟩ := Submodule.mem_sup.mp z.2
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hw
      change 0 < B (z : V) (z : V)
      rw [← hxw, hsq x (hP'Wp x hx) u huW t]
      by_cases hx0 : x = 0
      · have ht : t ≠ 0 := by
          rintro rfl
          apply hz
          ext
          simp [← hxw, hx0]
        rw [hx0, map_zero, zero_add]
        have : 0 < t ^ 2 := by positivity
        exact mul_pos this huu
      · have := hP'pos x hx hx0
        have : 0 ≤ t ^ 2 * B u u := mul_nonneg (sq_nonneg t) huu.le
        linarith
    have h3 := le_sigPos_of_posDef B.toQuadraticMap hpos
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq P' (ℝ ∙ u)
    rw [hdisj, finrank_bot, finrank_span_singleton hu0] at hsup
    omega
  · -- otherwise `W^⊥` with `δ₂` would be negative semidefinite of dimension `dim V - 1`
    by_contra hlt
    push Not at hlt
    have hnonpos : ∀ x ∈ Wp, B x x ≤ 0 := fun x hx => by
      by_contra hpos
      push Not at hpos
      have hx0 : (⟨x, hx⟩ : Wp) ≠ 0 := fun h => by
        rw [show x = 0 from congrArg Subtype.val h] at hpos
        simp at hpos
      have hline : ((B.restrict Wp).toQuadraticMap.restrict (ℝ ∙ (⟨x, hx⟩ : Wp))).PosDef := by
        intro z hz
        obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp z.2
        have ht0 : t ≠ 0 := by
          rintro rfl
          apply hz
          ext
          simp [← ht]
        change 0 < B ((z : Wp) : V) ((z : Wp) : V)
        rw [← ht]
        simp only [SetLike.val_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]
        have : 0 < t ^ 2 := by positivity
        nlinarith
      have := le_sigPos_of_posDef _ hline
      rw [finrank_span_singleton hx0] at this
      omega
    have hδ₂0 : δ₂ ≠ 0 := fun h => by simp [h] at h₂
    have hdisj : Wp ⊓ (ℝ ∙ δ₂) = ⊥ := by
      refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
      obtain ⟨hxWp, hxδ⟩ := Submodule.mem_inf.mp hx
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hxδ
      have := horth _ hxWp δ₂ hδ₂W
      rw [map_smul, smul_eq_mul, h₂] at this
      have : t = 0 := by linarith
      rw [this, zero_smul]
    have hU : ∀ y ∈ Wp ⊔ (ℝ ∙ δ₂), B.toQuadraticMap y ≤ 0 := fun y hy => by
      obtain ⟨x, hx, w, hw, rfl⟩ := Submodule.mem_sup.mp hy
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hw
      change B (x + t • δ₂) (x + t • δ₂) ≤ 0
      rw [hsq x hx δ₂ hδ₂W t, h₂]
      have := hnonpos x hx
      nlinarith [sq_nonneg t]
    have h3 := QuadraticForm.sigPos_add_finrank_le_of_nonpos hU
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq Wp (ℝ ∙ δ₂)
    rw [hdisj, finrank_bot, finrank_span_singleton hδ₂0] at hsup
    omega

/-- **The orthogonal complement of two roots with `|⟨δ₁, δ₂⟩| > 2` has one positive direction**:
for `W = span(δ₁, δ₂)` in signature `(2, n)`, `sigPos(B|_{W^⊥}) = 1`. -/
theorem sigPos_orthogonal_pair_eq_one (B : LinearMap.BilinForm ℝ V) (hB : ∀ x y, B x y = B y x)
    (hnd : ∀ w, (∀ y, B w y = 0) → w = 0) (hsig : sigPos B.toQuadraticMap = 2) {δ₁ δ₂ : V}
    (h₁ : B δ₁ δ₁ = -2) (h₂ : B δ₂ δ₂ = -2) (ha : 4 < B δ₁ δ₂ ^ 2) :
    sigPos (B.restrict (B.orthogonal (Submodule.span ℝ {δ₁, δ₂}))).toQuadraticMap = 1 := by
  classical
  refine sigPos_orthogonal_eq_one_of_two_lt B hB hnd hsig h₁ h₂ ha
    (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp)) ?_
  have := finrank_span_le_card (R := ℝ) ({δ₁, δ₂} : Set V)
  have hc : ({δ₁, δ₂} : Set V).toFinset.card ≤ 2 := by
    rw [Set.toFinset_insert, Set.toFinset_singleton]
    exact (Finset.card_insert_le _ _).trans (by simp)
  omega

/-! ### Nondegeneracy, the signature `(1, n - 1)` and no positive semidefinite plane -/

omit [FiniteDimensional ℝ V] in
/-- **The Gram matrix of two roots with `⟨δ₁, δ₂⟩² ≠ 4` is invertible**: if `s δ₁ + t δ₂` is
orthogonal to both roots, then `s = t = 0`. -/
lemma eq_zero_of_orthogonal_pair (B : LinearMap.BilinForm ℝ V) (hB : ∀ x y, B x y = B y x)
    {δ₁ δ₂ : V} (h₁ : B δ₁ δ₁ = -2) (h₂ : B δ₂ δ₂ = -2) (ha : B δ₁ δ₂ ^ 2 ≠ 4) {s t : ℝ}
    (hs₁ : B (s • δ₁ + t • δ₂) δ₁ = 0) (hs₂ : B (s • δ₁ + t • δ₂) δ₂ = 0) : s = 0 ∧ t = 0 := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h₁, h₂,
    hB δ₂ δ₁] at hs₁ hs₂
  have hs : s * (B δ₁ δ₂ ^ 2 - 4) = 0 := by linear_combination B δ₁ δ₂ * hs₂ + 2 * hs₁
  have hs0 : s = 0 := (mul_eq_zero.mp hs).resolve_right (sub_ne_zero.mpr ha)
  subst hs0
  exact ⟨rfl, by linarith⟩

omit [FiniteDimensional ℝ V] in
/-- **Two roots with `⟨δ₁, δ₂⟩² ≠ 4` are linearly independent.** -/
theorem linearIndependent_pair_of_sq_ne_four (B : LinearMap.BilinForm ℝ V)
    (hB : ∀ x y, B x y = B y x) {δ₁ δ₂ : V} (h₁ : B δ₁ δ₁ = -2) (h₂ : B δ₂ δ₂ = -2)
    (ha : B δ₁ δ₂ ^ 2 ≠ 4) : LinearIndependent ℝ ![δ₁, δ₂] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  exact eq_zero_of_orthogonal_pair B hB h₁ h₂ ha (by rw [hst]; simp) (by rw [hst]; simp)

omit [FiniteDimensional ℝ V] in
/-- `W = span(δ₁, δ₂)` is a plane when `⟨δ₁, δ₂⟩² ≠ 4`. -/
theorem finrank_span_pair_of_sq_ne_four (B : LinearMap.BilinForm ℝ V)
    (hB : ∀ x y, B x y = B y x) {δ₁ δ₂ : V} (h₁ : B δ₁ δ₁ = -2) (h₂ : B δ₂ δ₂ = -2)
    (ha : B δ₁ δ₂ ^ 2 ≠ 4) : finrank ℝ (Submodule.span ℝ {δ₁, δ₂}) = 2 := by
  have := finrank_span_eq_card (linearIndependent_pair_of_sq_ne_four B hB h₁ h₂ ha)
  rwa [Matrix.range_cons_cons_empty, Fintype.card_fin] at this

omit [FiniteDimensional ℝ V] in
/-- **Two roots with `⟨δ₁, δ₂⟩² ≠ 4` span a nondegenerate plane.** -/
theorem restrict_span_pair_nondegenerate (B : LinearMap.BilinForm ℝ V)
    (hB : ∀ x y, B x y = B y x) {δ₁ δ₂ : V} (h₁ : B δ₁ δ₁ = -2) (h₂ : B δ₂ δ₂ = -2)
    (ha : B δ₁ δ₂ ^ 2 ≠ 4) : (B.restrict (Submodule.span ℝ {δ₁, δ₂})).Nondegenerate := by
  have hsep : ∀ w ∈ Submodule.span ℝ {δ₁, δ₂}, B w δ₁ = 0 → B w δ₂ = 0 → w = 0 := by
    intro w hw hw₁ hw₂
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hw
    obtain ⟨rfl, rfl⟩ := eq_zero_of_orthogonal_pair B hB h₁ h₂ ha hw₁ hw₂
    simp
  have hδ₁ : δ₁ ∈ Submodule.span ℝ {δ₁, δ₂} := Submodule.subset_span (by simp)
  have hδ₂ : δ₂ ∈ Submodule.span ℝ {δ₁, δ₂} := Submodule.subset_span (by simp)
  refine ⟨fun w hw => Subtype.ext (hsep w w.2 (hw ⟨δ₁, hδ₁⟩) (hw ⟨δ₂, hδ₂⟩)), fun w hw =>
    Subtype.ext (hsep w w.2 ?_ ?_)⟩
  · rw [hB]
    exact hw ⟨δ₁, hδ₁⟩
  · rw [hB]
    exact hw ⟨δ₂, hδ₂⟩

/-- **`B` is nondegenerate on `W^⊥` when `⟨δ₁, δ₂⟩² ≠ 4`**, for `W = span(δ₁, δ₂)`: the plane `W`
is nondegenerate, so `V = W ⊕ W^⊥`, and `W^⊥` is nondegenerate with `(W^⊥)^⊥ = W`. -/
theorem restrict_orthogonal_pair_nondegenerate (B : LinearMap.BilinForm ℝ V)
    (hB : ∀ x y, B x y = B y x) (hnd : ∀ w, (∀ y, B w y = 0) → w = 0) {δ₁ δ₂ : V}
    (h₁ : B δ₁ δ₁ = -2) (h₂ : B δ₂ δ₂ = -2) (ha : B δ₁ δ₂ ^ 2 ≠ 4) :
    (B.restrict (B.orthogonal (Submodule.span ℝ {δ₁, δ₂}))).Nondegenerate := by
  have hnd' : B.Nondegenerate := ⟨hnd, fun y hy => hnd y fun x => by rw [hB]; exact hy x⟩
  have hrefl : B.IsRefl := fun x y h => by rw [hB]; exact h
  have hW := LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hrefl
    (restrict_span_pair_nondegenerate B hB h₁ h₂ ha)
  rw [LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal hrefl,
    LinearMap.BilinForm.orthogonal_orthogonal hnd' hrefl]
  exact hW.symm

omit [FiniteDimensional ℝ V] in
/-- At `a = ⟨δ₁, δ₂⟩` with `a² = 4`, the vector `δ₁ + (a/2) δ₂` of `W = span(δ₁, δ₂)` is orthogonal
to `W`. -/
lemma add_smul_mem_orthogonal_pair (B : LinearMap.BilinForm ℝ V) (hB : ∀ x y, B x y = B y x)
    {δ₁ δ₂ : V} (h₁ : B δ₁ δ₁ = -2) (h₂ : B δ₂ δ₂ = -2) (ha : B δ₁ δ₂ ^ 2 = 4) :
    δ₁ + (B δ₁ δ₂ / 2) • δ₂ ∈ B.orthogonal (Submodule.span ℝ {δ₁, δ₂}) := by
  have hu₁ : B δ₁ (δ₁ + (B δ₁ δ₂ / 2) • δ₂) = 0 := by
    simp only [map_add, map_smul, smul_eq_mul, h₁]
    linear_combination ha / 2
  have hu₂ : B δ₂ (δ₁ + (B δ₁ δ₂ / 2) • δ₂) = 0 := by
    simp only [map_add, map_smul, smul_eq_mul, h₂, hB δ₂ δ₁]
    ring
  intro w hw
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hw
  change B (s • δ₁ + t • δ₂) (δ₁ + (B δ₁ δ₂ / 2) • δ₂) = 0
  rw [LinearMap.map_add₂, LinearMap.map_smul₂, LinearMap.map_smul₂, hu₁, hu₂, smul_zero,
    smul_zero, add_zero]

/-- **`W^⊥` is nondegenerate exactly when `⟨δ₁, δ₂⟩² ≠ 4`**, for linearly independent roots. At
`⟨δ₁, δ₂⟩ = a = ±2` the vector `δ₁ + (a/2) δ₂` is nonzero and lies in `W ∩ W^⊥`, so it is in the
radical of `B` on `W^⊥`. -/
theorem restrict_orthogonal_pair_nondegenerate_iff (B : LinearMap.BilinForm ℝ V)
    (hB : ∀ x y, B x y = B y x) (hnd : ∀ w, (∀ y, B w y = 0) → w = 0) {δ₁ δ₂ : V}
    (h₁ : B δ₁ δ₁ = -2) (h₂ : B δ₂ δ₂ = -2) (hind : LinearIndependent ℝ ![δ₁, δ₂]) :
    (B.restrict (B.orthogonal (Submodule.span ℝ {δ₁, δ₂}))).Nondegenerate ↔
      B δ₁ δ₂ ^ 2 ≠ 4 := by
  refine ⟨fun hW ha => ?_, restrict_orthogonal_pair_nondegenerate B hB hnd h₁ h₂⟩
  have huW := add_smul_mem_orthogonal_pair B hB h₁ h₂ ha
  have hu0 : δ₁ + (B δ₁ δ₂ / 2) • δ₂ ≠ 0 := fun h => by
    have := (LinearIndependent.pair_iff.mp hind) 1 (B δ₁ δ₂ / 2) (by rw [one_smul]; exact h)
    exact one_ne_zero this.1
  refine hu0 (congrArg Subtype.val (hW.1 ⟨_, huW⟩ fun y => ?_))
  obtain ⟨y, hy⟩ := y
  have hδy : ∀ w ∈ Submodule.span ℝ {δ₁, δ₂}, B w y = 0 := hy
  change B (δ₁ + (B δ₁ δ₂ / 2) • δ₂) y = 0
  exact hδy _ (Submodule.add_mem _ (Submodule.subset_span (by simp))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))

/-- **At pairing `±2` every positive semidefinite plane orthogonal to both roots contains
`δ₁ ± δ₂`.** For linearly independent roots with `a = ⟨δ₁, δ₂⟩ = ±2`, in signature `(2, n)`, every
subspace `P ≤ W^⊥` of dimension at least two on which `B` is positive semidefinite contains the
isotropic vector `δ₁ + (a/2) δ₂`. Otherwise `P` and that vector, which is orthogonal to `P`, would
span a positive semidefinite subspace of dimension at least three, while a positive semidefinite
subspace has dimension at most `dim V - sigNeg B = 2`
(`QuadraticForm.sigPos_add_finrank_le_of_nonpos`). -/
theorem add_smul_mem_of_le_orthogonal_pair (B : LinearMap.BilinForm ℝ V)
    (hB : ∀ x y, B x y = B y x) (hnd : ∀ w, (∀ y, B w y = 0) → w = 0)
    (hsig : sigPos B.toQuadraticMap = 2) {δ₁ δ₂ : V} (h₁ : B δ₁ δ₁ = -2) (h₂ : B δ₂ δ₂ = -2)
    (hind : LinearIndependent ℝ ![δ₁, δ₂]) (ha : B δ₁ δ₂ ^ 2 = 4) {P : Submodule ℝ V}
    (hP : P ≤ B.orthogonal (Submodule.span ℝ {δ₁, δ₂})) (hPdim : 2 ≤ finrank ℝ P)
    (hpsd : ∀ x ∈ P, 0 ≤ B x x) : δ₁ + (B δ₁ δ₂ / 2) • δ₂ ∈ P := by
  have huWp := add_smul_mem_orthogonal_pair B hB h₁ h₂ ha
  have huW : δ₁ + (B δ₁ δ₂ / 2) • δ₂ ∈ Submodule.span ℝ {δ₁, δ₂} :=
    Submodule.add_mem _ (Submodule.subset_span (by simp))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hu0 : δ₁ + (B δ₁ δ₂ / 2) • δ₂ ≠ 0 := fun h => by
    have := (LinearIndependent.pair_iff.mp hind) 1 (B δ₁ δ₂ / 2) (by rw [one_smul]; exact h)
    exact one_ne_zero this.1
  obtain ⟨u, hu⟩ : ∃ u, u = δ₁ + (B δ₁ δ₂ / 2) • δ₂ := ⟨_, rfl⟩
  rw [← hu] at huWp huW hu0 ⊢
  -- `u` is isotropic and orthogonal to `P`
  have hup : ∀ p ∈ P, B u p = 0 := fun p hp => hP hp u huW
  have huu : B u u = 0 := huWp u huW
  by_contra hnot
  have hdisj : P ⊓ (ℝ ∙ u) = ⊥ := by
    refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
    obtain ⟨hxP, hxu⟩ := Submodule.mem_inf.mp hx
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hxu
    by_cases ht : t = 0
    · rw [ht, zero_smul]
    · exact absurd ((P.smul_mem_iff ht).mp hxP) hnot
  -- so `P ⊔ ℝu` is positive semidefinite of dimension `dim P + 1`
  have hS : ∀ x ∈ P ⊔ (ℝ ∙ u), (-B.toQuadraticMap) x ≤ 0 := fun x hx => by
    obtain ⟨p, hp, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hw
    change -(B (p + t • u) (p + t • u)) ≤ 0
    have h₃ := hup p hp
    have h₄ : B p u = 0 := by rw [hB]; exact h₃
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h₃, h₄,
      huu, mul_zero, add_zero]
    linarith [hpsd p hp]
  have hle := QuadraticForm.sigPos_add_finrank_le_of_nonpos hS
  rw [sigPos_neg] at hle
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq P (ℝ ∙ u)
  rw [hdisj, finrank_bot, finrank_span_singleton hu0] at hsup
  have hV := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := B.toQuadraticMap)
  rw [QuadraticForm.radical_toQuadraticMap_eq_bot B hB hnd, finrank_bot, add_zero, hsig] at hV
  omega

/-- **`W^⊥` has dimension `dim V - 2`** when `⟨δ₁, δ₂⟩² ≠ 4`. -/
theorem finrank_orthogonal_pair (B : LinearMap.BilinForm ℝ V) (hB : ∀ x y, B x y = B y x)
    (hnd : ∀ w, (∀ y, B w y = 0) → w = 0) {δ₁ δ₂ : V} (h₁ : B δ₁ δ₁ = -2) (h₂ : B δ₂ δ₂ = -2)
    (ha : B δ₁ δ₂ ^ 2 ≠ 4) :
    finrank ℝ (B.orthogonal (Submodule.span ℝ {δ₁, δ₂})) + 2 = finrank ℝ V := by
  have hnd' : B.Nondegenerate := ⟨hnd, fun y hy => hnd y fun x => by rw [hB]; exact hy x⟩
  have h := LinearMap.BilinForm.finrank_orthogonal hnd' (Submodule.span ℝ {δ₁, δ₂})
  have h2 := finrank_span_pair_of_sq_ne_four B hB h₁ h₂ ha
  have hle := Submodule.finrank_le (Submodule.span ℝ {δ₁, δ₂})
  omega

/-- **`W^⊥` has signature `(1, n - 1)`** for `⟨δ₁, δ₂⟩² > 4`, in signature `(2, n)`:
`sigPos(B|_{W^⊥}) = 1` (`sigPos_orthogonal_pair_eq_one`) and `sigNeg(B|_{W^⊥}) + 1 = sigNeg B`,
since `B` is nondegenerate on `V` and on `W^⊥` and `dim W^⊥ = dim V - 2`. -/
theorem sigNeg_orthogonal_pair (B : LinearMap.BilinForm ℝ V) (hB : ∀ x y, B x y = B y x)
    (hnd : ∀ w, (∀ y, B w y = 0) → w = 0) (hsig : sigPos B.toQuadraticMap = 2) {δ₁ δ₂ : V}
    (h₁ : B δ₁ δ₁ = -2) (h₂ : B δ₂ δ₂ = -2) (ha : 4 < B δ₁ δ₂ ^ 2) :
    sigNeg (B.restrict (B.orthogonal (Submodule.span ℝ {δ₁, δ₂}))).toQuadraticMap + 1 =
      sigNeg B.toQuadraticMap := by
  have hWnd := restrict_orthogonal_pair_nondegenerate B hB hnd h₁ h₂ ha.ne'
  have hpos := sigPos_orthogonal_pair_eq_one B hB hnd hsig h₁ h₂ ha
  have hdim := finrank_orthogonal_pair B hB hnd h₁ h₂ ha.ne'
  have hV := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := B.toQuadraticMap)
  rw [QuadraticForm.radical_toQuadraticMap_eq_bot B hB hnd, finrank_bot, add_zero, hsig] at hV
  have hW := QuadraticForm.sigPos_add_sigNeg_add_radical
    (Q := (B.restrict (B.orthogonal (Submodule.span ℝ {δ₁, δ₂}))).toQuadraticMap)
  rw [QuadraticForm.radical_toQuadraticMap_eq_bot
    (B.restrict (B.orthogonal (Submodule.span ℝ {δ₁, δ₂}))) (fun x y => hB (x : V) (y : V))
    hWnd.1, finrank_bot, add_zero, hpos] at hW
  omega

/-- **`W^⊥` contains no positive semidefinite plane** for `⟨δ₁, δ₂⟩² > 4`, in signature `(2, n)`:
every subspace `P ≤ W^⊥` of dimension at least two contains a vector of negative square. So no
plane of `W^⊥` is a limit of positive periods. At `⟨δ₁, δ₂⟩² = 4` this fails as soon as `W^⊥` has
a positive vector `x`: `x` and the radical vector of `restrict_orthogonal_pair_nondegenerate_iff`
span a positive semidefinite plane. -/
theorem exists_neg_of_le_orthogonal_pair (B : LinearMap.BilinForm ℝ V)
    (hB : ∀ x y, B x y = B y x) (hnd : ∀ w, (∀ y, B w y = 0) → w = 0)
    (hsig : sigPos B.toQuadraticMap = 2) {δ₁ δ₂ : V} (h₁ : B δ₁ δ₁ = -2) (h₂ : B δ₂ δ₂ = -2)
    (ha : 4 < B δ₁ δ₂ ^ 2) {P : Submodule ℝ V}
    (hP : P ≤ B.orthogonal (Submodule.span ℝ {δ₁, δ₂})) (hPdim : 2 ≤ finrank ℝ P) :
    ∃ x ∈ P, B x x < 0 := by
  have hWnd := restrict_orthogonal_pair_nondegenerate B hB hnd h₁ h₂ ha.ne'
  have hrad := QuadraticForm.radical_toQuadraticMap_eq_bot
    (B.restrict (B.orthogonal (Submodule.span ℝ {δ₁, δ₂}))) (fun x y => hB (x : V) (y : V))
    hWnd.1
  have hpos := sigPos_orthogonal_pair_eq_one B hB hnd hsig h₁ h₂ ha
  have hP' : finrank ℝ (P.comap (B.orthogonal (Submodule.span ℝ {δ₁, δ₂})).subtype) =
      finrank ℝ P :=
    (Submodule.comapSubtypeEquivOfLe hP).finrank_eq
  obtain ⟨x, hx, hneg⟩ := QuadraticForm.exists_neg_of_two_le_finrank _ hrad hpos
    (P := P.comap (B.orthogonal (Submodule.span ℝ {δ₁, δ₂})).subtype) (hP' ▸ hPdim)
  exact ⟨x, hx, hneg⟩

end Mukai
