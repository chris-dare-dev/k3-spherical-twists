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

So `W^⊥` is Lorentzian (of signature `(1, n - 1)` once `B` is nondegenerate on it, as it is for a
nondegenerate `W`), and it contains no positive plane: no positive period is orthogonal to both
roots.
-/

open Module

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

end Mukai
