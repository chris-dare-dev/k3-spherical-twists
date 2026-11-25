/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Poincaré duality and injectivity in every degree

A nonzero linear map out of a space of dimension at most one is injective
(`LinearMap.injective_of_ne_zero_of_finrank_le_one`). With a pairing that separates its left
argument, injectivity in the top degree propagates to the other degrees.

* **Degree-two lemma** (`LinearMap.injective_of_pairing_of_finrank_le_one`). Let
  `φ₁ : V → V'`, `φ₁' : W → W'` be maps and `φ₂ : X → X'` a linear map with
  `φ₂ (μ v w) = μ' (φ₁ v) (φ₁' w)` for pairings `μ : V → W → X` and `μ' : V' → W' → X'`. If
  `dim X ≤ 1`, `φ₁` is nonzero somewhere, `φ₁'` is onto and `μ'` separates its left argument,
  then `φ₂` is injective, and bijective if also `dim X' ≤ 1`. An arbitrary pairing `μ'` that
  separates its left argument is the input; for shifted morphisms in a category with a Serre
  functor it is composition followed by the Serre trace
  (`CategoryTheory/Triangulated/SerreFunctor/CompositionTrace.lean`).
* **Two-degree form** (`LinearMap.injective_of_separatingLeft`): if `φ_X` is injective, `μ`
  separates its left argument and `φ_X (μ v w) = μ' (φ_V v) (φ_W w)` with `μ'` additive in its
  first argument, then `φ_V` is injective.
* **Poincaré-duality lemma** (`AlgHom.injOn_of_top`). Let `A = ⨁ A_i` be a graded algebra whose
  multiplication `A_i × A_{d-i} → A_d` separates its left argument, with `dim A_d ≤ 1`, and let
  `φ : A → B` be an algebra map nonzero on `A_d`. Then `φ` is injective on every `A_i`, `i ≤ d`.
* **The converse** (`AlgHom.exists_top_ne_zero`, `AlgHom.exists_top_ne_zero_iff`). If the
  multiplication of the target `B_j × B_{d-j} → B_d` separates its left argument (Serre duality
  on the target), `B_j ≠ 0`, and `φ` maps `A_j` onto `B_j` and `A_{d-j}` onto `B_{d-j}`, then `φ`
  is nonzero on `A_d`. With graded `φ` and `dim A_i = dim B_i`, this gives: `φ` is nonzero on
  `A_d` if and only if it is injective in the degrees `i ≤ ⌈d/2⌉`, provided `B_{⌈d/2⌉} ≠ 0`. (For
  an algebra generated in degree one with `A_d ≠ 0`, `A_{⌈d/2⌉} ≠ 0`.)

For a family of point-like objects in a `d`-Calabi–Yau category the Ext algebra of a member has
Poincaré duality with top degree `d`; the last statement says that full faithfulness in the top
degree is decided in degrees `≤ ⌈d/2⌉`.

## Tags

Poincaré duality, graded algebra, nondegenerate pairing, injectivity
-/

open Module

namespace LinearMap

variable {k : Type*} [Field k]

section

variable {X X' : Type*} [AddCommGroup X] [Module k X] [AddCommGroup X'] [Module k X']

/-- A nonzero linear map out of a space of dimension at most one is injective. -/
theorem injective_of_ne_zero_of_finrank_le_one [FiniteDimensional k X] (f : X →ₗ[k] X')
    (hf : f ≠ 0) (hX : finrank k X ≤ 1) : Function.Injective f := by
  rw [← LinearMap.ker_eq_bot]
  by_contra hker
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hker
  have h1 : finrank k X = 1 := le_antisymm hX (Module.finrank_pos_iff_exists_ne_zero.2 ⟨x, hx0⟩)
  apply hf
  ext y
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_ne_zero' x hx0).1 h1 y
  simp [LinearMap.mem_ker.1 hx]

/-- A nonzero linear map between spaces of dimension at most one is bijective. -/
theorem bijective_of_ne_zero_of_finrank_le_one [FiniteDimensional k X] [FiniteDimensional k X']
    (f : X →ₗ[k] X') (hf : f ≠ 0) (hX : finrank k X ≤ 1) (hX' : finrank k X' ≤ 1) :
    Function.Bijective f := by
  have hinj := f.injective_of_ne_zero_of_finrank_le_one hf hX
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (LinearMap.ext h)
  have hpos : 0 < finrank k X := Module.finrank_pos_iff_exists_ne_zero.2
    ⟨x, fun h ↦ hx (by simp [h])⟩
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by lia)).1 hinj⟩

end

variable {V W X V' W' X' : Type*} [AddCommGroup V'] [AddCommGroup X] [Module k X]
  [AddCommGroup X'] [Module k X']

/-- **The degree-two lemma.** If `φ₂ (μ v w) = μ' (φ₁ v) (φ₁' w)`, `dim X ≤ 1`, `φ₁` is nonzero
somewhere, `φ₁'` is onto and `μ'` separates its left argument, then `φ₂` is injective. -/
theorem injective_of_pairing_of_finrank_le_one [FiniteDimensional k X] (μ : V → W → X)
    (μ' : V' → W' → X') (φ₁ : V → V') (φ₁' : W → W') (φ₂ : X →ₗ[k] X')
    (h : ∀ v w, φ₂ (μ v w) = μ' (φ₁ v) (φ₁' w)) (hX : finrank k X ≤ 1)
    (hφ₁ : ∃ v, φ₁ v ≠ 0) (hφ₁' : Function.Surjective φ₁')
    (hμ' : ∀ v', (∀ w', μ' v' w' = 0) → v' = 0) : Function.Injective φ₂ := by
  refine φ₂.injective_of_ne_zero_of_finrank_le_one ?_ hX
  intro h0
  obtain ⟨v, hv⟩ := hφ₁
  apply hv
  refine hμ' _ fun w' ↦ ?_
  obtain ⟨w, rfl⟩ := hφ₁' w'
  rw [← h, h0, LinearMap.zero_apply]

/-- **The degree-two lemma, bijective form**, when also `dim X' ≤ 1`. -/
theorem bijective_of_pairing_of_finrank_le_one [FiniteDimensional k X] [FiniteDimensional k X']
    (μ : V → W → X) (μ' : V' → W' → X') (φ₁ : V → V') (φ₁' : W → W') (φ₂ : X →ₗ[k] X')
    (h : ∀ v w, φ₂ (μ v w) = μ' (φ₁ v) (φ₁' w)) (hX : finrank k X ≤ 1)
    (hX' : finrank k X' ≤ 1) (hφ₁ : ∃ v, φ₁ v ≠ 0) (hφ₁' : Function.Surjective φ₁')
    (hμ' : ∀ v', (∀ w', μ' v' w' = 0) → v' = 0) : Function.Bijective φ₂ := by
  refine φ₂.bijective_of_ne_zero_of_finrank_le_one ?_ hX hX'
  intro h0
  obtain ⟨v, hv⟩ := hφ₁
  apply hv
  refine hμ' _ fun w' ↦ ?_
  obtain ⟨w, rfl⟩ := hφ₁' w'
  rw [← h, h0, LinearMap.zero_apply]

end LinearMap

namespace LinearMap

variable {V W X V' W' X' : Type*} [AddCommGroup V] [AddCommGroup X] [AddCommGroup V']
  [AddCommGroup X']

/-- **The two-degree form.** If `φ_X` is injective, `μ` separates its left argument and
`φ_X (μ v w) = μ' (φ_V v) (φ_W w)` with `μ' 0 = 0`, then `φ_V` is injective. -/
theorem injective_of_separatingLeft (μ : V → W → X) (μ' : V' → W' → X') (φV : V →+ V')
    (φW : W → W') (φX : X →+ X') (h : ∀ v w, φX (μ v w) = μ' (φV v) (φW w))
    (hμ'0 : ∀ w', μ' 0 w' = 0) (hφX : Function.Injective φX)
    (hμ : ∀ v, (∀ w, μ v w = 0) → v = 0) : Function.Injective φV := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  refine hμ v fun w ↦ hφX ?_
  rw [h, hv, hμ'0, map_zero]

end LinearMap

namespace AlgHom

variable {k A B : Type*} [Field k] [Ring A] [Algebra k A] [Ring B] [Algebra k B]
  (𝒜 : ℕ → Submodule k A) [SetLike.GradedMonoid 𝒜]

/-- **The Poincaré-duality lemma.** If `A_i × A_{d-i} → A_d` separates its left argument,
`dim A_d ≤ 1` and the algebra map `φ` is nonzero on `A_d`, then `φ` is injective on `A_i` for
`i ≤ d`. -/
theorem injOn_of_top {d i : ℕ} (hi : i ≤ d) [FiniteDimensional k (𝒜 d)]
    (hd : finrank k (𝒜 d) ≤ 1)
    (hnd : ∀ a ∈ 𝒜 i, (∀ b ∈ 𝒜 (d - i), a * b = 0) → a = 0) (φ : A →ₐ[k] B)
    (hφ : ∃ t ∈ 𝒜 d, φ t ≠ 0) : Set.InjOn φ (𝒜 i) := by
  have hmul : ∀ a ∈ 𝒜 i, ∀ b ∈ 𝒜 (d - i), a * b ∈ 𝒜 d := fun a ha b hb ↦ by
    simpa [Nat.add_sub_cancel' hi] using SetLike.GradedMul.mul_mem ha hb
  let φd : 𝒜 d →ₗ[k] B := (φ.toLinearMap).domRestrict (𝒜 d)
  have hφd : Function.Injective φd := by
    refine φd.injective_of_ne_zero_of_finrank_le_one ?_ hd
    obtain ⟨t, ht, htφ⟩ := hφ
    intro h0
    exact htφ (by simpa [φd] using LinearMap.congr_fun h0 ⟨t, ht⟩)
  have key : ∀ a ∈ 𝒜 i, φ a = 0 → a = 0 := by
    intro a ha hφa
    refine hnd a ha fun b hb ↦ ?_
    have : φd ⟨a * b, hmul a ha b hb⟩ = φd 0 := by
      simp [φd, map_mul, hφa]
    simpa using congrArg Subtype.val (hφd this)
  intro a ha a' ha' heq
  rw [← sub_eq_zero]
  exact key _ (Submodule.sub_mem _ ha ha') (by simp [map_sub, heq])

variable {𝒜} (ℬ : ℕ → Submodule k B)

/-- **The converse, from the target.** If `B_j × B_{d-j} → B_d` separates its left argument,
`B_j ≠ 0`, and `φ` maps `A_j` onto `B_j` and `A_{d-j}` onto `B_{d-j}`, then `φ` is nonzero on
`A_d`. -/
theorem exists_top_ne_zero {d j : ℕ} (hj : j ≤ d)
    (hnd : ∀ b ∈ ℬ j, (∀ b' ∈ ℬ (d - j), b * b' = 0) → b = 0) (hne : ℬ j ≠ ⊥)
    (φ : A →ₐ[k] B) (hsurj : ∀ b ∈ ℬ j, ∃ a ∈ 𝒜 j, φ a = b)
    (hsurj' : ∀ b ∈ ℬ (d - j), ∃ a ∈ 𝒜 (d - j), φ a = b) : ∃ t ∈ 𝒜 d, φ t ≠ 0 := by
  obtain ⟨b, hb, hb0⟩ := (Submodule.ne_bot_iff _).1 hne
  have : ∃ b' ∈ ℬ (d - j), b * b' ≠ 0 := by
    by_contra h
    push Not at h
    exact hb0 (hnd b hb h)
  obtain ⟨b', hb', hbb'⟩ := this
  obtain ⟨a, ha, rfl⟩ := hsurj b hb
  obtain ⟨a', ha', rfl⟩ := hsurj' b' hb'
  refine ⟨a * a', ?_, by simpa [map_mul] using hbb'⟩
  simpa [Nat.add_sub_cancel' hj] using SetLike.GradedMul.mul_mem ha ha'

/-- **Poincaré duality decides the top degree in half the degrees.** Let `φ` be graded with
`dim A_i = dim B_i` (finite), let the multiplications of `A` and `B` into degree `d` separate their
left arguments, `dim A_d ≤ 1` and `B_{⌈d/2⌉} ≠ 0`. Then `φ` is nonzero on `A_d` if and only if it
is injective on `A_i` for every `i ≤ ⌈d/2⌉`. -/
theorem exists_top_ne_zero_iff {d : ℕ} [∀ i, FiniteDimensional k (𝒜 i)]
    [∀ i, FiniteDimensional k (ℬ i)] (hdim : ∀ i, finrank k (𝒜 i) = finrank k (ℬ i))
    (hd : finrank k (𝒜 d) ≤ 1)
    (hndA : ∀ i ≤ d, ∀ a ∈ 𝒜 i, (∀ b ∈ 𝒜 (d - i), a * b = 0) → a = 0)
    (hndB : ∀ i ≤ d, ∀ b ∈ ℬ i, (∀ b' ∈ ℬ (d - i), b * b' = 0) → b = 0)
    (hne : ℬ ((d + 1) / 2) ≠ ⊥) (φ : A →ₐ[k] B) (hgr : ∀ i, ∀ a ∈ 𝒜 i, φ a ∈ ℬ i) :
    (∃ t ∈ 𝒜 d, φ t ≠ 0) ↔ ∀ i ≤ (d + 1) / 2, Set.InjOn φ (𝒜 i) := by
  constructor
  · intro hφ i hi
    exact injOn_of_top 𝒜 (by lia) hd (hndA i (by lia)) φ hφ
  · intro hinj
    have hsurj : ∀ i ≤ (d + 1) / 2, ∀ b ∈ ℬ i, ∃ a ∈ 𝒜 i, φ a = b := by
      intro i hi
      let f : 𝒜 i →ₗ[k] ℬ i := (φ.toLinearMap).restrict (hgr i)
      have hfx : ∀ x, (f x : B) = φ x := fun _ ↦ rfl
      have hf : Function.Injective f := fun x y hxy ↦
        Subtype.ext (hinj i hi x.2 y.2 (by rw [← hfx, ← hfx, hxy]))
      have hfs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hdim i)).1 hf
      intro b hb
      obtain ⟨x, hx⟩ := hfs ⟨b, hb⟩
      exact ⟨x, x.2, by rw [← hfx, hx]⟩
    exact exists_top_ne_zero ℬ (by lia) (hndB _ (by lia)) hne φ (hsurj _ le_rfl)
      (hsurj _ (by lia))

end AlgHom
