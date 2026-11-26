/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.GroupTheory.Coxeter.GeometricRepresentation
import K3Twists.LinearAlgebra.Matrix.ZMatrix.SignCoherence

/-!
# Real roots of a loopless quiver

A loopless quiver with `e i j = e j i` arrows between distinct vertices `i`, `j` (the `Ext`-quiver
of a configuration of spherical objects) has the root form `rootForm e` on `ℤ^σ`, with Gram
matrix `-2` on the diagonal and `e` off it (`GroupTheory/Coxeter/GeometricRepresentation.lean`).
This is the Mukai sign: `rootForm e v v = -2 q(v)` for the Tits form `q`. The simple reflection at
`i` is `stdReflect e i`.

* **Real roots** are the images of the simple roots `eᵢ` under words of simple reflections
  (`CoxeterMatrix.IsRealRoot`). They have norm `-2`, that is `q = 1`
  (`IsRealRoot.rootForm_self`), and the prefix roots of every word are real roots
  (`isRealRoot_of_mem_stdPrefixRoots`).
* **Sign coherence** (`CoxeterMatrix.IsSignCoherent`): every vector of norm `-2` has coordinates
  of one sign. It holds when the Tits form is positive semidefinite with isotropic vectors zero
  or of full support, which covers finite and connected affine type
  (`isSignCoherent_of_posSemidef`, from `Matrix.IsZMatrix.signCoherent`).
* **Descent** (`exists_eq_stdRoot_of_reflect_invariant`): for a sign-coherent form, every
  positive vector of norm `-2` is a real root, and a function invariant under the simple
  reflections between positive vectors takes there its value at a simple root. The proof is
  descent on the height. `Σ vᵢ (Cv)ᵢ = 2` for the Cartan matrix `C` gives a vertex with `vᵢ > 0`
  and `(Cv)ᵢ > 0`. Then `sᵢ v = v - (Cv)ᵢ eᵢ` has smaller height, and it is positive by sign
  coherence unless `v = eᵢ`.

Kac (*Infinite dimensional Lie algebras*, §5.1 and Chapter 5) describes the real and imaginary
roots of a symmetrizable generalized Cartan matrix; here only the real roots and the sign-coherent
case are used.
-/

open Matrix

namespace CoxeterMatrix

variable {B : Type*} [Fintype B] [DecidableEq B] (e : B → B → ℕ)

/-- A positive vector: nonnegative coordinates, not zero. -/
def IsPositiveVector (v : B → ℤ) : Prop :=
  (∀ i, 0 ≤ v i) ∧ v ≠ 0

theorem isPositiveVector_iff_mem_positiveCone {v : B → ℤ} :
    IsPositiveVector v ↔ v ∈ BilinearForm.positiveCone (stdRoot (B := B)) :=
  ⟨fun h => mem_positiveCone_stdRoot h.1 h.2, nonneg_of_mem_positiveCone_stdRoot⟩

omit [Fintype B] in
theorem isPositiveVector_stdRoot (i : B) : IsPositiveVector (stdRoot i : B → ℤ) :=
  ⟨fun k => by simp only [stdRoot, Pi.single_apply]; split_ifs <;> norm_num,
    fun h => by simpa using congr_fun h i⟩

/-- **A real root**: the image of a simple root under a word of simple reflections. -/
def IsRealRoot (v : B → ℤ) : Prop :=
  ∃ (ω : List B) (i : B), v = stdWord e ω (stdRoot i)

theorem stdWord_cons (i : B) (ω : List B) (v : B → ℤ) :
    stdWord e (i :: ω) v = stdReflect e i (stdWord e ω v) :=
  rfl

theorem isRealRoot_stdRoot (i : B) : IsRealRoot e (stdRoot i) :=
  ⟨[], i, rfl⟩

theorem IsRealRoot.stdReflect {v : B → ℤ} (hv : IsRealRoot e v) (i : B) :
    IsRealRoot e (stdReflect e i v) := by
  obtain ⟨ω, j, rfl⟩ := hv
  exact ⟨i :: ω, j, rfl⟩

/-- The simple reflections are isometries of the root form. -/
theorem rootForm_stdReflect (he : ∀ i j, e i j = e j i) (i : B) (v w : B → ℤ) :
    rootForm e (stdReflect e i v) (stdReflect e i w) = rootForm e v w := by
  rw [← reflect_rootForm, ← reflect_rootForm]
  exact BilinearForm.apply_reflect_reflect _ (rootForm_symm e he) _ (rootForm_stdRoot_self e i) v w

/-- **Real roots have norm `-2`**: `q = 1`. -/
theorem IsRealRoot.rootForm_self (he : ∀ i j, e i j = e j i) {v : B → ℤ} (hv : IsRealRoot e v) :
    rootForm e v v = -2 := by
  obtain ⟨ω, i, rfl⟩ := hv
  induction ω with
  | nil => exact rootForm_stdRoot_self e i
  | cons j ω ih => rw [stdWord_cons, rootForm_stdReflect e he, ih]

/-- **The prefix roots of every word are real roots.** -/
theorem isRealRoot_of_mem_stdPrefixRoots {ω : List B} {v : B → ℤ}
    (hv : v ∈ stdPrefixRoots e ω) : IsRealRoot e v := by
  induction ω generalizing v with
  | nil => simp [stdPrefixRoots] at hv
  | cons i ω ih =>
    simp only [stdPrefixRoots, List.mem_cons, List.mem_map] at hv
    rcases hv with rfl | ⟨u, hu, rfl⟩
    · exact isRealRoot_stdRoot e i
    · exact (ih hu).stdReflect e i

/-! ### Sign coherence -/

/-- The root form is **sign coherent** if every vector of norm `-2` has all coordinates of one
sign. -/
def IsSignCoherent : Prop :=
  ∀ v : B → ℤ, rootForm e v v = -2 → (∀ i, 0 ≤ v i) ∨ ∀ i, v i ≤ 0

theorem rootForm_apply_self (v : B → ℤ) : rootForm e v v = v ⬝ᵥ rootMatrix e *ᵥ v := by
  simp [rootForm, Matrix.toBilin'_apply']

/-- **Positive semidefinite Tits forms whose isotropic vectors are zero or of full support are
sign coherent**: finite type, and connected affine type. -/
theorem isSignCoherent_of_posSemidef (he : ∀ i j, e i j = e j i)
    (hpsd : ∀ v : B → ℤ, rootForm e v v ≤ 0)
    (hiso : ∀ v : B → ℤ, rootForm e v v = 0 → v = 0 ∨ ∀ i, v i ≠ 0) : IsSignCoherent e := by
  intro v hv
  have hneg : ∀ x : B → ℤ, x ⬝ᵥ (-rootMatrix e) *ᵥ x = -rootForm e x x := fun x => by
    rw [rootForm_apply_self, Matrix.neg_mulVec, dotProduct_neg]
  refine Matrix.IsZMatrix.signCoherent (A := -rootMatrix e) (fun i j hij => ?_) ?_
    (fun i => ⟨1, by simp [rootMatrix]⟩) (fun x => by rw [hneg]; linarith [hpsd x])
    (fun x hx => hiso x (by rw [hneg] at hx; linarith)) (by rw [hneg, hv]; norm_num)
  · simp [rootMatrix, hij]
  · ext i j
    simp only [Matrix.transpose_apply, Matrix.neg_apply, rootMatrix, Matrix.of_apply, eq_comm,
      he j i]

/-! ### Descent -/

/-- **Descent on the height.** For a sign-coherent root form, every positive vector of norm `-2`
is a real root, and a function invariant under the simple reflections between positive vectors
takes there its value at a simple root. -/
theorem exists_eq_stdRoot_of_reflect_invariant (he : ∀ i j, e i j = e j i)
    (hsc : IsSignCoherent e) {X : Type*} (f : (B → ℤ) → X)
    (hf : ∀ i v, IsPositiveVector v → v ≠ stdRoot i → IsPositiveVector (stdReflect e i v) →
      f (stdReflect e i v) = f v) :
    ∀ v, IsPositiveVector v → rootForm e v v = -2 → ∃ j, f v = f (stdRoot j) ∧ IsRealRoot e v := by
  suffices key : ∀ (n : ℕ) (v : B → ℤ), IsPositiveVector v → rootForm e v v = -2 →
      ∑ k, v k = n → ∃ j, f v = f (stdRoot j) ∧ IsRealRoot e v from
    fun v hv hn => key _ v hv hn (Int.toNat_of_nonneg (Finset.sum_nonneg fun k _ => hv.1 k)).symm
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hv hnorm hn
    -- some vertex `i` has `vᵢ > 0` and `⟨v, eᵢ⟩ < 0`
    obtain ⟨i, -, hi⟩ : ∃ i ∈ Finset.univ, v i * rootForm e v (stdRoot i) < 0 := by
      by_contra! h
      have hv' : ∑ i, v i • (stdRoot i : B → ℤ) = v := by
        ext k
        simp [Finset.sum_apply, Pi.single_apply]
      have hsum : rootForm e v v = ∑ i, v i * rootForm e v (stdRoot i) := by
        conv_lhs => arg 2; rw [← hv']
        simp only [map_sum, map_zsmul, smul_eq_mul]
      have := Finset.sum_nonneg h
      rw [← hsum, hnorm] at this
      norm_num at this
    have hvi : 0 < v i := lt_of_le_of_ne (hv.1 i) fun h0 => by
      rw [← h0, zero_mul] at hi
      exact lt_irrefl _ hi
    have ht : rootForm e v (stdRoot i) < 0 := by
      by_contra h
      exact absurd hi (not_lt.mpr (mul_nonneg (hv.1 i) (not_lt.mp h)))
    by_cases hvs : v = stdRoot i
    · exact ⟨i, by rw [hvs], hvs ▸ isRealRoot_stdRoot e i⟩
    set w := stdReflect e i v with hw
    have hwv : ∀ k, w k = v k + if k = i then rootForm e v (stdRoot i) else 0 := fun k => by
      rw [hw, stdReflect, ← rootForm_apply_stdRoot]
      simp [Pi.single_apply]
    have hwnorm : rootForm e w w = -2 := by rw [hw, rootForm_stdReflect e he, hnorm]
    -- `v` is not a multiple of `eᵢ`, so some other coordinate is positive
    obtain ⟨j, hji, hvj⟩ : ∃ j, j ≠ i ∧ 0 < v j := by
      by_contra! h
      have hv0 : ∀ k, k ≠ i → v k = 0 := fun k hk => le_antisymm (h k hk) (hv.1 k)
      obtain ⟨c, hc⟩ : ∃ c, v i = c := ⟨_, rfl⟩
      have hvc : v = c • (stdRoot i : B → ℤ) := by
        ext k
        by_cases hk : k = i
        · subst hk
          simp [hc]
        · simp [hk, hv0 k hk]
      have hcc : c * (c * -2) = -2 := by
        have := hnorm
        rw [hvc] at this
        simpa only [map_zsmul, LinearMap.smul_apply, rootForm_stdRoot_self, smul_eq_mul] using this
      have h1 : c = 1 := by nlinarith
      exact hvs (by rw [hvc, h1, one_smul])
    have hwpos : IsPositiveVector w := by
      rcases hsc w hwnorm with h | h
      · refine ⟨h, fun h0 => ?_⟩
        have := hwnorm
        rw [h0] at this
        simp at this
      · exfalso
        have := h j
        rw [hwv j] at this
        simp only [hji, ↓reduceIte, add_zero] at this
        omega
    have hlt : ∑ k, w k < n := by
      have : ∑ k, w k = ∑ k, v k + rootForm e v (stdRoot i) := by
        simp only [hwv, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      rw [this, hn]
      linarith
    have hw0 : 0 ≤ ∑ k, w k := Finset.sum_nonneg fun k _ => hwpos.1 k
    obtain ⟨j', hj', hreal⟩ := ih (∑ k, w k).toNat (by omega) w hwpos hwnorm (by omega)
    refine ⟨j', ?_, ?_⟩
    · rw [← hj', hw, hf i v hv hvs hwpos]
    · have := hreal.stdReflect e i
      rwa [hw, ← reflect_rootForm, ← reflect_rootForm,
        BilinearForm.reflect_reflect _ _ (rootForm_stdRoot_self e i)] at this

end CoxeterMatrix
