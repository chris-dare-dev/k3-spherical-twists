/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.GroupTheory.Coxeter.ArtinGroup
import K3Twists.LinearAlgebra.BilinearForm.Reflection
import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# The reflection representation of a simply laced Coxeter group

Let `Λ` be an abelian group with a symmetric bilinear form `b`, and let `α : B → Λ` be vectors of
norm `b(α_i, α_i) = -2` whose pairings `b(α_i, α_j) = e i j` (`i ≠ j`) are natural numbers. The
reflections `ρ_i(v) = v + b(v, α_i) α_i` satisfy the Coxeter relations of the matrix
`CoxeterMatrix.ofExt e` (`m = 2, 3, ∞` for `e = 0, 1, ≥ 2`), so they define a representation of
its Coxeter group, `CoxeterMatrix.reflectionRep`. For `Λ = ℤ^B`, `α_i = e_i` and the form with
Gram matrix `-2` on the diagonal and `e` off it (`CoxeterMatrix.rootForm`), this is the
geometric representation of the Weyl group of the symmetric generalized Cartan matrix `2 - e`
(Bourbaki, *Groupes et algèbres de Lie*, Ch. V §4; Kac, *Infinite dimensional Lie algebras*,
§3.7). The simply laced matrices of finite type `A_n`, `D_n`, `E_n` are the cases `e i j ≤ 1`
whose form is negative definite.

The sign is the Mukai sign. In a `2`-Calabi–Yau category, `b` is minus the Euler form, the class
of a spherical object has norm `-2`, two spherical objects with total Ext `e` pair to `e` when
their Homs sit in one degree, and `ρ_{v(S)}` is the action of the twist `T_S` on classes. So the
matrix `ofExt e` here is the one Seidel and Thomas attach to a configuration of spherical objects
(arXiv:math/0001043, §2).

## Words, prefix roots and positivity

A word `ω = [i₁, …, i_k]` acts by `ρ_{i₁} ∘ ⋯ ∘ ρ_{i_k}` (`BilinearForm.reflectWord`). Its *prefix
roots* are `β_j = ρ_{i₁} ⋯ ρ_{i_{j-1}} α_{i_j}` (`BilinearForm.prefixRoots`), and the word is
*root-positive* if every `β_j` is a nonempty sum of the `α_i` (`BilinearForm.IsRootPositive`).
Tits' positivity theorem says that in the geometric representation a word is reduced exactly
when it is root-positive (Humphreys, *Reflection groups and Coxeter groups*, §5.4 and §5.6; Kac,
Lemma 3.11). It is stated as `CoxeterMatrix.CoxeterPositivity` and **not proved here**: its proof
runs through the dihedral subgroups and is the main Coxeter gap of the Weyl-gallery induction,
which therefore takes root-positive words as input.

Root-positivity transfers along any additive map that matches the Gram matrices
(`BilinearForm.IsRootPositive.map`, `BilinearForm.IsRootPositive.of_rootForm`), so it can be
checked once on `ℤ^B`, where it is a finite computation, and used for the classes of a
configuration in any lattice.

## Lengths from a finite root set

If a finite set `Φ` is mapped into itself by each `ρ(s_i)` except at one point, then the number of
elements of `Φ` that `ρ(w)` moves out of `Φ` is at most the length of `w`
(`CoxeterSystem.inversionCount_le_length`). With `Φ` the positive roots of a finite type this
gives the lower bound on lengths that proves explicit words reduced
(`CoxeterSystem.isReduced_of_length_le_inversionCount`). It uses no positivity theorem.

## Explicit words for `A_n`

`CoxeterMatrix.longestWordA n = [0] ++ [1, 0] ++ ⋯ ++ [n-1, …, 0]` has length `n(n+1)/2`. For
`n ≤ 6` this file checks by computation that it is reduced and root-positive and that it sends
`α_i` to `-α_{n-1-i}`, so it is a reduced word of the longest element `w₀`, whose diagram
automorphism is `i ↦ n-1-i`. `GroupTheory/Coxeter/TypeA.lean` proves the same for every `n`, in
the coordinates `ε_k` in which `W(A_n)` acts by permutations.

## Main definitions

* `BilinearForm.reflectWord`, `BilinearForm.prefixRoots`, `BilinearForm.positiveCone`,
  `BilinearForm.IsRootPositive`.
* `CoxeterMatrix.reflectionRep`: the representation `W(ofExt e) →* GL(Λ)`.
* `CoxeterMatrix.rootMatrix`, `CoxeterMatrix.rootForm`: the standard form on `ℤ^B`.
* `CoxeterMatrix.CoxeterPositivity`: Tits' positivity theorem, as an open statement.
* `CoxeterSystem.inversionCount`.
* `CoxeterMatrix.extA`, `CoxeterMatrix.longestWordA`.
-/

open CoxeterSystem

namespace BilinearForm

variable {B Λ Λ' : Type*} [AddCommGroup Λ] [AddCommGroup Λ']
variable (b : LinearMap.BilinForm ℤ Λ) (α : B → Λ)

/-! ### Words, prefix roots and positivity -/

/-- The action of a word: `reflectWord b α [i₁, …, i_k] = ρ_{α i₁} ∘ ⋯ ∘ ρ_{α i_k}`, the rightmost
letter applied first. -/
def reflectWord (ω : List B) : Module.End ℤ Λ := (ω.map fun i => reflectHom b (α i)).prod

@[simp] theorem reflectWord_nil : reflectWord b α [] = 1 := rfl

@[simp] theorem reflectWord_cons_apply (i : B) (ω : List B) (v : Λ) :
    reflectWord b α (i :: ω) v = reflect b (α i) (reflectWord b α ω v) := by
  simp [reflectWord, mul_apply_eq_comp]

theorem reflectWord_append (ω ω' : List B) :
    reflectWord b α (ω ++ ω') = reflectWord b α ω * reflectWord b α ω' := by
  simp [reflectWord]

theorem reflectWord_append_apply (ω ω' : List B) (v : Λ) :
    reflectWord b α (ω ++ ω') v = reflectWord b α ω (reflectWord b α ω' v) := by
  rw [reflectWord_append, mul_apply_eq_comp]

/-- The prefix roots `β_j = ρ_{i₁} ⋯ ρ_{i_{j-1}} α_{i_j}` of the word `[i₁, …, i_k]`. -/
def prefixRoots : List B → List Λ
  | [] => []
  | i :: ω => α i :: (prefixRoots ω).map (reflect b (α i))

@[simp] theorem prefixRoots_nil : prefixRoots b α [] = [] := rfl

@[simp] theorem prefixRoots_cons (i : B) (ω : List B) :
    prefixRoots b α (i :: ω) = α i :: (prefixRoots b α ω).map (reflect b (α i)) := rfl

/-- The last prefix root of `ω ++ [i]` is `ρ_ω (α_i)`. -/
theorem prefixRoots_append_singleton (ω : List B) (i : B) :
    prefixRoots b α (ω ++ [i]) = prefixRoots b α ω ++ [reflectWord b α ω (α i)] := by
  induction ω with
  | nil => simp
  | cons j ω ih => simp [ih]

/-- The positive cone: the nonempty sums of the `α i`. When the `α i` are linearly independent
these are the nonzero vectors with nonnegative coordinates in the `α i`. -/
def positiveCone : AddSubsemigroup Λ := AddSubsemigroup.closure (Set.range α)

theorem mem_positiveCone (i : B) : α i ∈ positiveCone α :=
  AddSubsemigroup.subset_closure ⟨i, rfl⟩

/-- A word is root-positive if all its prefix roots are positive. -/
def IsRootPositive (ω : List B) : Prop := ∀ β ∈ prefixRoots b α ω, β ∈ positiveCone α

theorem isRootPositive_nil : IsRootPositive b α [] := by simp [IsRootPositive]

theorem isRootPositive_append_singleton {ω : List B} {i : B} :
    IsRootPositive b α (ω ++ [i]) ↔
      IsRootPositive b α ω ∧ reflectWord b α ω (α i) ∈ positiveCone α := by
  simp [IsRootPositive, prefixRoots_append_singleton, or_imp, forall_and]

/-! ### Transport along a map matching the Gram matrices -/

variable {b α} {b' : LinearMap.BilinForm ℤ Λ'} {α' : B → Λ'}

theorem map_reflect (φ : Λ →ₗ[ℤ] Λ') {s : Λ} {s' : Λ'} (hs : φ s = s')
    (hφ : ∀ x, b' (φ x) s' = b x s) (v : Λ) : φ (reflect b s v) = reflect b' s' (φ v) := by
  rw [reflect_apply, reflect_apply, map_add, map_zsmul, hs, hφ]

theorem map_reflectWord (φ : Λ →ₗ[ℤ] Λ') (hα : ∀ i, φ (α i) = α' i)
    (hφ : ∀ x i, b' (φ x) (α' i) = b x (α i)) (ω : List B) (v : Λ) :
    φ (reflectWord b α ω v) = reflectWord b' α' ω (φ v) := by
  induction ω with
  | nil => rfl
  | cons i ω ih => rw [reflectWord_cons_apply, reflectWord_cons_apply, ← ih,
      map_reflect φ (hα i) (fun x => hφ x i)]

theorem prefixRoots_map (φ : Λ →ₗ[ℤ] Λ') (hα : ∀ i, φ (α i) = α' i)
    (hφ : ∀ x i, b' (φ x) (α' i) = b x (α i)) (ω : List B) :
    prefixRoots b' α' ω = (prefixRoots b α ω).map φ := by
  induction ω with
  | nil => rfl
  | cons i ω ih =>
    simp only [prefixRoots_cons, ih, List.map_cons, List.map_map, hα]
    congr 1
    refine List.map_congr_left fun v _ => ?_
    exact (map_reflect φ (hα i) (fun x => hφ x i) v).symm

theorem map_mem_positiveCone (φ : Λ →ₗ[ℤ] Λ') (hα : ∀ i, φ (α i) = α' i) {v : Λ}
    (hv : v ∈ positiveCone α) : φ v ∈ positiveCone α' := by
  induction hv using AddSubsemigroup.closure_induction with
  | mem v hv =>
    obtain ⟨i, rfl⟩ := hv
    rw [hα]
    exact mem_positiveCone α' i
  | add v w _ _ hv hw =>
    rw [map_add]
    exact add_mem hv hw

/-- **Root-positivity transfers** along a linear map that sends the roots to the roots and
matches the pairings with them. -/
theorem IsRootPositive.map (φ : Λ →ₗ[ℤ] Λ') (hα : ∀ i, φ (α i) = α' i)
    (hφ : ∀ x i, b' (φ x) (α' i) = b x (α i)) {ω : List B} (h : IsRootPositive b α ω) :
    IsRootPositive b' α' ω := by
  intro β hβ
  rw [prefixRoots_map φ hα hφ, List.mem_map] at hβ
  obtain ⟨β, hβ, rfl⟩ := hβ
  exact map_mem_positiveCone φ hα (h β hβ)

/-! ### Conjugation and the braid relations -/

/-- `ρ_s ρ_t ρ_s = ρ_{ρ_s t}`: the lattice form of `T_{Φ S} ≅ Φ T_S Φ⁻¹` for `Φ = T_s`. -/
theorem reflect_reflect_reflect (hb : ∀ x y, b x y = b y x) {s : Λ} (hs : b s s = -2)
    (t v : Λ) : reflect b s (reflect b t (reflect b s v)) = reflect b (reflect b s t) v := by
  have h1 : b (reflect b s v) t = b v (reflect b s t) := by
    conv_lhs => rw [← apply_reflect_reflect b hb s hs (reflect b s v) t,
      reflect_reflect b s hs]
  rw [reflect_apply b t, reflect_add, reflect_smul, reflect_reflect b s hs, h1,
    reflect_apply b (reflect b s t)]

variable (b α) in
/-- **The reflections satisfy the braid relations of `ofExt e`**: `ρ_i` and `ρ_j` commute when
`b(α_i, α_j) = 0` and satisfy `ρ_i ρ_j ρ_i = ρ_j ρ_i ρ_j` when `b(α_i, α_j) = 1`, both being
reflections in the same root. -/
theorem isBraidLiftable_reflectEquiv [DecidableEq B] (hb : ∀ x y, b x y = b y x)
    (hα : ∀ i, b (α i) (α i) = -2) (e : B → B → ℕ) (he : ∀ i j, e i j = e j i)
    (hαe : ∀ i j, i ≠ j → b (α i) (α j) = e i j) :
    (CoxeterMatrix.ofExt e he).IsBraidLiftable fun i => reflectEquiv b (α i) (hα i) := by
  refine CoxeterMatrix.isBraidLiftable_ofExt e he _ (fun i j hij h0 => ?_)
    (fun i j hij h1 => ?_)
  · refine LinearEquiv.ext fun v => ?_
    simp only [mul_apply_eq_comp, reflectEquiv_apply]
    have hji : reflect b (α i) (α j) = α j :=
      reflect_of_apply_eq_zero b (by rw [hαe j i hij.symm, he, h0, Nat.cast_zero])
    have h := reflect_reflect_reflect hb (hα i) (α j) (reflect b (α i) v)
    rwa [reflect_reflect b _ (hα i), hji] at h
  · refine LinearEquiv.ext fun v => ?_
    simp only [mul_apply_eq_comp, reflectEquiv_apply]
    have hij' : reflect b (α i) (α j) = reflect b (α j) (α i) := by
      rw [reflect_apply, reflect_apply, hαe j i hij.symm, hαe i j hij, he, h1, Nat.cast_one,
        one_smul, one_smul, add_comm]
    rw [reflect_reflect_reflect hb (hα i), reflect_reflect_reflect hb (hα j), hij']

end BilinearForm

namespace CoxeterMatrix

open BilinearForm

variable {B Λ : Type*} [DecidableEq B] [AddCommGroup Λ]
variable (e : B → B → ℕ) (he : ∀ i j, e i j = e j i)

/-! ### The reflection representation -/

section Representation

variable {b : LinearMap.BilinForm ℤ Λ} {α : B → Λ} (hb : ∀ x y, b x y = b y x)
  (hα : ∀ i, b (α i) (α i) = -2) (hαe : ∀ i j, i ≠ j → b (α i) (α j) = e i j)

/-- **The reflection representation** `W(ofExt e) →* GL(Λ)`, `s_i ↦ ρ_{α i}`. -/
def reflectionRep : (ofExt e he).Group →* (Λ ≃ₗ[ℤ] Λ) :=
  (ofExt e he).toCoxeterSystem.lift ⟨fun i => reflectEquiv b (α i) (hα i),
    (ofExt e he).isLiftable_of_braid _ (isBraidLiftable_reflectEquiv b α hb hα e he hαe)
      fun i => LinearEquiv.ext fun v => by
        simpa [mul_apply_eq_comp] using reflect_reflect b (α i) (hα i) v⟩

@[simp] theorem reflectionRep_simple (i : B) :
    reflectionRep e he hb hα hαe ((ofExt e he).simple i) = reflectEquiv b (α i) (hα i) := by
  rw [← toCoxeterSystem_simple]
  exact CoxeterSystem.lift_apply_simple _ _ i

/-- A word acts through the reflection representation as the composite of its reflections. -/
theorem reflectionRep_wordProd_apply (ω : List B) (v : Λ) :
    reflectionRep e he hb hα hαe ((ofExt e he).toCoxeterSystem.wordProd ω) v =
      reflectWord b α ω v := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, map_mul, mul_apply_eq_comp, ih, toCoxeterSystem_simple,
      reflectionRep_simple,
      reflectEquiv_apply, reflectWord_cons_apply]

end Representation

/-! ### The standard form on `ℤ^B` -/

section Standard

variable [Fintype B]

/-- The Gram matrix `-2` on the diagonal and `e i j` off it: minus the generalized Cartan
matrix `2 - e`. -/
def rootMatrix : Matrix B B ℤ := Matrix.of fun i j => if i = j then -2 else (e i j : ℤ)

/-- The standard form on `ℤ^B`, with Gram matrix `rootMatrix e` in the basis `e_i`. -/
def rootForm : LinearMap.BilinForm ℤ (B → ℤ) := Matrix.toBilin' (rootMatrix e)

/-- The simple roots `e_i` of `ℤ^B`. -/
abbrev stdRoot (i : B) : B → ℤ := Pi.single i 1

@[simp] theorem rootForm_stdRoot (i j : B) :
    rootForm e (stdRoot i) (stdRoot j) = if i = j then -2 else (e i j : ℤ) := by
  simp [rootForm, rootMatrix]

include he in
theorem rootForm_symm : ∀ x y, rootForm e x y = rootForm e y x := by
  intro x y
  simp only [rootForm, Matrix.toBilin'_apply, rootMatrix, Matrix.of_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases h : i = j
  · subst h; ring
  · simp only [h, Ne.symm h, ↓reduceIte]; rw [he j i]; ring

theorem rootForm_stdRoot_self (i : B) : rootForm e (stdRoot i) (stdRoot i) = -2 := by simp

theorem rootForm_stdRoot_of_ne (i j : B) (h : i ≠ j) :
    rootForm e (stdRoot i) (stdRoot j) = e i j := by simp [h]

theorem rootForm_apply_stdRoot (v : B → ℤ) (i : B) :
    rootForm e v (stdRoot i) = ∑ j, v j * rootMatrix e j i := by
  simp [rootForm, Matrix.toBilin'_apply, Pi.single_apply]

/-- **Coxeter positivity** (Tits): for the geometric representation of `W(ofExt e)` on `ℤ^B`, a
word is reduced if and only if it is root-positive (Humphreys, *Reflection groups and Coxeter
groups*, Theorem 5.4; Kac, *Infinite dimensional Lie algebras*, Lemma 3.11). Open here; the
Weyl-gallery induction takes root-positive words as input instead. -/
def CoxeterPositivity : Prop :=
  ∀ ω : List B, (ofExt e he).toCoxeterSystem.IsReduced ω ↔
    IsRootPositive (rootForm e) stdRoot ω

/-- One step of the standard reflection, as an explicit function. -/
def stdReflect (i : B) (v : B → ℤ) : B → ℤ := v + (∑ j, v j * rootMatrix e j i) • stdRoot i

theorem reflect_rootForm (i : B) (v : B → ℤ) :
    reflect (rootForm e) (stdRoot i) v = stdReflect e i v := by
  rw [reflect_apply, rootForm_apply_stdRoot, stdReflect]

/-- The standard action of a word, as an explicit function. -/
def stdWord (ω : List B) (v : B → ℤ) : B → ℤ := ω.foldr (stdReflect e) v

theorem reflectWord_rootForm (ω : List B) (v : B → ℤ) :
    reflectWord (rootForm e) stdRoot ω v = stdWord e ω v := by
  induction ω with
  | nil => rfl
  | cons i ω ih => rw [reflectWord_cons_apply, ih, reflect_rootForm]; rfl

/-- The standard prefix roots, as an explicit list. -/
def stdPrefixRoots : List B → List (B → ℤ)
  | [] => []
  | i :: ω => stdRoot i :: (stdPrefixRoots ω).map (stdReflect e i)

theorem prefixRoots_rootForm (ω : List B) :
    prefixRoots (rootForm e) stdRoot ω = stdPrefixRoots e ω := by
  induction ω with
  | nil => rfl
  | cons i ω ih =>
    simp only [prefixRoots_cons, ih, stdPrefixRoots]
    congr 1
    exact List.map_congr_left fun v _ => reflect_rootForm e i v

/-- A vector of `ℤ^B` with nonnegative coordinates, not zero, is a nonempty sum of the `e_i`. -/
theorem mem_positiveCone_stdRoot {v : B → ℤ} (h0 : ∀ k, 0 ≤ v k) (hv : v ≠ 0) :
    v ∈ positiveCone (stdRoot (B := B)) := by
  induction hN : ∑ k, (v k).toNat using Nat.strong_induction_on generalizing v with
  | _ N ih =>
    obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
      by_contra! h
      exact hv (funext h)
    have hk1 : 1 ≤ v k := by have := h0 k; omega
    by_cases hs : v = stdRoot k
    · rw [hs]; exact mem_positiveCone _ k
    set v' := v - stdRoot k with hv'
    have hv'k : ∀ j, v' j = v j - if j = k then 1 else 0 := fun j => by
      simp [hv', Pi.single_apply]
    have h0' : ∀ j, 0 ≤ v' j := fun j => by
      rw [hv'k]; split_ifs with hj
      · subst hj; omega
      · simpa using h0 j
    have hne : v' ≠ 0 := fun h => hs (by rw [← sub_eq_zero]; exact h)
    have hlt : ∑ j, (v' j).toNat < N := by
      rw [← hN]
      refine Finset.sum_lt_sum (fun j _ => ?_) ⟨k, Finset.mem_univ k, ?_⟩
      · rw [hv'k]; split_ifs <;> omega
      · simp only [hv'k, ↓reduceIte]; omega
    have := ih _ hlt h0' hne rfl
    have hsum : v = v' + stdRoot k := by rw [hv', sub_add_cancel]
    rw [hsum]
    exact add_mem this (mem_positiveCone _ k)

omit [Fintype B] in
/-- Conversely, a nonempty sum of the `e_i` has nonnegative coordinates and is not zero. -/
theorem nonneg_of_mem_positiveCone_stdRoot {v : B → ℤ}
    (hv : v ∈ positiveCone (stdRoot (B := B))) : (∀ k, 0 ≤ v k) ∧ v ≠ 0 := by
  induction hv using AddSubsemigroup.closure_induction with
  | mem v hv =>
    obtain ⟨i, rfl⟩ := hv
    refine ⟨fun k => ?_, fun h => ?_⟩
    · simp only [stdRoot, Pi.single_apply]; split_ifs <;> norm_num
    · simpa using congr_fun h i
  | add v w _ _ hv hw =>
    refine ⟨fun k => add_nonneg (hv.1 k) (hw.1 k), fun h => hv.2 (funext fun k => ?_)⟩
    have := congr_fun h k
    have := hv.1 k
    have := hw.1 k
    simp only [Pi.add_apply, Pi.zero_apply] at *
    omega

/-- **Root-positivity on `ℤ^B` is a finite check**: every standard prefix root has nonnegative
coordinates and is nonzero. -/
theorem isRootPositive_rootForm_iff {ω : List B} :
    IsRootPositive (rootForm e) stdRoot ω ↔
      ∀ β ∈ stdPrefixRoots e ω, (∀ k, 0 ≤ β k) ∧ β ≠ 0 := by
  rw [IsRootPositive, prefixRoots_rootForm]
  exact forall₂_congr fun β _ =>
    ⟨nonneg_of_mem_positiveCone_stdRoot, fun h => mem_positiveCone_stdRoot h.1 h.2⟩

theorem isRootPositive_rootForm_of {ω : List B}
    (h : ∀ β ∈ stdPrefixRoots e ω, (∀ k, 0 ≤ β k) ∧ β ≠ 0) :
    IsRootPositive (rootForm e) stdRoot ω :=
  (isRootPositive_rootForm_iff e).2 h

variable {Λ' : Type*} [AddCommGroup Λ'] {b' : LinearMap.BilinForm ℤ Λ'} {α' : B → Λ'}

/-- The linear map `ℤ^B → Λ'`, `e_i ↦ α'_i`. -/
abbrev rootMap (α' : B → Λ') : (B → ℤ) →ₗ[ℤ] Λ' := Fintype.linearCombination ℤ α'

theorem rootMap_stdRoot (i : B) : rootMap α' (stdRoot i) = α' i := by
  simp [Fintype.linearCombination_apply, Pi.single_apply]

theorem rootForm_rootMap (hG : ∀ i j, b' (α' j) (α' i) = rootMatrix e j i) (x : B → ℤ)
    (i : B) : b' (rootMap α' x) (α' i) = rootForm e x (stdRoot i) := by
  rw [rootForm_apply_stdRoot, Fintype.linearCombination_apply, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, LinearMap.smul_apply, hG, smul_eq_mul]

/-- **Root-positivity on `ℤ^B` gives root-positivity for any configuration with Gram matrix
`rootMatrix e`.** -/
theorem _root_.BilinearForm.IsRootPositive.of_rootForm
    (hG : ∀ i j, b' (α' j) (α' i) = rootMatrix e j i)
    {ω : List B} (h : IsRootPositive (rootForm e) stdRoot ω) : IsRootPositive b' α' ω :=
  h.map (rootMap α') rootMap_stdRoot (rootForm_rootMap e hG)

/-- The action of a word on a configuration with Gram matrix `rootMatrix e` is computed on
`ℤ^B`. -/
theorem reflectWord_of_rootForm (hG : ∀ i j, b' (α' j) (α' i) = rootMatrix e j i)
    (ω : List B) (v : B → ℤ) :
    reflectWord b' α' ω (rootMap α' v) = rootMap α' (stdWord e ω v) := by
  rw [← reflectWord_rootForm, map_reflectWord (rootMap α') rootMap_stdRoot
    (rootForm_rootMap e hG)]

end Standard

end CoxeterMatrix

/-! ### Lengths from a finite root set -/

namespace CoxeterSystem

variable {B W G X : Type*} [Group W] [Group G] [MulAction G X] [DecidableEq X]
  {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

/-- The number of elements of `Φ` that `g` moves out of `Φ`. For `Φ` the positive roots of a
finite root system and `g = ρ(w)`, it is the number of inversions of `w`. -/
def inversionCount (Φ : Finset X) (g : G) : ℕ := (Φ.filter fun x => g • x ∉ Φ).card

theorem inversionCount_one (Φ : Finset X) : inversionCount Φ (1 : G) = 0 := by
  simp [inversionCount]

/-- If `r` maps `Φ` into itself except at `x₀`, multiplying by `r` adds at most one to the
count. -/
theorem inversionCount_mul_le (Φ : Finset X) {r : G} {x₀ : X}
    (hr : ∀ y ∈ Φ, y ≠ x₀ → r • y ∈ Φ) (g : G) :
    inversionCount Φ (r * g) ≤ inversionCount Φ g + 1 := by
  refine (Finset.card_le_card (t := insert (g⁻¹ • x₀) (Φ.filter fun x => g • x ∉ Φ))
    fun x hx => ?_).trans (Finset.card_insert_le _ _)
  rw [Finset.mem_filter, mul_smul] at hx
  rw [Finset.mem_insert, Finset.mem_filter]
  by_cases hgx : g • x ∈ Φ
  · by_cases h : g • x = x₀
    · exact Or.inl (by rw [← h, inv_smul_smul])
    · exact absurd (hr _ hgx h) hx.2
  · exact Or.inr ⟨hx.1, hgx⟩

variable (ρ : W →* G) {Φ : Finset X}
  (hΦ : ∀ i, ∃ x₀, ∀ y ∈ Φ, y ≠ x₀ → ρ (cs.simple i) • y ∈ Φ)
include hΦ

theorem inversionCount_wordProd_le (ω : List B) :
    inversionCount Φ (ρ (cs.wordProd ω)) ≤ ω.length := by
  induction ω with
  | nil => simp [inversionCount_one]
  | cons i ω ih =>
    obtain ⟨x₀, hx₀⟩ := hΦ i
    rw [wordProd_cons, map_mul, List.length_cons]
    exact (inversionCount_mul_le Φ hx₀ _).trans (by omega)

/-- **The inversion count is a lower bound for the length.** -/
theorem inversionCount_le_length (w : W) : inversionCount Φ (ρ w) ≤ cs.length w := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  rw [hω.eq]
  exact cs.inversionCount_wordProd_le ρ hΦ ω

/-- A word with as many inversions as letters is reduced. -/
theorem isReduced_of_length_le_inversionCount {ω : List B}
    (h : ω.length ≤ inversionCount Φ (ρ (cs.wordProd ω))) : cs.IsReduced ω :=
  le_antisymm (cs.length_wordProd_le ω) (h.trans (cs.inversionCount_le_length ρ hΦ _))

end CoxeterSystem

/-! ### Explicit words for `A_n` -/

namespace CoxeterMatrix

open BilinearForm

/-- The total Ext numbers of the `A_n` chain: `1` between neighbours, `0` otherwise. -/
def extA (n : ℕ) (i j : Fin n) : ℕ := if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then 1 else 0

theorem extA_symm (n : ℕ) (i j : Fin n) : extA n i j = extA n j i := by
  simp only [extA, or_comm]

/-- Mathlib's `A_n` is the Seidel–Thomas matrix of the `A_n` chain. -/
theorem A_eq_ofExt (n : ℕ) : CoxeterMatrix.A n = ofExt (extA n) (extA_symm n) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [ofExt]
  · have h' : (i : ℕ) ≠ j := fun h'' => h (Fin.ext h'')
    simp only [CoxeterMatrix.A, ofExt, extA, Matrix.of_apply, h, ↓reduceIte]
    split_ifs <;> first | omega | contradiction

/-- `longestWordA n = [0] ++ [1, 0] ++ ⋯ ++ [n-1, …, 0]`, a word for the longest element of
`W(A_n)`: the longest word of `A_{n-1}` followed by `s_{n-1} ⋯ s_0`. -/
def longestWordA : (n : ℕ) → List (Fin n)
  | 0 => []
  | n + 1 => (longestWordA n).map Fin.castSucc ++ (List.finRange (n + 1)).reverse

theorem length_longestWordA (n : ℕ) : (longestWordA n).length = n * (n + 1) / 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [longestWordA, List.length_append, List.length_map, ih, List.length_reverse,
      List.length_finRange]
    rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [show (k + k) * (k + k + 1) = 2 * (k * (2 * k + 1)) by ring,
        show (k + k + 1) * (k + k + 1 + 1) = 2 * ((2 * k + 1) * (k + 1)) by ring]
      simp only [Nat.mul_div_cancel_left _ two_pos]
      ring
    · rw [show (2 * k + 1) * (2 * k + 1 + 1) = 2 * ((2 * k + 1) * (k + 1)) by ring,
        show (2 * k + 1 + 1) * (2 * k + 1 + 1 + 1) = 2 * ((k + 1) * (2 * k + 3)) by ring]
      simp only [Nat.mul_div_cancel_left _ two_pos]
      ring

/-- A positive word in the Artin group is the product of its generators. -/
theorem ArtinGroup.ofSignedWord_map_true {B : Type*} (M : CoxeterMatrix B) (ω : List B) :
    ArtinGroup.ofSignedWord M (ω.map fun i => (i, true)) = (ω.map M.artinGen).prod := by
  have h := ArtinGroup.lift_ofSignedWord M.artinGen ArtinGroup.isBraidLiftable_artinGen
    (ω.map fun i => (i, true))
  rw [show ArtinGroup.lift M.artinGen ArtinGroup.isBraidLiftable_artinGen = MonoidHom.id _ from
    ArtinGroup.hom_ext fun i => by simp] at h
  simpa [List.map_map, Function.comp_def] using h

/-- The positive roots of `A_n` in the basis of simple roots: the interval sums
`α_a + ⋯ + α_c` for `a ≤ c`. -/
def positiveRootsA (n : ℕ) : Finset (Fin n → ℤ) :=
  ((Finset.univ : Finset (Fin n × Fin n)).filter fun p => p.1 ≤ p.2).image
    fun p k => if p.1 ≤ k ∧ k ≤ p.2 then 1 else 0

/-- `s_i` maps the positive roots other than `α_i` to positive roots: the computed cases
`n ≤ 6`. For every `n` this is `stdReflect_mem_positiveRootsA'`. -/
theorem stdReflect_mem_positiveRootsA {n : ℕ} (hn : n ≤ 6) (i : Fin n) (y : Fin n → ℤ)
    (hy : y ∈ positiveRootsA n) (hne : y ≠ stdRoot i) :
    stdReflect (extA n) i y ∈ positiveRootsA n := by
  revert i y
  interval_cases n <;> decide

/-- `w₀ = longestWordA n` sends `α_i` to `-α_{n-1-i}`: the computed cases `n ≤ 6`. For every `n`
this is `stdWord_longestWordA'`. -/
theorem stdWord_longestWordA {n : ℕ} (hn : n ≤ 6) (i : Fin n) :
    stdWord (extA n) (longestWordA n) (stdRoot i) = -stdRoot i.rev := by
  revert i
  interval_cases n <;> decide

/-- `longestWordA n` is root-positive: the computed cases `n ≤ 6`. For every `n` this is
`isRootPositive_longestWordA'`. -/
theorem isRootPositive_longestWordA {n : ℕ} (hn : n ≤ 6) :
    IsRootPositive (rootForm (extA n)) stdRoot (longestWordA n) := by
  refine isRootPositive_rootForm_of _ ?_
  interval_cases n <;> decide

/-- `longestWordA n` moves all `n(n+1)/2` positive roots out of the positive roots: the computed
cases `n ≤ 6`. For every `n` this is `inversionCount_longestWordA'`. -/
theorem inversionCount_longestWordA {n : ℕ} (hn : n ≤ 6) :
    ((positiveRootsA n).filter fun x => stdWord (extA n) (longestWordA n) x ∉
      positiveRootsA n).card = n * (n + 1) / 2 := by
  interval_cases n <;> decide

/-- **`longestWordA n` is a reduced word** of `W(A_n)` (the computed cases `n ≤ 6`; for every `n`
this is `isReduced_longestWordA'`), by the inversion count of the reflection representation: it
moves all `n(n+1)/2` positive roots out of the positive roots. -/
theorem isReduced_longestWordA {n : ℕ} (hn : n ≤ 6) :
    (CoxeterMatrix.A n).toCoxeterSystem.IsReduced (longestWordA n) := by
  rw [A_eq_ofExt]
  have hρ := reflectionRep_wordProd_apply (extA n) (extA_symm n)
    (rootForm_symm (extA n) (extA_symm n)) (rootForm_stdRoot_self (extA n))
    (rootForm_stdRoot_of_ne (extA n))
  refine (ofExt (extA n) (extA_symm n)).toCoxeterSystem.isReduced_of_length_le_inversionCount
    (reflectionRep (extA n) (extA_symm n) (rootForm_symm (extA n) (extA_symm n))
      (rootForm_stdRoot_self (extA n)) (rootForm_stdRoot_of_ne (extA n)))
    (Φ := positiveRootsA n) (fun i => ⟨stdRoot i, fun y hy hne => ?_⟩) ?_
  · have h := hρ [i] y
    rw [CoxeterSystem.wordProd_singleton] at h
    rw [LinearEquiv.smul_def, h, reflectWord_cons_apply, reflectWord_nil, one_apply_eq_self,
      reflect_rootForm]
    exact stdReflect_mem_positiveRootsA hn i y hy hne
  · rw [CoxeterSystem.inversionCount, length_longestWordA]
    refine le_of_eq ?_
    rw [← inversionCount_longestWordA hn]
    congr 1
    refine Finset.filter_congr fun x _ => ?_
    rw [LinearEquiv.smul_def, hρ, reflectWord_rootForm]

end CoxeterMatrix
