/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Pairs of a functional and a vector it kills

On a finite-dimensional vector space `V`, the group `GL(V)` acts transitively on the pairs
`(φ, w)` of a nonzero functional `φ` and a nonzero vector `w` with `φ(w) = 0`. More generally, for
two such pairs on spaces of the same finite dimension there is a linear equivalence carrying one
to the other (`LinearMap.exists_linearEquiv_of_apply_eq_zero`).

## Main definitions

* `LinearMap.equivProdKer φ v₀ h`: the splitting `V ≃ k × ker φ`, `v ↦ (φ v, v - φ v • v₀)`,
  along a vector `v₀` with `φ v₀ = 1`.

## Main results

* `LinearMap.exists_equiv_normalForm`: a pair `(φ, w)` as above has the normal form
  `V ≃ k × (k × U)` in which `φ` is the first coordinate and `w` is `(0, (1, 0))`, with
  `dim U + 2 = dim V`.
* `LinearMap.exists_linearEquiv_of_apply_eq_zero`: **the orbit lemma.** Two pairs on spaces of the
  same finite dimension are carried to each other by a linear equivalence.

The proof splits off a line twice: `V ≃ k × ker φ` along `v₀`, then `ker φ ≃ k × ker ψ` along `w`
for a functional `ψ` on `ker φ` with `ψ(w) = 1`; two spaces `ker ψ` of the same dimension are
isomorphic.
-/

open Module

namespace LinearMap

variable {k V V' : Type*} [Field k] [AddCommGroup V] [Module k V] [AddCommGroup V']
  [Module k V']

/-- The splitting `V ≃ k × ker φ`, `v ↦ (φ v, v - φ v • v₀)`, along a vector `v₀` with
`φ v₀ = 1`; its inverse is `(a, u) ↦ a • v₀ + u`. -/
noncomputable def equivProdKer (φ : V →ₗ[k] k) (v₀ : V) (h : φ v₀ = 1) :
    V ≃ₗ[k] k × ker φ where
  toFun v := (φ v, ⟨v - φ v • v₀, by simp [h]⟩)
  invFun p := p.1 • v₀ + p.2
  map_add' v w := by
    refine Prod.ext (map_add φ v w) (Subtype.ext ?_)
    simp only [map_add, Prod.snd_add, Submodule.coe_add, add_smul]
    abel
  map_smul' c v := by
    refine Prod.ext (map_smul φ c v) (Subtype.ext ?_)
    simp only [map_smul, smul_eq_mul, RingHom.id_apply, Prod.smul_snd, SetLike.val_smul,
      smul_sub, mul_smul]
  left_inv v := by simp
  right_inv p := by
    obtain ⟨a, u, hu⟩ := p
    rw [mem_ker] at hu
    refine Prod.ext ?_ (Subtype.ext ?_)
    · simp [h, hu]
    · simp [h, hu]

@[simp]
lemma equivProdKer_apply_fst (φ : V →ₗ[k] k) (v₀ : V) (h : φ v₀ = 1) (v : V) :
    (equivProdKer φ v₀ h v).1 = φ v :=
  rfl

/-- A vector of `ker φ` goes to `(0, itself)`. -/
lemma equivProdKer_apply_of_mem_ker (φ : V →ₗ[k] k) (v₀ : V) (h : φ v₀ = 1) {w : V}
    (hw : φ w = 0) : equivProdKer φ v₀ h w = (0, ⟨w, hw⟩) := by
  refine Prod.ext hw (Subtype.ext ?_)
  change w - φ w • v₀ = w
  rw [hw, zero_smul, sub_zero]

/-- `v₀` goes to `(1, 0)`. -/
lemma equivProdKer_apply_self (φ : V →ₗ[k] k) (v₀ : V) (h : φ v₀ = 1) :
    equivProdKer φ v₀ h v₀ = (1, 0) := by
  refine Prod.ext h (Subtype.ext ?_)
  change v₀ - φ v₀ • v₀ = 0
  rw [h, one_smul, sub_self]

/-- **The normal form of a functional and a vector it kills.** For `φ ≠ 0` and `w ≠ 0` with
`φ w = 0` on a finite-dimensional `V`, there are a functional `ψ` on `ker φ` and an equivalence
`V ≃ k × (k × ker ψ)` in which `φ` is the first coordinate and `w` is `(0, (1, 0))`; and
`dim ker ψ + 2 = dim V`. -/
theorem exists_equiv_normalForm [FiniteDimensional k V] {φ : V →ₗ[k] k} {w : V} (hφ : φ ≠ 0)
    (hw : w ≠ 0) (h : φ w = 0) :
    ∃ (ψ : ker φ →ₗ[k] k) (e : V ≃ₗ[k] k × (k × ker ψ)),
      finrank k (ker ψ) + 2 = finrank k V ∧ (∀ v, (e v).1 = φ v) ∧ e w = (0, (1, 0)) := by
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, φ v₀ = 1 := by
    obtain ⟨v, hv⟩ : ∃ v, φ v ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hφ (LinearMap.ext hc)
    exact ⟨(φ v)⁻¹ • v, by simp [hv]⟩
  set wK : ker φ := ⟨w, h⟩
  have hwK : wK ≠ 0 := fun h0 => hw (congrArg Subtype.val h0)
  obtain ⟨ψ, hψ⟩ := Module.Projective.exists_dual_eq_one k hwK
  have hψ0 : ψ ≠ 0 := fun h0 => by simp [h0] at hψ
  refine ⟨ψ, (equivProdKer φ v₀ hv₀).trans
    ((LinearEquiv.refl k k).prodCongr (equivProdKer ψ wK hψ)), ?_, fun v => rfl, ?_⟩
  · have h1 := Module.Dual.finrank_ker_add_one_of_ne_zero hφ
    have h2 := Module.Dual.finrank_ker_add_one_of_ne_zero hψ0
    omega
  · rw [LinearEquiv.trans_apply, equivProdKer_apply_of_mem_ker φ v₀ hv₀ h,
      LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply]
    change ((0 : k), equivProdKer ψ wK hψ wK) = (0, (1, 0))
    rw [equivProdKer_apply_self]

/-- **The orbit lemma.** For nonzero functionals `φ`, `φ'` and nonzero vectors `w`, `w'` they kill,
on spaces of the same finite dimension, some linear equivalence `e : V ≃ V'` has `φ' ∘ e = φ` and
`e w = w'`. For `V = V'` this says that `GL(V)` acts transitively on such pairs. -/
theorem exists_linearEquiv_of_apply_eq_zero [FiniteDimensional k V] [FiniteDimensional k V']
    (hdim : finrank k V = finrank k V') {φ : V →ₗ[k] k} {w : V} {φ' : V' →ₗ[k] k} {w' : V'}
    (hφ : φ ≠ 0) (hw : w ≠ 0) (h : φ w = 0) (hφ' : φ' ≠ 0) (hw' : w' ≠ 0) (h' : φ' w' = 0) :
    ∃ e : V ≃ₗ[k] V', (∀ v, φ' (e v) = φ v) ∧ e w = w' := by
  obtain ⟨ψ, e, hd, he₁, hew⟩ := exists_equiv_normalForm hφ hw h
  obtain ⟨ψ', e', hd', he₁', hew'⟩ := exists_equiv_normalForm hφ' hw' h'
  let F : ker ψ ≃ₗ[k] ker ψ' := LinearEquiv.ofFinrankEq _ _ (by omega)
  let G : (k × (k × ker ψ)) ≃ₗ[k] (k × (k × ker ψ')) :=
    (LinearEquiv.refl k k).prodCongr ((LinearEquiv.refl k k).prodCongr F)
  refine ⟨e.trans (G.trans e'.symm), fun v => ?_, ?_⟩
  · rw [← he₁', LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
      ← he₁]
    rfl
  · rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hew, LinearEquiv.symm_apply_eq, hew']
    simp [G]

end LinearMap
