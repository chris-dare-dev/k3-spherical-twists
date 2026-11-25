/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.RepresentationTheory.Quiver.Kronecker.Preprojective
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Trace

/-!
# Extensions of preprojective representations

For representations `X` on `V₀, V₁` and `Y` on `W₀, W₁` of the doubled Kronecker quiver, `Ext` is
computed by the standard three-term complex of the preprojective algebra,

  `⊕_v Hom(X_v, Y_v) → ⊕_a Hom(X_{t(a)}, Y_{h(a)}) → ⊕_v Hom(X_v, Y_v)`,

whose first map is `h ↦ (Y_a h - h X_a)_a` and whose second map is the derivative of the
preprojective relations `∑ B_i A_i` and `∑ A_i B_i`. Here `Ext¹(X, Y)` is *defined* as the
one-cocycles of this complex modulo the one-coboundaries. Its kernel in degree zero is `Hom(X, Y)`,
and the one-cocycles of `(B, A)` are exactly the classes of the extensions `0 → A → N → B → 0`.

## Main definitions

* `d₀₁`, `d₁₂`, `cocycles₁`, `coboundaries₁`, `Ext1`: the complex and `Ext¹`, named as Mathlib's
  low-degree group cohomology;
* `map₀`, `map₁`, `postcomp`, `precomp`: composition of cochains with morphisms;
* `extension A B ξ`: the representation on `V₀ × W₀`, `V₁ × W₁` with block upper triangular arrows
  `[[A_a, ξ_a], [0, B_a]]`; `extensionIso` the isomorphism `[[α, h], [0, β]]` of two extensions;
* `orbitTangent A B ξ`: `End(A) ξ + ξ End(B)` plus the coboundaries, the tangent space at `ξ` to
  the orbit of `Aut(A) × Aut(B)`; `orbitSpan A B ξ` is its image in `Ext¹(B, A)`;
* `extQuotPushPull`: the map `Ext¹(B, A)/(End(A) ξ + ξ End(B)) → Ext¹(N, N)` induced by
  `v ↦ i ∘ v ∘ p`, for `i : A → N` the inclusion and `p : N → B` the projection.

## Main results

* `ker_d₀₁`: `H⁰ = Hom(X, Y)`;
* `isPreprojective_extension_iff`, `offDiag_mem_cocycles₁`, `exists_iso_extension`: an extension
  of representations is a cocycle placed in the off-diagonal block, and a subrepresentation `P`
  presents `M` as an extension of `M ⧸ P` by `P` (and `P ≤ Q` present `M|Q` as an extension of
  `Q / P` by `M|P`, `exists_iso_extension_of_le`); `extensionIso`: extensions whose classes are
  related by isomorphisms of their ends, cohomologous classes in particular, are isomorphic;
* `extQuotPushPull_injective`: **the injection** `Ext¹(B, A)/(End(A) ξ + ξ End(B)) ↪ Ext¹(N, N)`
  when `Hom(A, B) = 0`; `orbitSpan_eq_top`, `cocycles₁_le_orbitTangent`: if moreover `N` is
  rigid, then `Ext¹(B, A) = End(A) ξ + ξ End(B)`;
* `finrank_Ext1`: `dim Ext¹(X, Y) = dim Hom(X, Y) + dim Hom(Y, X) - (x, y)` for representations
  with the relations, `(x, y) = 2 x₀ y₀ + 2 x₁ y₁ - g (x₀ y₁ + x₁ y₀)` the symmetric Euler form of
  the `g`-Kronecker quiver (Crawley-Boevey, *On the exceptional fibres of Kleinian singularities*,
  Amer. J. Math. 122 (2000), Lemma 1). The proof is the duality of the two differentials under the
  trace pairing (`dualMap_d₀₁_comp_tracePairing₁`). With `X = Y` it reads
  `e(X) = 2 dim End X - 2 q(x)`, `q(x) = x₀² + x₁² - g x₀ x₁`, the Riemann–Roch identity
  `e = 2 dim End + v²` of the wall;
* `finrank_Ext1_extension`: **Mukai's inequality with its defect.** For an extension `N` of `B` by
  `A` with `Hom(A, B) = 0`,
  `dim Ext¹(N, N) = dim Ext¹(A, A) + dim Ext¹(B, B) + 2 dim Ext¹(B, A)/(End(A) ξ + ξ End(B))`;
  so `e(A) + e(B) ≤ e(N)` (`finrank_Ext1_add_le`, Bayer–Bridgeland, arXiv:1310.8266, Lemma 2.5)
  and a rigid `N` has rigid `A` and `B` (`rigid_of_rigid_extension`).

## Compared with the draft

The proposition on rigid wall groups proves the injection in the derived category: if `i v p`
vanishes, exactness gives `v p = ξ f` for some `f : N → B`, orthogonality gives `f = b p`, and
exactness once more gives `v - ξ b = a ξ`. Here the same argument is a computation with the four
blocks of a zero-cochain `H` of `N` with `d₀₁ H = i v p` (`exists_blockMap_of_d₀₁_eq`): the block
`A → B` is a morphism, hence zero; the diagonal blocks are endomorphisms `a` of `A` and `b` of `B`;
the corner gives `v = ξ b - a ξ + d₀₁ h`. The same block computation identifies `End(N)` with the
kernel of `(a, b, h) ↦ a ξ - ξ b - d₀₁ h` (`finrank_Hom_extension`), which with the dimension
formula gives Mukai's equality: it is stronger than the injection, which only bounds
`dim Ext¹(B, A)/(End(A) ξ + ξ End(B))` by `e(N)`. Everything here holds over any field.

## Implementation notes

The cochains are pairs: a zero-cochain is a pair `(h₀, h₁)` of maps at the two vertices, and a
one-cochain a pair of families indexed by the arrows `a_i : 0 → 1` and `b_i : 1 → 0`, as
`(ι → V₀ →ₗ[k] W₁) × (ι → V₁ →ₗ[k] W₀)`. An extension lives on the products `V₀ × W₀`,
`V₁ × W₁`, with `A` the first factor.
-/

namespace Quiver.Kronecker.DoubledRep

open Module

variable {k ι : Type*} [Field k]
  {V₀ V₁ W₀ W₁ : Type*} [AddCommGroup V₀] [Module k V₀] [AddCommGroup V₁] [Module k V₁]
  [AddCommGroup W₀] [Module k W₀] [AddCommGroup W₁] [Module k W₁]

/-! ### The standard complex -/

section Complex

variable (X : DoubledRep k ι V₀ V₁) (Y : DoubledRep k ι W₀ W₁)

/-- The degree-zero differential of the complex computing `Ext(X, Y)`: a pair `h = (h₀, h₁)` of
maps `X_v → Y_v` goes to `(Y_a h - h X_a)_a`, that is `Y.A i ∘ h₀ - h₁ ∘ X.A i` at the arrow
`a_i : 0 → 1` and `Y.B i ∘ h₁ - h₀ ∘ X.B i` at the arrow `b_i : 1 → 0`. -/
def d₀₁ : ((V₀ →ₗ[k] W₀) × (V₁ →ₗ[k] W₁)) →ₗ[k] (ι → V₀ →ₗ[k] W₁) × (ι → V₁ →ₗ[k] W₀) where
  toFun h := (fun i ↦ Y.A i ∘ₗ h.1 - h.2 ∘ₗ X.A i, fun i ↦ Y.B i ∘ₗ h.2 - h.1 ∘ₗ X.B i)
  map_add' h h' := by
    refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_) <;>
    · simp only [Prod.fst_add, Prod.snd_add, LinearMap.comp_add, LinearMap.add_comp,
        Pi.add_apply]
      abel
  map_smul' c h := by
    refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_) <;>
    · simp only [Prod.smul_fst, Prod.smul_snd, LinearMap.comp_smul, LinearMap.smul_comp,
        Pi.smul_apply, RingHom.id_apply, smul_sub]

@[simp]
lemma d₀₁_apply_fst (h : (V₀ →ₗ[k] W₀) × (V₁ →ₗ[k] W₁)) (i : ι) :
    (d₀₁ X Y h).1 i = Y.A i ∘ₗ h.1 - h.2 ∘ₗ X.A i := rfl

@[simp]
lemma d₀₁_apply_snd (h : (V₀ →ₗ[k] W₀) × (V₁ →ₗ[k] W₁)) (i : ι) :
    (d₀₁ X Y h).2 i = Y.B i ∘ₗ h.2 - h.1 ∘ₗ X.B i := rfl

/-- `H⁰` of the complex is `Hom(X, Y)`: `d₀₁ h = 0` says that `h` commutes with every arrow. -/
theorem ker_d₀₁ : LinearMap.ker (d₀₁ X Y) = Hom X Y := by
  ext h
  simp only [LinearMap.mem_ker, mem_Hom, Prod.ext_iff, funext_iff, d₀₁_apply_fst,
    d₀₁_apply_snd, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, sub_eq_zero]
  exact ⟨fun h i ↦ ⟨(h.1 i).symm, (h.2 i).symm⟩,
    fun h ↦ ⟨fun i ↦ (h i).1.symm, fun i ↦ (h i).2.symm⟩⟩

variable [Fintype ι]

/-- The degree-one differential, the linearized preprojective relations: a family `f` of maps
`f_{a_i} : X₀ → Y₁` and `f_{b_i} : X₁ → Y₀` goes to
`(∑ (Y.B i ∘ f_{a_i} + f_{b_i} ∘ X.A i), ∑ (Y.A i ∘ f_{b_i} + f_{a_i} ∘ X.B i))`, the derivative
of the relations `∑ B_i A_i` and `∑ A_i B_i` in the direction `f`. -/
def d₁₂ : ((ι → V₀ →ₗ[k] W₁) × (ι → V₁ →ₗ[k] W₀)) →ₗ[k] (V₀ →ₗ[k] W₀) × (V₁ →ₗ[k] W₁) where
  toFun f := (∑ i, (Y.B i ∘ₗ f.1 i + f.2 i ∘ₗ X.A i), ∑ i, (Y.A i ∘ₗ f.2 i + f.1 i ∘ₗ X.B i))
  map_add' f f' := by
    refine Prod.ext ?_ ?_ <;>
    · simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, LinearMap.comp_add, LinearMap.add_comp,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by abel
  map_smul' c f := by
    refine Prod.ext ?_ ?_ <;>
    · simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, LinearMap.comp_smul,
        LinearMap.smul_comp, ← smul_add, ← Finset.smul_sum, RingHom.id_apply]

@[simp]
lemma d₁₂_apply_fst (f : (ι → V₀ →ₗ[k] W₁) × (ι → V₁ →ₗ[k] W₀)) :
    (d₁₂ X Y f).1 = ∑ i, (Y.B i ∘ₗ f.1 i + f.2 i ∘ₗ X.A i) := rfl

@[simp]
lemma d₁₂_apply_snd (f : (ι → V₀ →ₗ[k] W₁) × (ι → V₁ →ₗ[k] W₀)) :
    (d₁₂ X Y f).2 = ∑ i, (Y.A i ∘ₗ f.2 i + f.1 i ∘ₗ X.B i) := rfl

variable {X Y} in
/-- The square of the differential vanishes when both representations satisfy the relations. -/
theorem d₁₂_comp_d₀₁ (hX : X.IsPreprojective) (hY : Y.IsPreprojective) :
    d₁₂ X Y ∘ₗ d₀₁ X Y = 0 := by
  refine LinearMap.ext fun h ↦ Prod.ext (LinearMap.ext fun x ↦ ?_) (LinearMap.ext fun x ↦ ?_)
  · have hY' := LinearMap.congr_fun hY.1 (h.1 x)
    have hX' := congrArg h.1 (LinearMap.congr_fun hX.1 x)
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.zero_apply, map_sum,
      map_zero] at hY' hX'
    simp only [LinearMap.comp_apply, d₁₂_apply_fst, d₀₁_apply_fst, d₀₁_apply_snd,
      LinearMap.sum_apply, LinearMap.add_apply, LinearMap.sub_apply, map_sub,
      LinearMap.zero_apply, Prod.fst_zero]
    calc _ = ∑ i, (Y.B i (Y.A i (h.1 x)) - h.1 (X.B i (X.A i x))) :=
          Finset.sum_congr rfl fun i _ ↦ by abel
      _ = 0 := by rw [Finset.sum_sub_distrib, hY', hX', sub_zero]
  · have hY' := LinearMap.congr_fun hY.2 (h.2 x)
    have hX' := congrArg h.2 (LinearMap.congr_fun hX.2 x)
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.zero_apply, map_sum,
      map_zero] at hY' hX'
    simp only [LinearMap.comp_apply, d₁₂_apply_snd, d₀₁_apply_fst, d₀₁_apply_snd,
      LinearMap.sum_apply, LinearMap.add_apply, LinearMap.sub_apply, map_sub,
      LinearMap.zero_apply, Prod.snd_zero]
    calc _ = ∑ i, (Y.A i (Y.B i (h.2 x)) - h.2 (X.A i (X.B i x))) :=
          Finset.sum_congr rfl fun i _ ↦ by abel
      _ = 0 := by rw [Finset.sum_sub_distrib, hY', hX', sub_zero]

/-- The one-cocycles `Z¹(X, Y)`, the kernel of `d₁₂`. By `isPreprojective_extension_iff` they are
the classes `ξ` for which the block upper triangular arrows `[[Y_a, ξ_a], [0, X_a]]` satisfy the
preprojective relations. -/
def cocycles₁ : Submodule k ((ι → V₀ →ₗ[k] W₁) × (ι → V₁ →ₗ[k] W₀)) :=
  LinearMap.ker (d₁₂ X Y)

/-- The one-coboundaries `B¹(X, Y)`, the range of `d₀₁`. -/
def coboundaries₁ : Submodule k ((ι → V₀ →ₗ[k] W₁) × (ι → V₁ →ₗ[k] W₀)) :=
  LinearMap.range (d₀₁ X Y)

variable {X Y} in
lemma coboundaries₁_le_cocycles₁ (hX : X.IsPreprojective) (hY : Y.IsPreprojective) :
    coboundaries₁ X Y ≤ cocycles₁ X Y := by
  rintro _ ⟨h, rfl⟩
  exact LinearMap.congr_fun (d₁₂_comp_d₀₁ hX hY) h

/-- `Ext¹(X, Y)`: the one-cocycles modulo the one-coboundaries. -/
abbrev Ext1 := cocycles₁ X Y ⧸ (coboundaries₁ X Y).comap (cocycles₁ X Y).subtype

/-- `Ext¹(X, Y)` vanishes exactly when every one-cocycle is a coboundary. -/
theorem subsingleton_Ext1_iff : Subsingleton (Ext1 X Y) ↔ cocycles₁ X Y ≤ coboundaries₁ X Y := by
  rw [Submodule.Quotient.subsingleton_iff, Submodule.comap_subtype_eq_top]

end Complex

@[simp]
lemma mem_cocycles₁ {X : DoubledRep k ι V₀ V₁} {Y : DoubledRep k ι W₀ W₁} [Fintype ι]
    {c : (ι → V₀ →ₗ[k] W₁) × (ι → V₁ →ₗ[k] W₀)} : c ∈ cocycles₁ X Y ↔ d₁₂ X Y c = 0 :=
  LinearMap.mem_ker

lemma mem_coboundaries₁ {X : DoubledRep k ι V₀ V₁} {Y : DoubledRep k ι W₀ W₁}
    {c : (ι → V₀ →ₗ[k] W₁) × (ι → V₁ →ₗ[k] W₀)} :
    c ∈ coboundaries₁ X Y ↔ ∃ h, d₀₁ X Y h = c :=
  LinearMap.mem_range

/-! ### Composition with morphisms -/

section Functoriality

variable {V₀' V₁' W₀' W₁' : Type*} [AddCommGroup V₀'] [Module k V₀'] [AddCommGroup V₁']
  [Module k V₁'] [AddCommGroup W₀'] [Module k W₀'] [AddCommGroup W₁'] [Module k W₁']

/-- Composition on both sides of a zero-cochain: `h ↦ w ∘ h ∘ f` at each vertex. -/
def map₀ (f : (V₀' →ₗ[k] V₀) × (V₁' →ₗ[k] V₁)) (w : (W₀ →ₗ[k] W₀') × (W₁ →ₗ[k] W₁')) :
    ((V₀ →ₗ[k] W₀) × (V₁ →ₗ[k] W₁)) →ₗ[k] (V₀' →ₗ[k] W₀') × (V₁' →ₗ[k] W₁') where
  toFun h := (w.1 ∘ₗ h.1 ∘ₗ f.1, w.2 ∘ₗ h.2 ∘ₗ f.2)
  map_add' h h' := by
    simp only [Prod.fst_add, Prod.snd_add, LinearMap.add_comp, LinearMap.comp_add, Prod.mk_add_mk]
  map_smul' c h := by
    simp only [Prod.smul_fst, Prod.smul_snd, LinearMap.smul_comp, LinearMap.comp_smul,
      RingHom.id_apply, Prod.smul_mk]

@[simp]
lemma map₀_apply (f : (V₀' →ₗ[k] V₀) × (V₁' →ₗ[k] V₁)) (w : (W₀ →ₗ[k] W₀') × (W₁ →ₗ[k] W₁'))
    (h : (V₀ →ₗ[k] W₀) × (V₁ →ₗ[k] W₁)) :
    map₀ f w h = (w.1 ∘ₗ h.1 ∘ₗ f.1, w.2 ∘ₗ h.2 ∘ₗ f.2) := rfl

/-- Composition on both sides of a one-cochain: `c ↦ w ∘ c ∘ f` at each arrow. -/
def map₁ (f : (V₀' →ₗ[k] V₀) × (V₁' →ₗ[k] V₁)) (w : (W₀ →ₗ[k] W₀') × (W₁ →ₗ[k] W₁')) :
    ((ι → V₀ →ₗ[k] W₁) × (ι → V₁ →ₗ[k] W₀)) →ₗ[k]
      (ι → V₀' →ₗ[k] W₁') × (ι → V₁' →ₗ[k] W₀') where
  toFun c := (fun i ↦ w.2 ∘ₗ c.1 i ∘ₗ f.1, fun i ↦ w.1 ∘ₗ c.2 i ∘ₗ f.2)
  map_add' c c' := by
    refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_) <;>
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, LinearMap.add_comp, LinearMap.comp_add]
  map_smul' a c := by
    refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_) <;>
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, LinearMap.smul_comp,
      LinearMap.comp_smul, RingHom.id_apply]

@[simp]
lemma map₁_apply_fst (f : (V₀' →ₗ[k] V₀) × (V₁' →ₗ[k] V₁))
    (w : (W₀ →ₗ[k] W₀') × (W₁ →ₗ[k] W₁')) (c : (ι → V₀ →ₗ[k] W₁) × (ι → V₁ →ₗ[k] W₀))
    (i : ι) : (map₁ f w c).1 i = w.2 ∘ₗ c.1 i ∘ₗ f.1 := rfl

@[simp]
lemma map₁_apply_snd (f : (V₀' →ₗ[k] V₀) × (V₁' →ₗ[k] V₁))
    (w : (W₀ →ₗ[k] W₀') × (W₁ →ₗ[k] W₁')) (c : (ι → V₀ →ₗ[k] W₁) × (ι → V₁ →ₗ[k] W₀))
    (i : ι) : (map₁ f w c).2 i = w.1 ∘ₗ c.2 i ∘ₗ f.2 := rfl

/-- Post-composition of a fixed one-cochain `ξ` with maps at the vertices, `a ↦ a ξ`. -/
def postcomp (ξ : (ι → V₀ →ₗ[k] W₁) × (ι → V₁ →ₗ[k] W₀)) :
    ((W₀ →ₗ[k] W₀') × (W₁ →ₗ[k] W₁')) →ₗ[k] (ι → V₀ →ₗ[k] W₁') × (ι → V₁ →ₗ[k] W₀') where
  toFun a := (fun i ↦ a.2 ∘ₗ ξ.1 i, fun i ↦ a.1 ∘ₗ ξ.2 i)
  map_add' a a' := by
    refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_) <;>
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, LinearMap.add_comp]
  map_smul' c a := by
    refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_) <;>
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, LinearMap.smul_comp, RingHom.id_apply]

@[simp]
lemma postcomp_apply_fst (ξ : (ι → V₀ →ₗ[k] W₁) × (ι → V₁ →ₗ[k] W₀))
    (a : (W₀ →ₗ[k] W₀') × (W₁ →ₗ[k] W₁')) (i : ι) : (postcomp ξ a).1 i = a.2 ∘ₗ ξ.1 i := rfl

@[simp]
lemma postcomp_apply_snd (ξ : (ι → V₀ →ₗ[k] W₁) × (ι → V₁ →ₗ[k] W₀))
    (a : (W₀ →ₗ[k] W₀') × (W₁ →ₗ[k] W₁')) (i : ι) : (postcomp ξ a).2 i = a.1 ∘ₗ ξ.2 i := rfl

/-- Pre-composition of a fixed one-cochain `ξ` with maps at the vertices, `b ↦ ξ b`. -/
def precomp (ξ : (ι → V₀ →ₗ[k] W₁) × (ι → V₁ →ₗ[k] W₀)) :
    ((V₀' →ₗ[k] V₀) × (V₁' →ₗ[k] V₁)) →ₗ[k] (ι → V₀' →ₗ[k] W₁) × (ι → V₁' →ₗ[k] W₀) where
  toFun b := (fun i ↦ ξ.1 i ∘ₗ b.1, fun i ↦ ξ.2 i ∘ₗ b.2)
  map_add' b b' := by
    refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_) <;>
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, LinearMap.comp_add]
  map_smul' c b := by
    refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_) <;>
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, LinearMap.comp_smul, RingHom.id_apply]

@[simp]
lemma precomp_apply_fst (ξ : (ι → V₀ →ₗ[k] W₁) × (ι → V₁ →ₗ[k] W₀))
    (b : (V₀' →ₗ[k] V₀) × (V₁' →ₗ[k] V₁)) (i : ι) : (precomp ξ b).1 i = ξ.1 i ∘ₗ b.1 := rfl

@[simp]
lemma precomp_apply_snd (ξ : (ι → V₀ →ₗ[k] W₁) × (ι → V₁ →ₗ[k] W₀))
    (b : (V₀' →ₗ[k] V₀) × (V₁' →ₗ[k] V₁)) (i : ι) : (precomp ξ b).2 i = ξ.2 i ∘ₗ b.2 := rfl

variable {X : DoubledRep k ι V₀ V₁} {Y : DoubledRep k ι W₀ W₁} {X' : DoubledRep k ι V₀' V₁'}
  {Y' : DoubledRep k ι W₀' W₁'} {f : (V₀' →ₗ[k] V₀) × (V₁' →ₗ[k] V₁)}
  {w : (W₀ →ₗ[k] W₀') × (W₁ →ₗ[k] W₁')}

/-- Composition with morphisms commutes with the degree-zero differential. -/
theorem d₀₁_map₀ (hf : f ∈ Hom X' X) (hw : w ∈ Hom Y Y') (h : (V₀ →ₗ[k] W₀) × (V₁ →ₗ[k] W₁)) :
    d₀₁ X' Y' (map₀ f w h) = map₁ f w (d₀₁ X Y h) := by
  have hw₁ : ∀ i y, w.2 (Y.A i y) = Y'.A i (w.1 y) := fun i ↦ LinearMap.congr_fun (hw i).1
  have hw₂ : ∀ i y, w.1 (Y.B i y) = Y'.B i (w.2 y) := fun i ↦ LinearMap.congr_fun (hw i).2
  have hf₁ : ∀ i x, f.2 (X'.A i x) = X.A i (f.1 x) := fun i ↦ LinearMap.congr_fun (hf i).1
  have hf₂ : ∀ i x, f.1 (X'.B i x) = X.B i (f.2 x) := fun i ↦ LinearMap.congr_fun (hf i).2
  refine Prod.ext (funext fun i ↦ LinearMap.ext fun x ↦ ?_)
    (funext fun i ↦ LinearMap.ext fun x ↦ ?_) <;>
  simp only [d₀₁_apply_fst, d₀₁_apply_snd, map₀_apply, map₁_apply_fst, map₁_apply_snd,
    LinearMap.sub_apply, LinearMap.comp_apply, map_sub, hw₁, hw₂, hf₁, hf₂]

/-- Composition with morphisms commutes with the degree-one differential. -/
theorem d₁₂_map₁ [Fintype ι] (hf : f ∈ Hom X' X) (hw : w ∈ Hom Y Y')
    (c : (ι → V₀ →ₗ[k] W₁) × (ι → V₁ →ₗ[k] W₀)) :
    d₁₂ X' Y' (map₁ f w c) = map₀ f w (d₁₂ X Y c) := by
  have hw₁ : ∀ i y, Y'.A i (w.1 y) = w.2 (Y.A i y) := fun i y ↦
    (LinearMap.congr_fun (hw i).1 y).symm
  have hw₂ : ∀ i y, Y'.B i (w.2 y) = w.1 (Y.B i y) := fun i y ↦
    (LinearMap.congr_fun (hw i).2 y).symm
  have hf₁ : ∀ i x, f.2 (X'.A i x) = X.A i (f.1 x) := fun i ↦ LinearMap.congr_fun (hf i).1
  have hf₂ : ∀ i x, f.1 (X'.B i x) = X.B i (f.2 x) := fun i ↦ LinearMap.congr_fun (hf i).2
  refine Prod.ext (LinearMap.ext fun x ↦ ?_) (LinearMap.ext fun x ↦ ?_) <;>
  simp only [d₁₂_apply_fst, d₁₂_apply_snd, map₀_apply, map₁_apply_fst, map₁_apply_snd,
    LinearMap.sum_apply, LinearMap.add_apply, LinearMap.comp_apply, map_sum, map_add, hw₁, hw₂,
    hf₁, hf₂]

lemma map₁_mem_cocycles₁ [Fintype ι] (hf : f ∈ Hom X' X) (hw : w ∈ Hom Y Y')
    {c : (ι → V₀ →ₗ[k] W₁) × (ι → V₁ →ₗ[k] W₀)} (hc : c ∈ cocycles₁ X Y) :
    map₁ f w c ∈ cocycles₁ X' Y' := by
  rw [mem_cocycles₁] at hc ⊢
  rw [d₁₂_map₁ hf hw, hc, map_zero]

lemma map₁_mem_coboundaries₁ (hf : f ∈ Hom X' X) (hw : w ∈ Hom Y Y')
    {c : (ι → V₀ →ₗ[k] W₁) × (ι → V₁ →ₗ[k] W₀)} (hc : c ∈ coboundaries₁ X Y) :
    map₁ f w c ∈ coboundaries₁ X' Y' := by
  obtain ⟨h, rfl⟩ := hc
  exact ⟨map₀ f w h, d₀₁_map₀ hf hw h⟩

end Functoriality

/-! ### Extensions -/

section Triangular

variable {V W V' W' : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup V'] [Module k V'] [AddCommGroup W'] [Module k W']

/-- The block upper triangular map `[[P, Q], [0, R]] : V × W → V' × W'`,
`(x, y) ↦ (P x + Q y, R y)`. -/
def triangular (P : V →ₗ[k] V') (Q : W →ₗ[k] V') (R : W →ₗ[k] W') : V × W →ₗ[k] V' × W' :=
  (P.coprod Q).prod (R ∘ₗ LinearMap.snd k V W)

@[simp]
lemma triangular_apply (P : V →ₗ[k] V') (Q : W →ₗ[k] V') (R : W →ₗ[k] W') (x : V × W) :
    triangular P Q R x = (P x.1 + Q x.2, R x.2) := rfl

/-- `[[P, Q], [0, R]]` with `P`, `R` invertible is invertible, with inverse
`[[P⁻¹, -P⁻¹ Q R⁻¹], [0, R⁻¹]]`. -/
def triangularEquiv (P : V ≃ₗ[k] V') (Q : W →ₗ[k] V') (R : W ≃ₗ[k] W') : (V × W) ≃ₗ[k] V' × W' :=
  .ofLinearMap (triangular P Q R)
    (triangular P.symm (-((P.symm : V' →ₗ[k] V) ∘ₗ Q ∘ₗ (R.symm : W' →ₗ[k] W))) R.symm)
    (LinearMap.ext fun x ↦ by simp)
    (LinearMap.ext fun x ↦ by simp)

@[simp]
lemma triangularEquiv_apply (P : V ≃ₗ[k] V') (Q : W →ₗ[k] V') (R : W ≃ₗ[k] W') (x : V × W) :
    triangularEquiv P Q R x = (P x.1 + Q x.2, R x.2) := rfl

end Triangular

section Extension

variable (A : DoubledRep k ι V₀ V₁) (B : DoubledRep k ι W₀ W₁)

/-- The extension of `B` by `A` with class `ξ`: the representation on `V₀ × W₀` and `V₁ × W₁`
with block upper triangular arrows `[[A_a, ξ_a], [0, B_a]]`. -/
def extension (ξ : (ι → W₀ →ₗ[k] V₁) × (ι → W₁ →ₗ[k] V₀)) :
    DoubledRep k ι (V₀ × W₀) (V₁ × W₁) where
  A i := triangular (A.A i) (ξ.1 i) (B.A i)
  B i := triangular (A.B i) (ξ.2 i) (B.B i)

variable (ξ : (ι → W₀ →ₗ[k] V₁) × (ι → W₁ →ₗ[k] V₀))

@[simp]
lemma extension_A_apply (i : ι) (x : V₀ × W₀) :
    (extension A B ξ).A i x = (A.A i x.1 + ξ.1 i x.2, B.A i x.2) := rfl

@[simp]
lemma extension_B_apply (i : ι) (x : V₁ × W₁) :
    (extension A B ξ).B i x = (A.B i x.1 + ξ.2 i x.2, B.B i x.2) := rfl

/-- The inclusion `A → N` of the extension is a morphism. -/
lemma inl_mem_Hom :
    (LinearMap.inl k V₀ W₀, LinearMap.inl k V₁ W₁) ∈ Hom A (extension A B ξ) := fun i ↦
  ⟨LinearMap.ext fun x ↦ by simp, LinearMap.ext fun y ↦ by simp⟩

/-- The projection `N → B` of the extension is a morphism. -/
lemma snd_mem_Hom :
    (LinearMap.snd k V₀ W₀, LinearMap.snd k V₁ W₁) ∈ Hom (extension A B ξ) B := fun i ↦
  ⟨LinearMap.ext fun x ↦ by simp, LinearMap.ext fun y ↦ by simp⟩

variable [Fintype ι]

/-- The relation at vertex zero of the extension: its diagonal blocks are the relations of `A`
and `B`, its off-diagonal block is the vertex-zero component of `d₁₂ ξ`. -/
lemma extension_relation_zero (x : V₀ × W₀) :
    (∑ i, (extension A B ξ).B i ∘ₗ (extension A B ξ).A i) x =
      ((∑ i, A.B i ∘ₗ A.A i) x.1 + (d₁₂ B A ξ).1 x.2, (∑ i, B.B i ∘ₗ B.A i) x.2) := by
  refine Prod.ext ?_ ?_
  · simp only [LinearMap.sum_apply, LinearMap.comp_apply, extension_A_apply, extension_B_apply,
      Prod.fst_sum, d₁₂_apply_fst, LinearMap.add_apply, map_add, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by abel
  · simp only [LinearMap.sum_apply, LinearMap.comp_apply, extension_A_apply, extension_B_apply,
      Prod.snd_sum]

/-- The relation at vertex one of the extension. -/
lemma extension_relation_one (x : V₁ × W₁) :
    (∑ i, (extension A B ξ).A i ∘ₗ (extension A B ξ).B i) x =
      ((∑ i, A.A i ∘ₗ A.B i) x.1 + (d₁₂ B A ξ).2 x.2, (∑ i, B.A i ∘ₗ B.B i) x.2) := by
  refine Prod.ext ?_ ?_
  · simp only [LinearMap.sum_apply, LinearMap.comp_apply, extension_A_apply, extension_B_apply,
      Prod.fst_sum, d₁₂_apply_snd, LinearMap.add_apply, map_add, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by abel
  · simp only [LinearMap.sum_apply, LinearMap.comp_apply, extension_A_apply, extension_B_apply,
      Prod.snd_sum]

/-- **An extension satisfies the preprojective relations exactly when `A` and `B` do and its
class is a cocycle.** -/
theorem isPreprojective_extension_iff :
    (extension A B ξ).IsPreprojective ↔
      A.IsPreprojective ∧ B.IsPreprojective ∧ ξ ∈ cocycles₁ B A := by
  constructor
  · rintro ⟨h₀, h₁⟩
    have e₀ := fun x ↦ (extension_relation_zero A B ξ x).symm.trans (LinearMap.congr_fun h₀ x)
    have e₁ := fun x ↦ (extension_relation_one A B ξ x).symm.trans (LinearMap.congr_fun h₁ x)
    refine ⟨⟨LinearMap.ext fun x ↦ ?_, LinearMap.ext fun x ↦ ?_⟩,
      ⟨LinearMap.ext fun y ↦ ?_, LinearMap.ext fun y ↦ ?_⟩, ?_⟩
    · simpa using congrArg Prod.fst (e₀ (x, 0))
    · simpa using congrArg Prod.fst (e₁ (x, 0))
    · simpa using congrArg Prod.snd (e₀ (0, y))
    · simpa using congrArg Prod.snd (e₁ (0, y))
    · rw [mem_cocycles₁]
      refine Prod.ext (LinearMap.ext fun y ↦ ?_) (LinearMap.ext fun y ↦ ?_)
      · simpa using congrArg Prod.fst (e₀ (0, y))
      · simpa using congrArg Prod.fst (e₁ (0, y))
  · rintro ⟨hA, hB, hξ⟩
    rw [mem_cocycles₁] at hξ
    refine ⟨LinearMap.ext fun x ↦ ?_, LinearMap.ext fun x ↦ ?_⟩
    · rw [extension_relation_zero, hA.1, hB.1, hξ]
      simp
    · rw [extension_relation_one, hA.2, hB.2, hξ]
      simp

omit [Fintype ι] in
/-- The off-diagonal block of a representation on `V₀ × W₀` and `V₁ × W₁`. -/
def offDiag (N : DoubledRep k ι (V₀ × W₀) (V₁ × W₁)) : (ι → W₀ →ₗ[k] V₁) × (ι → W₁ →ₗ[k] V₀) :=
  (fun i ↦ LinearMap.fst k V₁ W₁ ∘ₗ N.A i ∘ₗ LinearMap.inr k V₀ W₀,
    fun i ↦ LinearMap.fst k V₀ W₀ ∘ₗ N.B i ∘ₗ LinearMap.inr k V₁ W₁)

omit [Fintype ι] in
/-- **An extension is block upper triangular.** If the inclusion of `A` and the projection to
`B` are morphisms, then `N = extension A B (offDiag N)`. -/
theorem eq_extension {N : DoubledRep k ι (V₀ × W₀) (V₁ × W₁)}
    (hi : (LinearMap.inl k V₀ W₀, LinearMap.inl k V₁ W₁) ∈ Hom A N)
    (hp : (LinearMap.snd k V₀ W₀, LinearMap.snd k V₁ W₁) ∈ Hom N B) :
    N = extension A B (offDiag N) := by
  refine DoubledRep.ext (funext fun i ↦ LinearMap.ext fun x ↦ ?_)
    (funext fun i ↦ LinearMap.ext fun x ↦ ?_)
  · have h1 := LinearMap.congr_fun (hi i).1 x.1
    have h2 := LinearMap.congr_fun (hp i).1 (0, x.2)
    simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.snd_apply] at h1 h2
    calc N.A i x = N.A i (x.1, 0) + N.A i (0, x.2) := by
          rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
      _ = _ := by
        refine Prod.ext ?_ ?_
        · simp [offDiag, ← h1]
        · simp [← h1, h2]
  · have h1 := LinearMap.congr_fun (hi i).2 x.1
    have h2 := LinearMap.congr_fun (hp i).2 (0, x.2)
    simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.snd_apply] at h1 h2
    calc N.B i x = N.B i (x.1, 0) + N.B i (0, x.2) := by
          rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
      _ = _ := by
        refine Prod.ext ?_ ?_
        · simp [offDiag, ← h1]
        · simp [← h1, h2]

/-- **An extension of representations is a cocycle in the off-diagonal block.** If `N` satisfies
the relations and is an extension of `B` by `A` (the inclusion of `A` and the projection to `B`
are morphisms), then its off-diagonal block is a one-cocycle of `(B, A)`. -/
theorem offDiag_mem_cocycles₁ {N : DoubledRep k ι (V₀ × W₀) (V₁ × W₁)}
    (hN : N.IsPreprojective)
    (hi : (LinearMap.inl k V₀ W₀, LinearMap.inl k V₁ W₁) ∈ Hom A N)
    (hp : (LinearMap.snd k V₀ W₀, LinearMap.snd k V₁ W₁) ∈ Hom N B) :
    offDiag N ∈ cocycles₁ B A := by
  rw [eq_extension A B hi hp] at hN
  exact ((isPreprojective_extension_iff A B _).mp hN).2.2

end Extension

/-! ### Isomorphisms of extensions -/

section ExtensionIso

variable {V₀' V₁' W₀' W₁' : Type*} [AddCommGroup V₀'] [Module k V₀'] [AddCommGroup V₁']
  [Module k V₁'] [AddCommGroup W₀'] [Module k W₀'] [AddCommGroup W₁'] [Module k W₁']
  {A : DoubledRep k ι V₀ V₁} {B : DoubledRep k ι W₀ W₁} {A' : DoubledRep k ι V₀' V₁'}
  {B' : DoubledRep k ι W₀' W₁'} {ξ : (ι → W₀ →ₗ[k] V₁) × (ι → W₁ →ₗ[k] V₀)}
  {ξ' : (ι → W₀' →ₗ[k] V₁') × (ι → W₁' →ₗ[k] V₀')}

/-- A block upper triangular pair `[[a, h], [0, b]]` is a morphism of extensions
`extension A B ξ → extension A' B' ξ'` when `a`, `b` are morphisms and `a ξ - ξ' b = d₀₁ h`. -/
theorem triangular_mem_Hom {a : (V₀ →ₗ[k] V₀') × (V₁ →ₗ[k] V₁')}
    {b : (W₀ →ₗ[k] W₀') × (W₁ →ₗ[k] W₁')} {h : (W₀ →ₗ[k] V₀') × (W₁ →ₗ[k] V₁')}
    (ha : a ∈ Hom A A') (hb : b ∈ Hom B B') (hrel : postcomp ξ a - precomp ξ' b = d₀₁ B A' h) :
    (triangular a.1 h.1 b.1, triangular a.2 h.2 b.2) ∈
      Hom (extension A B ξ) (extension A' B' ξ') := by
  have hr₁ : ∀ i y, a.2 (ξ.1 i y) + h.2 (B.A i y) = A'.A i (h.1 y) + ξ'.1 i (b.1 y) :=
    fun i y ↦ sub_eq_sub_iff_add_eq_add.mp (by
      simpa using LinearMap.congr_fun (congrFun (congrArg Prod.fst hrel) i) y)
  have hr₂ : ∀ i y, a.1 (ξ.2 i y) + h.1 (B.B i y) = A'.B i (h.2 y) + ξ'.2 i (b.2 y) :=
    fun i y ↦ sub_eq_sub_iff_add_eq_add.mp (by
      simpa using LinearMap.congr_fun (congrFun (congrArg Prod.snd hrel) i) y)
  have ha₁ : ∀ i x, a.2 (A.A i x) = A'.A i (a.1 x) := fun i ↦ LinearMap.congr_fun (ha i).1
  have ha₂ : ∀ i x, a.1 (A.B i x) = A'.B i (a.2 x) := fun i ↦ LinearMap.congr_fun (ha i).2
  have hb₁ : ∀ i x, b.2 (B.A i x) = B'.A i (b.1 x) := fun i ↦ LinearMap.congr_fun (hb i).1
  have hb₂ : ∀ i x, b.1 (B.B i x) = B'.B i (b.2 x) := fun i ↦ LinearMap.congr_fun (hb i).2
  refine fun i ↦ ⟨LinearMap.ext fun z ↦ Prod.ext ?_ ?_, LinearMap.ext fun z ↦ Prod.ext ?_ ?_⟩
  · simp only [LinearMap.comp_apply, extension_A_apply, triangular_apply, map_add, ha₁]
    rw [add_assoc, hr₁, add_assoc]
  · simp only [LinearMap.comp_apply, extension_A_apply, triangular_apply, hb₁]
  · simp only [LinearMap.comp_apply, extension_B_apply, triangular_apply, map_add, ha₂]
    rw [add_assoc, hr₂, add_assoc]
  · simp only [LinearMap.comp_apply, extension_B_apply, triangular_apply, hb₂]

/-- **Extensions related by isomorphisms of their ends are isomorphic.** If `α : A ≅ A'`,
`β : B ≅ B'` and `α ξ - ξ' β = d₀₁ h`, then `[[α, h], [0, β]]` is an isomorphism
`extension A B ξ ≅ extension A' B' ξ'`. With `A' = A`, `B' = B` and identities, cohomologous
cocycles give isomorphic extensions. -/
def extensionIso (α : Iso A A') (β : Iso B B') (h : (W₀ →ₗ[k] V₀') × (W₁ →ₗ[k] V₁'))
    (hrel : postcomp ξ ((α.e₀ : V₀ →ₗ[k] V₀'), (α.e₁ : V₁ →ₗ[k] V₁')) -
      precomp ξ' ((β.e₀ : W₀ →ₗ[k] W₀'), (β.e₁ : W₁ →ₗ[k] W₁')) = d₀₁ B A' h) :
    Iso (extension A B ξ) (extension A' B' ξ') where
  e₀ := triangularEquiv α.e₀ h.1 β.e₀
  e₁ := triangularEquiv α.e₁ h.2 β.e₁
  comm_A i z := LinearMap.congr_fun ((triangular_mem_Hom α.mem_Hom β.mem_Hom hrel i).1) z
  comm_B i z := LinearMap.congr_fun ((triangular_mem_Hom α.mem_Hom β.mem_Hom hrel i).2) z

/-- Transport of a class along isomorphisms `α : A ≅ A'` and `β : B ≅ B'`: `ξ ↦ α ξ β⁻¹`. -/
def transportClass (α : Iso A A') (β : Iso B B') (ξ : (ι → W₀ →ₗ[k] V₁) × (ι → W₁ →ₗ[k] V₀)) :
    (ι → W₀' →ₗ[k] V₁') × (ι → W₁' →ₗ[k] V₀') :=
  map₁ ((β.e₀.symm : W₀' →ₗ[k] W₀), (β.e₁.symm : W₁' →ₗ[k] W₁))
    ((α.e₀ : V₀ →ₗ[k] V₀'), (α.e₁ : V₁ →ₗ[k] V₁')) ξ

lemma transportClass_mem_cocycles₁ [Fintype ι] (α : Iso A A') (β : Iso B B')
    (hξ : ξ ∈ cocycles₁ B A) : transportClass α β ξ ∈ cocycles₁ B' A' :=
  map₁_mem_cocycles₁ β.symm.mem_Hom α.mem_Hom hξ

/-- The extension with the transported class is isomorphic to the original one. -/
def isoTransportClass (α : Iso A A') (β : Iso B B') :
    Iso (extension A B ξ) (extension A' B' (transportClass α β ξ)) :=
  extensionIso α β 0 (by
    refine Prod.ext (funext fun i ↦ LinearMap.ext fun y ↦ ?_)
      (funext fun i ↦ LinearMap.ext fun y ↦ ?_) <;>
    simp [transportClass])

/-- `Ext¹` of a representation with itself vanishes exactly when it does for an isomorphic
copy. -/
theorem Iso.subsingleton_Ext1 [Fintype ι] {X : DoubledRep k ι V₀ V₁}
    {X' : DoubledRep k ι V₀' V₁'} (u : Iso X X') (h : Subsingleton (Ext1 X X)) :
    Subsingleton (Ext1 X' X') := by
  rw [subsingleton_Ext1_iff] at h ⊢
  intro c hc
  have hc' := h (map₁_mem_cocycles₁ u.mem_Hom u.symm.mem_Hom hc)
  convert map₁_mem_coboundaries₁ u.symm.mem_Hom u.mem_Hom hc' using 1
  refine Prod.ext (funext fun i ↦ LinearMap.ext fun x ↦ ?_)
    (funext fun i ↦ LinearMap.ext fun x ↦ ?_) <;>
  simp [Iso.symm]

end ExtensionIso

/-! ### Subrepresentations as extensions -/

section Subrep

variable (M : DoubledRep k ι V₀ V₁) (P : M.subreps)

section Split

variable {V : Type*} [AddCommGroup V] [Module k V] (p q : Submodule k V) (h : IsCompl p q)

/-- The section `V ⧸ p → V` with image the complement `q`. -/
private noncomputable def quotSection : (V ⧸ p) →ₗ[k] V :=
  q.subtype ∘ₗ (p.quotientEquivOfIsCompl q h : V ⧸ p →ₗ[k] q)

private lemma mk_quotSection (z : V ⧸ p) :
    (Submodule.Quotient.mk (quotSection p q h z) : V ⧸ p) = z :=
  Submodule.mk_quotientEquivOfIsCompl_apply h z

private lemma projectionOnto_quotSection (z : V ⧸ p) :
    p.projectionOnto q h (quotSection p q h z) = 0 :=
  Submodule.projectionOnto_apply_right h _

private lemma projectionOnto_add_quotSection (x : V) :
    (p.projectionOnto q h x : V) + quotSection p q h (Submodule.Quotient.mk x) = x := by
  simp only [quotSection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Submodule.quotientEquivOfIsCompl_apply_mk, Submodule.subtype_apply,
    Submodule.coe_projectionOnto_apply]
  exact Submodule.projection_add_projection_eq_self h x

/-- A complement `q` of `p` identifies `V` with `p × V ⧸ p`, `x ↦ (π x, [x])`. -/
private noncomputable def splitEquiv : V ≃ₗ[k] p × (V ⧸ p) :=
  .ofLinearMap ((p.projectionOnto q h).prod p.mkQ) (p.subtype.coprod (quotSection p q h))
    (LinearMap.ext fun z ↦ Prod.ext (by simp [projectionOnto_quotSection])
      (by simp [(Submodule.Quotient.mk_eq_zero p).mpr z.1.2, mk_quotSection]))
    (LinearMap.ext fun x ↦ projectionOnto_add_quotSection p q h x)

private lemma splitEquiv_apply (x : V) :
    splitEquiv p q h x = (p.projectionOnto q h x, Submodule.Quotient.mk x) := rfl

end Split

/-- **An extension of representations is a cocycle in the off-diagonal block.** For a
subrepresentation `P` of `M`, complements of the subspaces of `P` identify `M` with the extension
of `M ⧸ P` by `P` whose class is `ξ_a = π ∘ M_a ∘ σ`, `π` the projection to `P` and `σ` the section
of `M → M ⧸ P` along the complements; the class is a cocycle when `M` satisfies the relations. -/
theorem exists_iso_extension [Fintype ι] (hM : M.IsPreprojective) :
    ∃ ξ ∈ cocycles₁ (M.quotient P) (M.restrict P),
      Nonempty (Iso M (extension (M.restrict P) (M.quotient P) ξ)) := by
  obtain ⟨C₀, h₀⟩ := (P : Submodule k V₀ × Submodule k V₁).1.exists_isCompl
  obtain ⟨C₁, h₁⟩ := (P : Submodule k V₀ × Submodule k V₁).2.exists_isCompl
  let ξ : (ι → V₀ ⧸ (P : Submodule k V₀ × Submodule k V₁).1 →ₗ[k]
      (P : Submodule k V₀ × Submodule k V₁).2) ×
      (ι → V₁ ⧸ (P : Submodule k V₀ × Submodule k V₁).2 →ₗ[k]
        (P : Submodule k V₀ × Submodule k V₁).1) :=
    (fun i ↦ (P : Submodule k V₀ × Submodule k V₁).2.projectionOnto C₁ h₁ ∘ₗ M.A i ∘ₗ
        quotSection _ C₀ h₀,
      fun i ↦ (P : Submodule k V₀ × Submodule k V₁).1.projectionOnto C₀ h₀ ∘ₗ M.B i ∘ₗ
        quotSection _ C₁ h₁)
  let u : Iso M (extension (M.restrict P) (M.quotient P) ξ) :=
    { e₀ := splitEquiv _ C₀ h₀
      e₁ := splitEquiv _ C₁ h₁
      comm_A := fun i x ↦ by
        refine Prod.ext ?_ rfl
        conv_lhs => rw [splitEquiv_apply, ← projectionOnto_add_quotSection _ C₀ h₀ x]
        rw [map_add, map_add, Submodule.projectionOnto_apply_of_mem_left h₁
          (A_mem P i (Submodule.projectionOnto _ C₀ h₀ x).2)]
        rfl
      comm_B := fun i y ↦ by
        refine Prod.ext ?_ rfl
        conv_lhs => rw [splitEquiv_apply, ← projectionOnto_add_quotSection _ C₁ h₁ y]
        rw [map_add, map_add, Submodule.projectionOnto_apply_of_mem_left h₀
          (B_mem P i (Submodule.projectionOnto _ C₁ h₁ y).2)]
        rfl }
  exact ⟨ξ, ((isPreprojective_extension_iff _ _ ξ).mp (u.isPreprojective hM)).2.2, ⟨u⟩⟩

end Subrep

/-- **Subrepresentations `P ≤ Q` present `M|Q` as an extension of `Q / P` by `M|P`.** -/
theorem exists_iso_extension_of_le [Fintype ι] {M : DoubledRep k ι V₀ V₁}
    (hM : M.IsPreprojective) {P Q : M.subreps} (h : P ≤ Q) :
    ∃ ξ ∈ cocycles₁ (M.subquotient P Q) (M.restrict P),
      Nonempty (Iso (M.restrict Q) (extension (M.restrict P) (M.subquotient P Q) ξ)) := by
  obtain ⟨ξ, hξ, ⟨u⟩⟩ := (M.restrict Q).exists_iso_extension (M.subrepOf P Q) (hM.restrict Q)
  exact ⟨_, transportClass_mem_cocycles₁ (restrictSubrepOfIso h) (Iso.refl _) hξ,
    ⟨u.trans (isoTransportClass _ _)⟩⟩

/-! ### The injection into `Ext¹(N, N)` -/

section Injection

/-- The map `v ↦ i ∘ v ∘ p` from one-cochains of `(B, A)` to one-cochains of the extension `N`,
`i` the inclusion of `A` and `p` the projection to `B`. -/
def pushPull : ((ι → W₀ →ₗ[k] V₁) × (ι → W₁ →ₗ[k] V₀)) →ₗ[k]
    (ι → V₀ × W₀ →ₗ[k] V₁ × W₁) × (ι → V₁ × W₁ →ₗ[k] V₀ × W₀) :=
  map₁ (LinearMap.snd k V₀ W₀, LinearMap.snd k V₁ W₁)
    (LinearMap.inl k V₀ W₀, LinearMap.inl k V₁ W₁)

@[simp]
lemma pushPull_apply_fst (v : (ι → W₀ →ₗ[k] V₁) × (ι → W₁ →ₗ[k] V₀)) (i : ι) (z : V₀ × W₀) :
    (pushPull v).1 i z = (v.1 i z.2, 0) := rfl

@[simp]
lemma pushPull_apply_snd (v : (ι → W₀ →ₗ[k] V₁) × (ι → W₁ →ₗ[k] V₀)) (i : ι) (z : V₁ × W₁) :
    (pushPull v).2 i z = (v.2 i z.2, 0) := rfl

variable {A : DoubledRep k ι V₀ V₁} {B : DoubledRep k ι W₀ W₁}
  {ξ : (ι → W₀ →ₗ[k] V₁) × (ι → W₁ →ₗ[k] V₀)}

lemma pushPull_mem_cocycles₁ [Fintype ι] {v : (ι → W₀ →ₗ[k] V₁) × (ι → W₁ →ₗ[k] V₀)}
    (hv : v ∈ cocycles₁ B A) : pushPull v ∈ cocycles₁ (extension A B ξ) (extension A B ξ) :=
  map₁_mem_cocycles₁ (snd_mem_Hom A B ξ) (inl_mem_Hom A B ξ) hv

lemma pushPull_mem_coboundaries₁ {v : (ι → W₀ →ₗ[k] V₁) × (ι → W₁ →ₗ[k] V₀)}
    (hv : v ∈ coboundaries₁ B A) :
    pushPull v ∈ coboundaries₁ (extension A B ξ) (extension A B ξ) :=
  map₁_mem_coboundaries₁ (snd_mem_Hom A B ξ) (inl_mem_Hom A B ξ) hv

variable (A B ξ) in
/-- `(a, b, h) ↦ a ξ - ξ b - d₀₁ h` on `End(A) × End(B) × C⁰(B, A)`. Its range is the tangent
space `orbitTangent`; when `Hom(A, B) = 0` its kernel is `End(N)` (`finrank_Hom_extension`). -/
def orbitMap : (Hom A A × Hom B B × ((W₀ →ₗ[k] V₀) × (W₁ →ₗ[k] V₁))) →ₗ[k]
    (ι → W₀ →ₗ[k] V₁) × (ι → W₁ →ₗ[k] V₀) :=
  (postcomp ξ ∘ₗ (Hom A A).subtype).coprod
    ((-(precomp ξ ∘ₗ (Hom B B).subtype)).coprod (-d₀₁ B A))

lemma orbitMap_apply (x : Hom A A × Hom B B × ((W₀ →ₗ[k] V₀) × (W₁ →ₗ[k] V₁))) :
    orbitMap A B ξ x =
      postcomp ξ (x.1 : (V₀ →ₗ[k] V₀) × (V₁ →ₗ[k] V₁)) -
        precomp ξ (x.2.1 : (W₀ →ₗ[k] W₀) × (W₁ →ₗ[k] W₁)) - d₀₁ B A x.2.2 := by
  obtain ⟨a, b, h⟩ := x
  simp [orbitMap, sub_eq_add_neg, add_assoc]

variable (A B ξ) in
/-- The tangent space at `ξ` to the orbit of `Aut(A) × Aut(B)`, lifted to cochains:
`End(A) ξ + ξ End(B)` plus the coboundaries. -/
def orbitTangent : Submodule k ((ι → W₀ →ₗ[k] V₁) × (ι → W₁ →ₗ[k] V₀)) :=
  LinearMap.range (orbitMap A B ξ)

variable (A B) in
/-- `(a, b, h) ↦ [[a, h], [0, b]]` at both vertices. -/
def blockMap : (Hom A A × Hom B B × ((W₀ →ₗ[k] V₀) × (W₁ →ₗ[k] V₁))) →ₗ[k]
    (V₀ × W₀ →ₗ[k] V₀ × W₀) × (V₁ × W₁ →ₗ[k] V₁ × W₁) where
  toFun x := (triangular (x.1 : (V₀ →ₗ[k] V₀) × (V₁ →ₗ[k] V₁)).1 x.2.2.1
      (x.2.1 : (W₀ →ₗ[k] W₀) × (W₁ →ₗ[k] W₁)).1,
    triangular (x.1 : (V₀ →ₗ[k] V₀) × (V₁ →ₗ[k] V₁)).2 x.2.2.2
      (x.2.1 : (W₀ →ₗ[k] W₀) × (W₁ →ₗ[k] W₁)).2)
  map_add' x y := by
    refine Prod.ext (LinearMap.ext fun z ↦ Prod.ext ?_ ?_)
      (LinearMap.ext fun z ↦ Prod.ext ?_ ?_)
    · simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, triangular_apply,
        LinearMap.add_apply, Prod.mk_add_mk]
      abel
    · simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, triangular_apply,
        LinearMap.add_apply, Prod.mk_add_mk]
    · simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, triangular_apply,
        LinearMap.add_apply, Prod.mk_add_mk]
      abel
    · simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, triangular_apply,
        LinearMap.add_apply, Prod.mk_add_mk]
  map_smul' c x := by
    refine Prod.ext (LinearMap.ext fun z ↦ Prod.ext ?_ ?_)
      (LinearMap.ext fun z ↦ Prod.ext ?_ ?_) <;>
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, triangular_apply,
      LinearMap.smul_apply, RingHom.id_apply, smul_add]

lemma blockMap_apply (x : Hom A A × Hom B B × ((W₀ →ₗ[k] V₀) × (W₁ →ₗ[k] V₁))) :
    blockMap A B x = (triangular (x.1 : (V₀ →ₗ[k] V₀) × (V₁ →ₗ[k] V₁)).1 x.2.2.1
      (x.2.1 : (W₀ →ₗ[k] W₀) × (W₁ →ₗ[k] W₁)).1,
    triangular (x.1 : (V₀ →ₗ[k] V₀) × (V₁ →ₗ[k] V₁)).2 x.2.2.2
      (x.2.1 : (W₀ →ₗ[k] W₀) × (W₁ →ₗ[k] W₁)).2) := rfl

/-- The coboundary of `[[a, h], [0, b]]`, for `a ∈ End(A)` and `b ∈ End(B)`, is
`-i (a ξ - ξ b - d₀₁ h) p`. -/
lemma d₀₁_blockMap (x : Hom A A × Hom B B × ((W₀ →ₗ[k] V₀) × (W₁ →ₗ[k] V₁))) :
    d₀₁ (extension A B ξ) (extension A B ξ) (blockMap A B x) =
      -pushPull (orbitMap A B ξ x) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, h⟩ := x
  have ha₁ : ∀ i x, a.2 (A.A i x) = A.A i (a.1 x) := fun i ↦ LinearMap.congr_fun (ha i).1
  have ha₂ : ∀ i x, a.1 (A.B i x) = A.B i (a.2 x) := fun i ↦ LinearMap.congr_fun (ha i).2
  have hb₁ : ∀ i x, b.2 (B.A i x) = B.A i (b.1 x) := fun i ↦ LinearMap.congr_fun (hb i).1
  have hb₂ : ∀ i x, b.1 (B.B i x) = B.B i (b.2 x) := fun i ↦ LinearMap.congr_fun (hb i).2
  refine Prod.ext (funext fun i ↦ LinearMap.ext fun z ↦ Prod.ext ?_ ?_)
    (funext fun i ↦ LinearMap.ext fun z ↦ Prod.ext ?_ ?_)
  · simp [blockMap_apply, orbitMap_apply, ha₁]
    abel
  · simp [blockMap_apply, orbitMap_apply, hb₁]
  · simp [blockMap_apply, orbitMap_apply, ha₂]
    abel
  · simp [blockMap_apply, orbitMap_apply, hb₂]

/-- **The blocks of a coboundary relation in the extension.** If `d₀₁ H = i v p` for a
zero-cochain `H` of `N = extension A B ξ` and `Hom(A, B) = 0`, then `H = [[a, h], [0, b]]` with
`a ∈ End(A)`, `b ∈ End(B)` and `a ξ - ξ b - d₀₁ h = -v`. -/
theorem exists_blockMap_of_d₀₁_eq (hAB : Hom A B = ⊥)
    {H : (V₀ × W₀ →ₗ[k] V₀ × W₀) × (V₁ × W₁ →ₗ[k] V₁ × W₁)}
    {v : (ι → W₀ →ₗ[k] V₁) × (ι → W₁ →ₗ[k] V₀)}
    (hH : d₀₁ (extension A B ξ) (extension A B ξ) H = pushPull v) :
    ∃ x, blockMap A B x = H ∧ orbitMap A B ξ x = -v := by
  have hA : ∀ i z, (extension A B ξ).A i (H.1 z) - H.2 ((extension A B ξ).A i z) =
      (v.1 i z.2, 0) := fun i z ↦ LinearMap.congr_fun (congrFun (congrArg Prod.fst hH) i) z
  have hB : ∀ i z, (extension A B ξ).B i (H.2 z) - H.1 ((extension A B ξ).B i z) =
      (v.2 i z.2, 0) := fun i z ↦ LinearMap.congr_fun (congrFun (congrArg Prod.snd hH) i) z
  have split₀ : ∀ x y, H.1 (x, y) = H.1 (x, 0) + H.1 (0, y) := fun x y ↦ by
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
  have split₁ : ∀ x y, H.2 (x, y) = H.2 (x, 0) + H.2 (0, y) := fun x y ↦ by
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
  -- The block `A → B` of `H` is a morphism, hence zero.
  have hc : ((LinearMap.snd k V₀ W₀ ∘ₗ H.1 ∘ₗ LinearMap.inl k V₀ W₀,
      LinearMap.snd k V₁ W₁ ∘ₗ H.2 ∘ₗ LinearMap.inl k V₁ W₁) :
        (V₀ →ₗ[k] W₀) × (V₁ →ₗ[k] W₁)) ∈ Hom A B := by
    refine fun i ↦ ⟨LinearMap.ext fun x ↦ ?_, LinearMap.ext fun x ↦ ?_⟩
    · have := congrArg Prod.snd (hA i (x, 0))
      simp only [extension_A_apply, map_zero, add_zero, Prod.snd_sub] at this
      rw [sub_eq_zero] at this
      simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.snd_apply]
      exact this.symm
    · have := congrArg Prod.snd (hB i (x, 0))
      simp only [extension_B_apply, map_zero, add_zero, Prod.snd_sub] at this
      rw [sub_eq_zero] at this
      simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.snd_apply]
      exact this.symm
  rw [hAB, Submodule.mem_bot] at hc
  have hc₀ : ∀ x, (H.1 (x, 0)).2 = 0 := fun x ↦ by
    simpa using LinearMap.congr_fun (congrArg Prod.fst hc) x
  have hc₁ : ∀ x, (H.2 (x, 0)).2 = 0 := fun x ↦ by
    simpa using LinearMap.congr_fun (congrArg Prod.snd hc) x
  -- The diagonal blocks are endomorphisms.
  have ha : ((LinearMap.fst k V₀ W₀ ∘ₗ H.1 ∘ₗ LinearMap.inl k V₀ W₀,
      LinearMap.fst k V₁ W₁ ∘ₗ H.2 ∘ₗ LinearMap.inl k V₁ W₁) :
        (V₀ →ₗ[k] V₀) × (V₁ →ₗ[k] V₁)) ∈ Hom A A := by
    refine fun i ↦ ⟨LinearMap.ext fun x ↦ ?_, LinearMap.ext fun x ↦ ?_⟩
    · have := congrArg Prod.fst (hA i (x, 0))
      simp only [extension_A_apply, map_zero, add_zero, Prod.fst_sub, hc₀] at this
      rw [sub_eq_zero] at this
      simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.fst_apply]
      exact this.symm
    · have := congrArg Prod.fst (hB i (x, 0))
      simp only [extension_B_apply, map_zero, add_zero, Prod.fst_sub, hc₁] at this
      rw [sub_eq_zero] at this
      simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.fst_apply]
      exact this.symm
  have hb : ((LinearMap.snd k V₀ W₀ ∘ₗ H.1 ∘ₗ LinearMap.inr k V₀ W₀,
      LinearMap.snd k V₁ W₁ ∘ₗ H.2 ∘ₗ LinearMap.inr k V₁ W₁) :
        (W₀ →ₗ[k] W₀) × (W₁ →ₗ[k] W₁)) ∈ Hom B B := by
    refine fun i ↦ ⟨LinearMap.ext fun y ↦ ?_, LinearMap.ext fun y ↦ ?_⟩
    · have := congrArg Prod.snd (hA i (0, y))
      simp only [extension_A_apply, map_zero, zero_add, Prod.snd_sub] at this
      rw [split₁, Prod.snd_add, hc₁, zero_add, sub_eq_zero] at this
      simp only [LinearMap.comp_apply, LinearMap.inr_apply, LinearMap.snd_apply]
      exact this.symm
    · have := congrArg Prod.snd (hB i (0, y))
      simp only [extension_B_apply, map_zero, zero_add, Prod.snd_sub] at this
      rw [split₀, Prod.snd_add, hc₀, zero_add, sub_eq_zero] at this
      simp only [LinearMap.comp_apply, LinearMap.inr_apply, LinearMap.snd_apply]
      exact this.symm
  refine ⟨(⟨_, ha⟩, ⟨_, hb⟩, (LinearMap.fst k V₀ W₀ ∘ₗ H.1 ∘ₗ LinearMap.inr k V₀ W₀,
    LinearMap.fst k V₁ W₁ ∘ₗ H.2 ∘ₗ LinearMap.inr k V₁ W₁)), ?_, ?_⟩
  · refine Prod.ext (LinearMap.ext fun z ↦ ?_) (LinearMap.ext fun z ↦ ?_)
    · rw [blockMap_apply, split₀ z.1 z.2]
      simp [Prod.ext_iff, hc₀]
    · rw [blockMap_apply, split₁ z.1 z.2]
      simp [Prod.ext_iff, hc₁]
  · refine Prod.ext (funext fun i ↦ LinearMap.ext fun y ↦ ?_)
      (funext fun i ↦ LinearMap.ext fun y ↦ ?_)
    · have := congrArg Prod.fst (hA i (0, y))
      simp only [extension_A_apply, map_zero, zero_add, Prod.fst_sub] at this
      rw [split₁, Prod.fst_add] at this
      simp only [orbitMap_apply, Prod.fst_sub, Pi.sub_apply, LinearMap.sub_apply,
        postcomp_apply_fst, precomp_apply_fst, d₀₁_apply_fst, LinearMap.comp_apply,
        LinearMap.inl_apply, LinearMap.inr_apply, LinearMap.fst_apply, LinearMap.snd_apply,
        Prod.fst_neg, Pi.neg_apply, LinearMap.neg_apply]
      rw [← this]
      abel
    · have := congrArg Prod.fst (hB i (0, y))
      simp only [extension_B_apply, map_zero, zero_add, Prod.fst_sub] at this
      rw [split₀, Prod.fst_add] at this
      simp only [orbitMap_apply, Prod.snd_sub, Pi.sub_apply, LinearMap.sub_apply,
        postcomp_apply_snd, precomp_apply_snd, d₀₁_apply_snd, LinearMap.comp_apply,
        LinearMap.inl_apply, LinearMap.inr_apply, LinearMap.fst_apply, LinearMap.snd_apply,
        Prod.snd_neg, Pi.neg_apply, LinearMap.neg_apply]
      rw [← this]
      abel

/-- **The injection, on cochains.** If `Hom(A, B) = 0` and `i v p` is a coboundary of the
extension `N`, then `v` lies in `End(A) ξ + ξ End(B)` plus the coboundaries. -/
theorem mem_orbitTangent_of_pushPull_mem (hAB : Hom A B = ⊥)
    {v : (ι → W₀ →ₗ[k] V₁) × (ι → W₁ →ₗ[k] V₀)}
    (hv : pushPull v ∈ coboundaries₁ (extension A B ξ) (extension A B ξ)) :
    v ∈ orbitTangent A B ξ := by
  obtain ⟨H, hH⟩ := hv
  obtain ⟨x, -, hx⟩ := exists_blockMap_of_d₀₁_eq hAB hH
  exact ⟨-x, by rw [map_neg, hx, neg_neg]⟩

/-- Conversely `i v p` is a coboundary for every `v` in `End(A) ξ + ξ End(B)` plus the
coboundaries. -/
theorem pushPull_mem_coboundaries₁_of_mem_orbitTangent
    {v : (ι → W₀ →ₗ[k] V₁) × (ι → W₁ →ₗ[k] V₀)} (hv : v ∈ orbitTangent A B ξ) :
    pushPull v ∈ coboundaries₁ (extension A B ξ) (extension A B ξ) := by
  obtain ⟨x, rfl⟩ := hv
  exact ⟨-blockMap A B x, by rw [map_neg, d₀₁_blockMap, neg_neg]⟩

lemma coboundaries₁_le_orbitTangent : coboundaries₁ B A ≤ orbitTangent A B ξ := by
  rintro _ ⟨h, rfl⟩
  exact ⟨(0, 0, -h), by simp [orbitMap_apply]⟩

lemma postcomp_eq_map₁ (a : (V₀ →ₗ[k] V₀) × (V₁ →ₗ[k] V₁)) :
    postcomp ξ a = map₁ (LinearMap.id, LinearMap.id) a ξ :=
  Prod.ext (funext fun _ ↦ (LinearMap.comp_id _).symm) (funext fun _ ↦ (LinearMap.comp_id _).symm)

lemma precomp_eq_map₁ (b : (W₀ →ₗ[k] W₀) × (W₁ →ₗ[k] W₁)) :
    precomp ξ b = map₁ b (LinearMap.id, LinearMap.id) ξ :=
  Prod.ext (funext fun _ ↦ (LinearMap.id_comp _).symm) (funext fun _ ↦ (LinearMap.id_comp _).symm)

/-- `End(A) ξ + ξ End(B)` plus the coboundaries consists of cocycles. -/
lemma orbitTangent_le_cocycles₁ [Fintype ι] (hA : A.IsPreprojective) (hB : B.IsPreprojective)
    (hξ : ξ ∈ cocycles₁ B A) : orbitTangent A B ξ ≤ cocycles₁ B A := by
  rintro _ ⟨⟨⟨a, ha⟩, ⟨b, hb⟩, h⟩, rfl⟩
  rw [orbitMap_apply]
  refine sub_mem (sub_mem ?_ ?_) (coboundaries₁_le_cocycles₁ hB hA ⟨h, rfl⟩)
  · rw [postcomp_eq_map₁]
    exact map₁_mem_cocycles₁ (id_mem_Hom B) ha hξ
  · rw [precomp_eq_map₁]
    exact map₁_mem_cocycles₁ hb (id_mem_Hom A) hξ

variable [Fintype ι]

variable (A B ξ) in
/-- `End(A) ξ + ξ End(B)` as a subspace of `Ext¹(B, A)`. -/
def orbitSpan : Submodule k (Ext1 B A) :=
  ((orbitTangent A B ξ).comap (cocycles₁ B A).subtype).map
    ((coboundaries₁ B A).comap (cocycles₁ B A).subtype).mkQ

variable (A B ξ) in
/-- `v ↦ i v p` on one-cocycles. -/
def pushPullCocycles : cocycles₁ B A →ₗ[k] cocycles₁ (extension A B ξ) (extension A B ξ) :=
  pushPull.restrict fun _ hv ↦ pushPull_mem_cocycles₁ hv

@[simp]
lemma coe_pushPullCocycles (v : cocycles₁ B A) :
    (pushPullCocycles A B ξ v : (ι → V₀ × W₀ →ₗ[k] V₁ × W₁) × (ι → V₁ × W₁ →ₗ[k] V₀ × W₀)) =
      pushPull (v : (ι → W₀ →ₗ[k] V₁) × (ι → W₁ →ₗ[k] V₀)) := rfl

lemma pushPullCocycles_le :
    (coboundaries₁ B A).comap (cocycles₁ B A).subtype ≤
      ((coboundaries₁ (extension A B ξ) (extension A B ξ)).comap
        (cocycles₁ (extension A B ξ) (extension A B ξ)).subtype).comap
        (pushPullCocycles A B ξ) := fun v hv ↦ by
  simp only [Submodule.mem_comap, Submodule.subtype_apply, coe_pushPullCocycles] at hv ⊢
  exact pushPull_mem_coboundaries₁ hv

variable (A B ξ) in
/-- The map `Ext¹(B, A) → Ext¹(N, N)` induced by `v ↦ i v p`. -/
def extPushPull : Ext1 B A →ₗ[k] Ext1 (extension A B ξ) (extension A B ξ) :=
  Submodule.mapQ _ _ (pushPullCocycles A B ξ) pushPullCocycles_le

variable (A B ξ) in
/-- The map `Ext¹(B, A)/(End(A) ξ + ξ End(B)) → Ext¹(N, N)` induced by `v ↦ i v p`. -/
def extQuotPushPull :
    (Ext1 B A ⧸ orbitSpan A B ξ) →ₗ[k] Ext1 (extension A B ξ) (extension A B ξ) :=
  (orbitSpan A B ξ).liftQ (extPushPull A B ξ) (by
    rintro _ ⟨v, hv, rfl⟩
    rw [LinearMap.mem_ker, Submodule.mkQ_apply, extPushPull, Submodule.mapQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact pushPull_mem_coboundaries₁_of_mem_orbitTangent hv)

/-- **The injection.** For an extension `0 → A → N → B → 0` with class `ξ` and
`Hom(A, B) = 0`, the map `v ↦ i v p` induces an injective linear map
`Ext¹(B, A)/(End(A) ξ + ξ End(B)) → Ext¹(N, N)`. -/
theorem extQuotPushPull_injective (hAB : Hom A B = ⊥) :
    Function.Injective (extQuotPushPull A B ξ) := by
  rw [← LinearMap.ker_eq_bot]
  refine Submodule.ker_liftQ_eq_bot _ _ _ fun e he ↦ ?_
  induction e using Submodule.Quotient.induction_on with
  | H v =>
    rw [LinearMap.mem_ker, extPushPull, Submodule.mapQ_apply,
      Submodule.Quotient.mk_eq_zero] at he
    exact ⟨v, mem_orbitTangent_of_pushPull_mem hAB he, rfl⟩

/-- **The corollary for a rigid middle term.** If `Hom(A, B) = 0` and `Ext¹(N, N) = 0`, then
`Ext¹(B, A) = End(A) ξ + ξ End(B)`. -/
theorem orbitSpan_eq_top (hAB : Hom A B = ⊥)
    (hN : Subsingleton (Ext1 (extension A B ξ) (extension A B ξ))) :
    orbitSpan A B ξ = ⊤ :=
  Submodule.Quotient.subsingleton_iff.mp (extQuotPushPull_injective hAB).subsingleton

/-- The same on cochains: every cocycle lies in `End(A) ξ + ξ End(B)` plus the coboundaries. -/
theorem cocycles₁_le_orbitTangent (hAB : Hom A B = ⊥)
    (hN : Subsingleton (Ext1 (extension A B ξ) (extension A B ξ))) :
    cocycles₁ B A ≤ orbitTangent A B ξ := fun _ hv ↦
  mem_orbitTangent_of_pushPull_mem hAB
    ((subsingleton_Ext1_iff _ _).mp hN (pushPull_mem_cocycles₁ hv))

end Injection

/-! ### The dimension of `Ext¹` -/

section Dimension

/-- The trace pairing `(f, g) ↦ tr(f g)` of maps `V → W` and `W → V` is nondegenerate. -/
lemma eq_zero_of_forall_trace_comp_eq_zero {V W : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    {f : V →ₗ[k] W} (h : ∀ g : W →ₗ[k] V, LinearMap.trace k W (f ∘ₗ g) = 0) : f = 0 := by
  refine LinearMap.ext fun x ↦ (Module.forall_dual_apply_eq_zero_iff k (f x)).mp fun φ ↦ ?_
  have hφ := h (φ.smulRight x)
  rwa [show f ∘ₗ φ.smulRight x = φ.smulRight (f x) from LinearMap.ext fun y ↦ by simp,
    LinearMap.trace_smulRight] at hφ

variable (k ι V₀ V₁ W₀ W₁) in
/-- The trace pairing between one-cochains of `(X, Y)` and of `(Y, X)`,
`⟨f, g⟩ = ∑ᵢ tr(f_{a_i} g_{b_i}) - tr(f_{b_i} g_{a_i})`. -/
noncomputable def tracePairing₁ [Fintype ι] : ((ι → V₀ →ₗ[k] W₁) × (ι → V₁ →ₗ[k] W₀)) →ₗ[k]
    Module.Dual k ((ι → W₀ →ₗ[k] V₁) × (ι → W₁ →ₗ[k] V₀)) :=
  LinearMap.mk₂ k (fun f g ↦ ∑ i, (LinearMap.trace k W₁ (f.1 i ∘ₗ g.2 i) -
      LinearMap.trace k W₀ (f.2 i ∘ₗ g.1 i)))
    (fun f f' g ↦ by
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, LinearMap.add_comp, map_add,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by ring)
    (fun c f g ↦ by
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, LinearMap.smul_comp, map_smul,
        smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by ring)
    (fun f g g' ↦ by
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, LinearMap.comp_add, map_add,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by ring)
    (fun c f g ↦ by
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, LinearMap.comp_smul, map_smul,
        smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by ring)

lemma tracePairing₁_apply [Fintype ι] (f : (ι → V₀ →ₗ[k] W₁) × (ι → V₁ →ₗ[k] W₀))
    (g : (ι → W₀ →ₗ[k] V₁) × (ι → W₁ →ₗ[k] V₀)) :
    tracePairing₁ k ι V₀ V₁ W₀ W₁ f g = ∑ i, (LinearMap.trace k W₁ (f.1 i ∘ₗ g.2 i) -
      LinearMap.trace k W₀ (f.2 i ∘ₗ g.1 i)) := rfl

variable (k V₀ V₁ W₀ W₁) in
/-- The trace pairing between two-cochains of `(X, Y)` and zero-cochains of `(Y, X)`,
`⟨c, h⟩ = tr(c₁ h₁) - tr(c₀ h₀)`. -/
noncomputable def tracePairing₂ : ((V₀ →ₗ[k] W₀) × (V₁ →ₗ[k] W₁)) →ₗ[k]
    Module.Dual k ((W₀ →ₗ[k] V₀) × (W₁ →ₗ[k] V₁)) :=
  LinearMap.mk₂ k (fun c h ↦ LinearMap.trace k W₁ (c.2 ∘ₗ h.2) - LinearMap.trace k W₀ (c.1 ∘ₗ h.1))
    (fun c c' h ↦ by
      simp only [Prod.fst_add, Prod.snd_add, LinearMap.add_comp, map_add]
      ring)
    (fun a c h ↦ by
      simp only [Prod.smul_fst, Prod.smul_snd, LinearMap.smul_comp, map_smul, smul_eq_mul]
      ring)
    (fun c h h' ↦ by
      simp only [Prod.fst_add, Prod.snd_add, LinearMap.comp_add, map_add]
      ring)
    (fun a c h ↦ by
      simp only [Prod.smul_fst, Prod.smul_snd, LinearMap.comp_smul, map_smul, smul_eq_mul]
      ring)

lemma tracePairing₂_apply (c : (V₀ →ₗ[k] W₀) × (V₁ →ₗ[k] W₁))
    (h : (W₀ →ₗ[k] V₀) × (W₁ →ₗ[k] V₁)) :
    tracePairing₂ k V₀ V₁ W₀ W₁ c h =
      LinearMap.trace k W₁ (c.2 ∘ₗ h.2) - LinearMap.trace k W₀ (c.1 ∘ₗ h.1) := rfl

private lemma sum_comp {U U' U'' : Type*} [AddCommGroup U] [Module k U] [AddCommGroup U']
    [Module k U'] [AddCommGroup U''] [Module k U''] [Fintype ι] (F : ι → U' →ₗ[k] U'')
    (G : U →ₗ[k] U') : (∑ i, F i) ∘ₗ G = ∑ i, F i ∘ₗ G :=
  LinearMap.ext fun x ↦ by simp [LinearMap.sum_apply]

variable [FiniteDimensional k V₀] [FiniteDimensional k V₁] [FiniteDimensional k W₀]
  [FiniteDimensional k W₁]

omit [FiniteDimensional k V₀] [FiniteDimensional k V₁] in
lemma tracePairing₂_injective : Function.Injective (tracePairing₂ k V₀ V₁ W₀ W₁) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro c hc
  rw [LinearMap.mem_ker] at hc
  refine Prod.ext (eq_zero_of_forall_trace_comp_eq_zero fun g ↦ ?_)
    (eq_zero_of_forall_trace_comp_eq_zero fun g ↦ ?_)
  · simpa [tracePairing₂_apply] using LinearMap.congr_fun hc (g, 0)
  · simpa [tracePairing₂_apply] using LinearMap.congr_fun hc (0, g)

omit [FiniteDimensional k V₀] [FiniteDimensional k V₁] in
lemma tracePairing₁_injective [Fintype ι] : Function.Injective (tracePairing₁ k ι V₀ V₁ W₀ W₁) := by
  classical
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro f hf
  rw [LinearMap.mem_ker] at hf
  refine Prod.ext (funext fun i ↦ eq_zero_of_forall_trace_comp_eq_zero fun g ↦ ?_)
    (funext fun i ↦ eq_zero_of_forall_trace_comp_eq_zero fun g ↦ ?_)
  · have := LinearMap.congr_fun hf (0, Pi.single i g)
    rw [tracePairing₁_apply, Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj])
      (by simp)] at this
    simpa using this
  · have := LinearMap.congr_fun hf (Pi.single i g, 0)
    rw [tracePairing₁_apply, Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj])
      (by simp)] at this
    simpa using this

lemma tracePairing₁_surjective [Fintype ι] :
    Function.Surjective (tracePairing₁ k ι V₀ V₁ W₀ W₁) := by
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp tracePairing₁_injective
  rw [Subspace.dual_finrank_eq]
  simp only [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_linearMap,
    Finset.sum_const, Finset.card_univ, smul_eq_mul]
  ring

omit [FiniteDimensional k V₀] [FiniteDimensional k V₁] in
/-- **The duality between the two differentials.** Under the trace pairings, `d₁₂` of `(X, Y)` is
the transpose of `d₀₁` of `(Y, X)`. This is the Calabi–Yau symmetry of the complex. -/
theorem dualMap_d₀₁_comp_tracePairing₁ [Fintype ι] (X : DoubledRep k ι V₀ V₁)
    (Y : DoubledRep k ι W₀ W₁) :
    (d₀₁ Y X).dualMap ∘ₗ tracePairing₁ k ι V₀ V₁ W₀ W₁ =
      tracePairing₂ k V₀ V₁ W₀ W₁ ∘ₗ d₁₂ X Y := by
  refine LinearMap.ext fun f ↦ LinearMap.ext fun h ↦ ?_
  have c₁ : ∀ i, LinearMap.trace k W₁ (f.1 i ∘ₗ h.1 ∘ₗ Y.B i) =
      LinearMap.trace k W₀ (Y.B i ∘ₗ f.1 i ∘ₗ h.1) := fun i ↦ by
    rw [← LinearMap.comp_assoc, LinearMap.trace_comp_comm']
  have c₂ : ∀ i, LinearMap.trace k W₀ (f.2 i ∘ₗ h.2 ∘ₗ Y.A i) =
      LinearMap.trace k W₁ (Y.A i ∘ₗ f.2 i ∘ₗ h.2) := fun i ↦ by
    rw [← LinearMap.comp_assoc, LinearMap.trace_comp_comm']
  simp only [LinearMap.comp_apply, LinearMap.dualMap_apply, tracePairing₁_apply,
    tracePairing₂_apply, d₀₁_apply_fst, d₀₁_apply_snd, d₁₂_apply_fst, d₁₂_apply_snd,
    LinearMap.comp_sub, sum_comp, LinearMap.add_comp, LinearMap.comp_assoc, map_sub, map_sum,
    map_add, c₁, c₂]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- `rank d₁₂(X, Y) = rank d₀₁(Y, X)`. -/
theorem finrank_range_d₁₂ [Fintype ι] (X : DoubledRep k ι V₀ V₁) (Y : DoubledRep k ι W₀ W₁) :
    finrank k (LinearMap.range (d₁₂ X Y)) = finrank k (LinearMap.range (d₀₁ Y X)) := by
  rw [← LinearMap.finrank_range_dualMap_eq_finrank_range (d₀₁ Y X),
    ← LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr tracePairing₁_surjective),
    dualMap_d₀₁_comp_tracePairing₁, LinearMap.range_comp]
  exact (Submodule.equivMapOfInjective _ tracePairing₂_injective _).finrank_eq

/-- **The dimension of `Ext¹`.** For representations `X`, `Y` with the preprojective relations,
of dimension vectors `x`, `y`,
`dim Ext¹(X, Y) = dim Hom(X, Y) + dim Hom(Y, X) - (2 x₀ y₀ + 2 x₁ y₁ - g (x₀ y₁ + x₁ y₀))`, the
last term the symmetric Euler form of the doubled `g`-Kronecker quiver. -/
theorem finrank_Ext1 [Fintype ι] {X : DoubledRep k ι V₀ V₁} {Y : DoubledRep k ι W₀ W₁}
    (hX : X.IsPreprojective) (hY : Y.IsPreprojective) :
    finrank k (Ext1 X Y) + 2 * (finrank k V₀ * finrank k W₀ + finrank k V₁ * finrank k W₁) =
      Fintype.card ι * (finrank k V₀ * finrank k W₁ + finrank k V₁ * finrank k W₀) +
        finrank k (Hom X Y) + finrank k (Hom Y X) := by
  have e₁ : finrank k (Ext1 X Y) + finrank k (coboundaries₁ X Y) =
      finrank k (cocycles₁ X Y) := by
    rw [← Submodule.finrank_quotient_add_finrank
      ((coboundaries₁ X Y).comap (cocycles₁ X Y).subtype)]
    congr 1
    exact (Submodule.comapSubtypeEquivOfLe (coboundaries₁_le_cocycles₁ hX hY)).finrank_eq.symm
  have e₂ : finrank k (LinearMap.range (d₁₂ X Y)) + finrank k (cocycles₁ X Y) =
      finrank k ((ι → V₀ →ₗ[k] W₁) × (ι → V₁ →ₗ[k] W₀)) :=
    LinearMap.finrank_range_add_finrank_ker _
  have e₃ : finrank k (coboundaries₁ X Y) + finrank k (Hom X Y) =
      finrank k ((V₀ →ₗ[k] W₀) × (V₁ →ₗ[k] W₁)) := by
    rw [← ker_d₀₁]
    exact LinearMap.finrank_range_add_finrank_ker _
  have e₄ : finrank k (LinearMap.range (d₀₁ Y X)) + finrank k (Hom Y X) =
      finrank k ((W₀ →ₗ[k] V₀) × (W₁ →ₗ[k] V₁)) := by
    rw [← ker_d₀₁]
    exact LinearMap.finrank_range_add_finrank_ker _
  have e₅ := finrank_range_d₁₂ X Y
  simp only [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_linearMap,
    Finset.sum_const, Finset.card_univ, smul_eq_mul] at e₂ e₃ e₄
  nlinarith

end Dimension

/-! ### Endomorphisms of an extension and Mukai's inequality -/

section Mukai

variable {A : DoubledRep k ι V₀ V₁} {B : DoubledRep k ι W₀ W₁}
  {ξ : (ι → W₀ →ₗ[k] V₁) × (ι → W₁ →ₗ[k] V₀)}

lemma blockMap_injective : Function.Injective (blockMap A B) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, h⟩ hx
  rw [LinearMap.mem_ker, blockMap_apply] at hx
  have h₀ := fun z ↦ LinearMap.congr_fun (congrArg Prod.fst hx) z
  have h₁ := fun z ↦ LinearMap.congr_fun (congrArg Prod.snd hx) z
  simp only [triangular_apply, Prod.fst_zero, Prod.snd_zero, LinearMap.zero_apply,
    Prod.mk_eq_zero] at h₀ h₁
  refine Prod.ext (Subtype.ext (Prod.ext ?_ ?_)) (Prod.ext (Subtype.ext (Prod.ext ?_ ?_))
    (Prod.ext ?_ ?_))
  · exact LinearMap.ext fun x ↦ by simpa using (h₀ (x, 0)).1
  · exact LinearMap.ext fun x ↦ by simpa using (h₁ (x, 0)).1
  · exact LinearMap.ext fun y ↦ by simpa using (h₀ (0, y)).2
  · exact LinearMap.ext fun y ↦ by simpa using (h₁ (0, y)).2
  · exact LinearMap.ext fun y ↦ by simpa using (h₀ (0, y)).1
  · exact LinearMap.ext fun y ↦ by simpa using (h₁ (0, y)).1

/-- **The endomorphisms of an extension.** If `Hom(A, B) = 0`, every endomorphism of `N` is
`[[a, h], [0, b]]` with `a ξ - ξ b = d₀₁ h`, so `End(N)` is the kernel of `orbitMap`. -/
theorem finrank_Hom_extension (hAB : Hom A B = ⊥) :
    finrank k (Hom (extension A B ξ) (extension A B ξ)) =
      finrank k (LinearMap.ker (orbitMap A B ξ)) := by
  let Θ : LinearMap.ker (orbitMap A B ξ) →ₗ[k] Hom (extension A B ξ) (extension A B ξ) :=
    (blockMap A B).restrict fun x hx ↦ by
      rw [← ker_d₀₁, LinearMap.mem_ker, d₀₁_blockMap, LinearMap.mem_ker.mp hx, map_zero,
        neg_zero]
  have hbij : Function.Bijective Θ := by
    refine ⟨fun x y hxy ↦ Subtype.ext (blockMap_injective (congrArg Subtype.val hxy)),
      fun H ↦ ?_⟩
    have hH : d₀₁ (extension A B ξ) (extension A B ξ) H = pushPull 0 := by
      rw [map_zero, ← LinearMap.mem_ker, ker_d₀₁]
      exact H.2
    obtain ⟨x, hx, hx'⟩ := exists_blockMap_of_d₀₁_eq hAB hH
    exact ⟨⟨x, by rw [LinearMap.mem_ker, hx', neg_zero]⟩, Subtype.ext hx⟩
  exact (LinearEquiv.ofBijective Θ hbij).finrank_eq.symm

variable [Fintype ι] [FiniteDimensional k V₀] [FiniteDimensional k V₁] [FiniteDimensional k W₀]
  [FiniteDimensional k W₁]

/-- **Mukai's inequality, with its defect.** For an extension `0 → A → N → B → 0` of
representations with the preprojective relations and `Hom(A, B) = 0`,
`dim Ext¹(N, N) = dim Ext¹(A, A) + dim Ext¹(B, B) + 2 dim Ext¹(B, A)/(End(A) ξ + ξ End(B))`. -/
theorem finrank_Ext1_extension (hA : A.IsPreprojective) (hB : B.IsPreprojective)
    (hξ : ξ ∈ cocycles₁ B A) (hAB : Hom A B = ⊥) :
    finrank k (Ext1 (extension A B ξ) (extension A B ξ)) =
      finrank k (Ext1 A A) + finrank k (Ext1 B B) +
        2 * finrank k (Ext1 B A ⧸ orbitSpan A B ξ) := by
  have hN := (isPreprojective_extension_iff A B ξ).mpr ⟨hA, hB, hξ⟩
  have eN := finrank_Ext1 hN hN
  have eA := finrank_Ext1 hA hA
  have eB := finrank_Ext1 hB hB
  have eBA := finrank_Ext1 hB hA
  rw [hAB, finrank_bot] at eBA
  have hEnd := finrank_Hom_extension (ξ := ξ) hAB
  have hrn : finrank k (orbitTangent A B ξ) + finrank k (LinearMap.ker (orbitMap A B ξ)) =
      finrank k (Hom A A × Hom B B × ((W₀ →ₗ[k] V₀) × (W₁ →ₗ[k] V₁))) :=
    LinearMap.finrank_range_add_finrank_ker _
  have e₁ : finrank k (Ext1 B A) + finrank k (coboundaries₁ B A) =
      finrank k (cocycles₁ B A) := by
    rw [← Submodule.finrank_quotient_add_finrank
      ((coboundaries₁ B A).comap (cocycles₁ B A).subtype)]
    congr 1
    exact (Submodule.comapSubtypeEquivOfLe (coboundaries₁_le_cocycles₁ hB hA)).finrank_eq.symm
  have e₃ : finrank k (coboundaries₁ B A) + finrank k (Hom B A) =
      finrank k ((W₀ →ₗ[k] V₀) × (W₁ →ₗ[k] V₁)) := by
    rw [← ker_d₀₁]
    exact LinearMap.finrank_range_add_finrank_ker _
  have e₄ : finrank k (Ext1 B A ⧸ orbitSpan A B ξ) + finrank k (orbitTangent A B ξ) =
      finrank k (cocycles₁ B A) := by
    rw [orbitSpan, (Submodule.quotientQuotientEquivQuotient _ _
      (Submodule.comap_mono coboundaries₁_le_orbitTangent)).finrank_eq,
      ← Submodule.finrank_quotient_add_finrank
        ((orbitTangent A B ξ).comap (cocycles₁ B A).subtype)]
    congr 1
    exact (Submodule.comapSubtypeEquivOfLe
      (orbitTangent_le_cocycles₁ hA hB hξ)).finrank_eq.symm
  simp only [Module.finrank_prod, Module.finrank_linearMap] at eN hrn e₃
  zify at eN eA eB eBA hEnd hrn e₁ e₃ e₄ ⊢
  linear_combination eN - eA - eB + 2 * hEnd + 2 * hrn - 2 * e₄ + 2 * e₁ - 2 * e₃ - 2 * eBA

/-- **Mukai's inequality** (Bayer–Bridgeland, arXiv:1310.8266, Lemma 2.5, in the quiver model):
`dim Ext¹(A, A) + dim Ext¹(B, B) ≤ dim Ext¹(N, N)` when `Hom(A, B) = 0`. -/
theorem finrank_Ext1_add_le (hA : A.IsPreprojective) (hB : B.IsPreprojective)
    (hξ : ξ ∈ cocycles₁ B A) (hAB : Hom A B = ⊥) :
    finrank k (Ext1 A A) + finrank k (Ext1 B B) ≤
      finrank k (Ext1 (extension A B ξ) (extension A B ξ)) := by
  rw [finrank_Ext1_extension hA hB hξ hAB]
  omega

/-- **A rigid extension has rigid pieces.** If `N` is rigid and `Hom(A, B) = 0`, then `A` and `B`
are rigid and `Ext¹(B, A) = End(A) ξ + ξ End(B)`. -/
theorem rigid_of_rigid_extension (hA : A.IsPreprojective) (hB : B.IsPreprojective)
    (hξ : ξ ∈ cocycles₁ B A) (hAB : Hom A B = ⊥)
    (hN : Subsingleton (Ext1 (extension A B ξ) (extension A B ξ))) :
    Subsingleton (Ext1 A A) ∧ Subsingleton (Ext1 B B) := by
  have h := finrank_Ext1_extension hA hB hξ hAB
  rw [Module.finrank_zero_of_subsingleton] at h
  exact ⟨(finrank_eq_zero_iff_of_free k _).mp (by omega),
    (finrank_eq_zero_iff_of_free k _).mp (by omega)⟩

end Mukai

end Quiver.Kronecker.DoubledRep
