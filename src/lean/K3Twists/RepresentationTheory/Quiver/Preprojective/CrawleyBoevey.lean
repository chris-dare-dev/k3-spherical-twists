/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.RepresentationTheory.Quiver.Preprojective.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Trace

/-!
# The Crawley-Boevey complex of a doubled quiver

For representations `X` on spaces `V i` and `Y` on spaces `W i` of the double of a quiver `Q`
(loops allowed), `Ext` over the preprojective algebra is computed by the standard three-term
complex

  `⊕_i Hom(V_i, W_i) → ⊕_{a : i → j} (Hom(V_i, W_j) ⊕ Hom(V_j, W_i)) → ⊕_i Hom(V_i, W_i)`,

whose first map is `h ↦ (A_a h_i - h_j A_a, B_a h_j - h_i B_a)_a` and whose second map is the
derivative of the preprojective relations. Here `Ext¹(X, Y)` is *defined* as the one-cocycles
modulo the one-coboundaries (`DoubledRep.Ext1`). The kernel in degree zero is `Hom(X, Y)`, and the
two differentials are transposes of each other under the trace pairings, so the cokernel in degree
two is dual to `Hom(Y, X)`.

## Main results

* `DoubledRep.ker_d₀`: `H⁰ = Hom(X, Y)`; `DoubledRep.d₁_comp_d₀`: the complex is a complex for
  representations with the preprojective relations;
* `DoubledRep.dualMap_d₀_comp_tracePairing₁`: the duality of the two differentials;
* `DoubledRep.finrank_Ext1`, `DoubledRep.finrank_Ext1_eq`: **Crawley-Boevey's formula**
  `dim Ext¹(X, Y) = dim Hom(X, Y) + dim Hom(Y, X) - (x, y)` for representations with the
  relations, with `(x, y) = ∑_i 2 x_i y_i - ∑_{a : i → j} (x_i y_j + x_j y_i)` the symmetric Euler
  form of `Q` (`Quiver.Preprojective.eulerForm`) (Crawley-Boevey, *On the exceptional fibres of
  Kleinian singularities*, Amer. J. Math. 122 (2000), Lemma 1). Written with the Mukai pairing
  `⟨x, y⟩ = -(x, y)` of the classes of a 2-Calabi–Yau category it reads
  `dim Ext¹(X, Y) = hom(X, Y) + hom(Y, X) + ⟨x, y⟩`;
* `DoubledRep.selfExtDim_eq`: `e(X) = 2 dim End X - 2 q(x)`, `q` the Tits form
  (`Quiver.Preprojective.titsForm`); in Mukai's notation `e = 2 dim End + v²`, and
  `DoubledRep.even_selfExtDim`: `e` is even;
* **Bricks**: if `End X = k` then `q(x) ≤ 1` (`DoubledRep.titsForm_le_one_of_brick`), `X` is rigid
  exactly when `q(x) = 1` (`DoubledRep.selfExtDim_eq_zero_iff_of_brick`), and `e(X) = 2` exactly
  when `q(x) = 0` (`DoubledRep.selfExtDim_eq_two_iff_of_brick`); so a rigid or semirigid brick
  has `q = 1` or `q = 0` (`DoubledRep.titsForm_eq_one_or_eq_zero_of_brick`). Riemann–Roch
  `e = 2 + v²` holds for bricks only.
* `DoubledRep.Iso.selfExtDim_eq`: `e` is invariant under isomorphism.

For the doubled Kronecker quiver this is `Quiver.Kronecker.DoubledRep.finrank_Ext1`.

## Implementation notes

The cochains of `(X, Y)` depend only on the vertex spaces: `Cochain₀ k V W` is
`∀ i, V i →ₗ W i` (zero- and two-cochains), and `Cochain₁ k Q V W` is a pair of families indexed by
the arrows, deforming the maps `A a` and `B a`. Because arrows are typed by their endpoints, the
cochains need no transport between vertex spaces.
-/

namespace Quiver.Preprojective

open Module

section Forms

variable {I : Type*} (Q : I → I → Type*) [Fintype I] [∀ i j, Fintype (Q i j)]

/-- The symmetric Euler form of `Q` on dimension vectors,
`(x, y) = ∑_i 2 x_i y_i - ∑_{a : i → j} (x_i y_j + x_j y_i)`. For two spheres with `g` arrows
it is `2 x₀ y₀ + 2 x₁ y₁ - g (x₀ y₁ + x₁ y₀)`; a loop at `i` contributes `-2 x_i y_i`. -/
def eulerForm (x y : I → ℤ) : ℤ :=
  ∑ i, 2 * x i * y i - ∑ i, ∑ j, (Fintype.card (Q i j) : ℤ) * (x i * y j + x j * y i)

/-- The Tits form `q(x) = ∑_i x_i² - ∑_{a : i → j} x_i x_j`, half the Euler form on the
diagonal. -/
def titsForm (x : I → ℤ) : ℤ :=
  ∑ i, x i ^ 2 - ∑ i, ∑ j, (Fintype.card (Q i j) : ℤ) * (x i * x j)

lemma eulerForm_self (x : I → ℤ) : eulerForm Q x x = 2 * titsForm Q x := by
  simp only [eulerForm, titsForm, mul_sub, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun i _ ↦ by ring
  · exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

lemma eulerForm_comm (x y : I → ℤ) : eulerForm Q x y = eulerForm Q y x := by
  simp only [eulerForm]
  congr 1
  · exact Finset.sum_congr rfl fun i _ ↦ by ring
  · exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

end Forms

namespace DoubledRep

variable {k : Type*} [Field k] {I : Type*} {Q : I → I → Type*} {V W : I → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [∀ i, AddCommGroup (W i)]
  [∀ i, Module k (W i)]

variable (k V W) in
/-- Zero-cochains (and two-cochains) of the complex of `(X, Y)`: a map `V i → W i` at each
vertex. -/
abbrev Cochain₀ := ∀ i, V i →ₗ[k] W i

variable (k Q V W) in
/-- One-cochains of the complex of `(X, Y)`: a map `V i → W j` for every arrow `a : i → j`
(deforming `A a`) and a map `V j → W i` for its reverse (deforming `B a`). -/
abbrev Cochain₁ := (∀ i j, Q i j → V i →ₗ[k] W j) × (∀ i j, Q i j → V j →ₗ[k] W i)

/-! ### The complex -/

section Complex

variable (X : DoubledRep k Q V) (Y : DoubledRep k Q W)

/-- The degree-zero differential: `h ↦ (A_a h_i - h_j A_a, B_a h_j - h_i B_a)_a`. -/
def d₀ : Cochain₀ k V W →ₗ[k] Cochain₁ k Q V W where
  toFun h := (fun i j a ↦ Y.A a ∘ₗ h i - h j ∘ₗ X.A a, fun i j a ↦ Y.B a ∘ₗ h j - h i ∘ₗ X.B a)
  map_add' h h' := by
    refine Prod.ext (funext fun i ↦ funext fun j ↦ funext fun a ↦ ?_)
      (funext fun i ↦ funext fun j ↦ funext fun a ↦ ?_) <;>
    · simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add, LinearMap.comp_add, LinearMap.add_comp]
      abel
  map_smul' c h := by
    refine Prod.ext (funext fun i ↦ funext fun j ↦ funext fun a ↦ ?_)
      (funext fun i ↦ funext fun j ↦ funext fun a ↦ ?_) <;>
    · simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, LinearMap.comp_smul,
        LinearMap.smul_comp, RingHom.id_apply, smul_sub]

@[simp]
lemma d₀_apply_fst (h : Cochain₀ k V W) (i j : I) (a : Q i j) :
    (d₀ X Y h).1 i j a = Y.A a ∘ₗ h i - h j ∘ₗ X.A a :=
  rfl

@[simp]
lemma d₀_apply_snd (h : Cochain₀ k V W) (i j : I) (a : Q i j) :
    (d₀ X Y h).2 i j a = Y.B a ∘ₗ h j - h i ∘ₗ X.B a :=
  rfl

/-- `H⁰` of the complex is `Hom(X, Y)`. -/
theorem ker_d₀ : LinearMap.ker (d₀ X Y) = Hom X Y := by
  ext h
  simp only [LinearMap.mem_ker, mem_Hom, Prod.ext_iff, funext_iff, d₀_apply_fst, d₀_apply_snd,
    Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, sub_eq_zero]
  exact ⟨fun h i j a ↦ ⟨(h.1 i j a).symm, (h.2 i j a).symm⟩,
    fun h ↦ ⟨fun i j a ↦ (h i j a).1.symm, fun i j a ↦ (h i j a).2.symm⟩⟩

/-- The one-coboundaries `B¹(X, Y)`, the range of `d₀`. -/
def coboundaries : Submodule k (Cochain₁ k Q V W) :=
  LinearMap.range (d₀ X Y)

variable [Fintype I] [∀ i j, Fintype (Q i j)]

/-- The degree-one differential, the linearized preprojective relations: at the vertex `i`,
`∑_{a : j → i} (A_a f_{a*} + f_a B_a) - ∑_{a : i → j} (B_a f_a + f_{a*} A_a)`. -/
def d₁ : Cochain₁ k Q V W →ₗ[k] Cochain₀ k V W where
  toFun c i := ∑ j, ∑ a : Q j i, (Y.A a ∘ₗ c.2 j i a + c.1 j i a ∘ₗ X.B a) -
    ∑ j, ∑ a : Q i j, (Y.B a ∘ₗ c.1 i j a + c.2 i j a ∘ₗ X.A a)
  map_add' c c' := by
    funext i
    simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add, LinearMap.comp_add, LinearMap.add_comp,
      Finset.sum_add_distrib]
    abel
  map_smul' c h := by
    funext i
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, LinearMap.comp_smul,
      LinearMap.smul_comp, smul_add, Finset.smul_sum, RingHom.id_apply, smul_sub]

lemma d₁_apply (c : Cochain₁ k Q V W) (i : I) :
    d₁ X Y c i = ∑ j, ∑ a : Q j i, (Y.A a ∘ₗ c.2 j i a + c.1 j i a ∘ₗ X.B a) -
      ∑ j, ∑ a : Q i j, (Y.B a ∘ₗ c.1 i j a + c.2 i j a ∘ₗ X.A a) :=
  rfl

variable {X Y} in
/-- The square of the differential vanishes when both representations satisfy the relations:
`d₁ (d₀ h)` at `i` is `relation Y i ∘ h i - h i ∘ relation X i`. -/
theorem d₁_comp_d₀ (hX : X.IsPreprojective) (hY : Y.IsPreprojective) :
    d₁ X Y ∘ₗ d₀ X Y = 0 := by
  refine LinearMap.ext fun h ↦ funext fun i ↦ LinearMap.ext fun x ↦ ?_
  have hY' := LinearMap.congr_fun (hY i) (h i x)
  have hX' := congrArg (h i) (LinearMap.congr_fun (hX i) x)
  simp only [relation_apply, map_sub, map_sum, LinearMap.zero_apply, map_zero] at hY' hX'
  simp only [LinearMap.comp_apply, d₁_apply, d₀_apply_fst, d₀_apply_snd, LinearMap.sub_apply,
    LinearMap.sum_apply, LinearMap.add_apply, map_sub, LinearMap.zero_apply, Pi.zero_apply]
  calc _ = (∑ j, ∑ a : Q j i, (Y.A a (Y.B a (h i x)) - h i (X.A a (X.B a x)))) -
        ∑ j, ∑ a : Q i j, (Y.B a (Y.A a (h i x)) - h i (X.B a (X.A a x))) := by
        congr 1 <;>
        exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun a _ ↦ by abel
    _ = ((∑ j, ∑ a : Q j i, Y.A a (Y.B a (h i x))) - ∑ j, ∑ a : Q i j, Y.B a (Y.A a (h i x))) -
        ((∑ j, ∑ a : Q j i, h i (X.A a (X.B a x))) - ∑ j, ∑ a : Q i j, h i (X.B a (X.A a x))) := by
        simp only [Finset.sum_sub_distrib]
        abel
    _ = 0 := by rw [hY', hX', sub_zero]

/-- The one-cocycles `Z¹(X, Y)`, the kernel of `d₁`. -/
def cocycles : Submodule k (Cochain₁ k Q V W) :=
  LinearMap.ker (d₁ X Y)

variable {X Y} in
lemma coboundaries_le_cocycles (hX : X.IsPreprojective) (hY : Y.IsPreprojective) :
    coboundaries X Y ≤ cocycles X Y := by
  rintro _ ⟨h, rfl⟩
  exact LinearMap.congr_fun (d₁_comp_d₀ hX hY) h

/-- `Ext¹(X, Y)`: the one-cocycles modulo the one-coboundaries. -/
abbrev Ext1 := cocycles X Y ⧸ (coboundaries X Y).comap (cocycles X Y).subtype

/-- `Ext¹(X, Y)` vanishes exactly when every one-cocycle is a coboundary. -/
theorem subsingleton_Ext1_iff : Subsingleton (Ext1 X Y) ↔ cocycles X Y ≤ coboundaries X Y := by
  rw [Submodule.Quotient.subsingleton_iff, Submodule.comap_subtype_eq_top]

end Complex

lemma mem_cocycles [Fintype I] [∀ i j, Fintype (Q i j)] {X : DoubledRep k Q V}
    {Y : DoubledRep k Q W} {c : Cochain₁ k Q V W} :
    c ∈ cocycles X Y ↔ d₁ X Y c = 0 :=
  LinearMap.mem_ker

lemma mem_coboundaries {X : DoubledRep k Q V} {Y : DoubledRep k Q W} {c : Cochain₁ k Q V W} :
    c ∈ coboundaries X Y ↔ ∃ h, d₀ X Y h = c :=
  LinearMap.mem_range

/-! ### Composition with morphisms -/

section Functoriality

variable {V' W' : I → Type*} [∀ i, AddCommGroup (V' i)] [∀ i, Module k (V' i)]
  [∀ i, AddCommGroup (W' i)] [∀ i, Module k (W' i)]

/-- Composition on both sides of a zero-cochain: `h ↦ w ∘ h ∘ f` at each vertex. -/
def map₀ (f : ∀ i, V' i →ₗ[k] V i) (w : ∀ i, W i →ₗ[k] W' i) :
    Cochain₀ k V W →ₗ[k] Cochain₀ k V' W' where
  toFun h i := w i ∘ₗ h i ∘ₗ f i
  map_add' h h' := by
    funext i
    simp only [Pi.add_apply, LinearMap.add_comp, LinearMap.comp_add]
  map_smul' c h := by
    funext i
    simp only [Pi.smul_apply, LinearMap.smul_comp, LinearMap.comp_smul, RingHom.id_apply]

@[simp]
lemma map₀_apply (f : ∀ i, V' i →ₗ[k] V i) (w : ∀ i, W i →ₗ[k] W' i) (h : Cochain₀ k V W)
    (i : I) : map₀ f w h i = w i ∘ₗ h i ∘ₗ f i :=
  rfl

/-- Composition on both sides of a one-cochain: `c ↦ w ∘ c ∘ f` at each arrow. -/
def map₁ (f : ∀ i, V' i →ₗ[k] V i) (w : ∀ i, W i →ₗ[k] W' i) :
    Cochain₁ k Q V W →ₗ[k] Cochain₁ k Q V' W' where
  toFun c := (fun i j a ↦ w j ∘ₗ c.1 i j a ∘ₗ f i, fun i j a ↦ w i ∘ₗ c.2 i j a ∘ₗ f j)
  map_add' c c' := by
    refine Prod.ext (funext fun i ↦ funext fun j ↦ funext fun a ↦ ?_)
      (funext fun i ↦ funext fun j ↦ funext fun a ↦ ?_) <;>
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, LinearMap.add_comp, LinearMap.comp_add]
  map_smul' c h := by
    refine Prod.ext (funext fun i ↦ funext fun j ↦ funext fun a ↦ ?_)
      (funext fun i ↦ funext fun j ↦ funext fun a ↦ ?_) <;>
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, LinearMap.smul_comp,
      LinearMap.comp_smul, RingHom.id_apply]

@[simp]
lemma map₁_apply_fst (f : ∀ i, V' i →ₗ[k] V i) (w : ∀ i, W i →ₗ[k] W' i)
    (c : Cochain₁ k Q V W) (i j : I) (a : Q i j) :
    (map₁ f w c).1 i j a = w j ∘ₗ c.1 i j a ∘ₗ f i :=
  rfl

@[simp]
lemma map₁_apply_snd (f : ∀ i, V' i →ₗ[k] V i) (w : ∀ i, W i →ₗ[k] W' i)
    (c : Cochain₁ k Q V W) (i j : I) (a : Q i j) :
    (map₁ f w c).2 i j a = w i ∘ₗ c.2 i j a ∘ₗ f j :=
  rfl

variable {X : DoubledRep k Q V} {Y : DoubledRep k Q W} {X' : DoubledRep k Q V'}
  {Y' : DoubledRep k Q W'} {f : ∀ i, V' i →ₗ[k] V i} {w : ∀ i, W i →ₗ[k] W' i}

/-- Composition with morphisms commutes with the degree-zero differential. -/
theorem d₀_map₀ (hf : f ∈ Hom X' X) (hw : w ∈ Hom Y Y') (h : Cochain₀ k V W) :
    d₀ X' Y' (map₀ f w h) = map₁ f w (d₀ X Y h) := by
  have hw₁ : ∀ i j (a : Q i j) y, w j (Y.A a y) = Y'.A a (w i y) := fun i j a ↦
    LinearMap.congr_fun (hw i j a).1
  have hw₂ : ∀ i j (a : Q i j) y, w i (Y.B a y) = Y'.B a (w j y) := fun i j a ↦
    LinearMap.congr_fun (hw i j a).2
  have hf₁ : ∀ i j (a : Q i j) x, f j (X'.A a x) = X.A a (f i x) := fun i j a ↦
    LinearMap.congr_fun (hf i j a).1
  have hf₂ : ∀ i j (a : Q i j) x, f i (X'.B a x) = X.B a (f j x) := fun i j a ↦
    LinearMap.congr_fun (hf i j a).2
  refine Prod.ext (funext fun i ↦ funext fun j ↦ funext fun a ↦ LinearMap.ext fun x ↦ ?_)
    (funext fun i ↦ funext fun j ↦ funext fun a ↦ LinearMap.ext fun x ↦ ?_) <;>
  simp only [d₀_apply_fst, d₀_apply_snd, map₀_apply, map₁_apply_fst, map₁_apply_snd,
    LinearMap.sub_apply, LinearMap.comp_apply, map_sub, hw₁, hw₂, hf₁, hf₂]

/-- Composition with morphisms commutes with the degree-one differential. -/
theorem d₁_map₁ [Fintype I] [∀ i j, Fintype (Q i j)] (hf : f ∈ Hom X' X) (hw : w ∈ Hom Y Y')
    (c : Cochain₁ k Q V W) : d₁ X' Y' (map₁ f w c) = map₀ f w (d₁ X Y c) := by
  have hw₁ : ∀ i j (a : Q i j) y, Y'.A a (w i y) = w j (Y.A a y) := fun i j a y ↦
    (LinearMap.congr_fun (hw i j a).1 y).symm
  have hw₂ : ∀ i j (a : Q i j) y, Y'.B a (w j y) = w i (Y.B a y) := fun i j a y ↦
    (LinearMap.congr_fun (hw i j a).2 y).symm
  have hf₁ : ∀ i j (a : Q i j) x, f j (X'.A a x) = X.A a (f i x) := fun i j a ↦
    LinearMap.congr_fun (hf i j a).1
  have hf₂ : ∀ i j (a : Q i j) x, f i (X'.B a x) = X.B a (f j x) := fun i j a ↦
    LinearMap.congr_fun (hf i j a).2
  refine funext fun i ↦ LinearMap.ext fun x ↦ ?_
  simp only [d₁_apply, map₀_apply, map₁_apply_fst, map₁_apply_snd, LinearMap.sub_apply,
    LinearMap.sum_apply, LinearMap.add_apply, LinearMap.comp_apply, map_sum, map_add, map_sub,
    hw₁, hw₂, hf₁, hf₂]

lemma map₁_mem_cocycles [Fintype I] [∀ i j, Fintype (Q i j)] (hf : f ∈ Hom X' X)
    (hw : w ∈ Hom Y Y') {c : Cochain₁ k Q V W} (hc : c ∈ cocycles X Y) :
    map₁ f w c ∈ cocycles X' Y' := by
  rw [mem_cocycles] at hc ⊢
  rw [d₁_map₁ hf hw, hc, map_zero]

lemma map₁_mem_coboundaries (hf : f ∈ Hom X' X) (hw : w ∈ Hom Y Y')
    {c : Cochain₁ k Q V W} (hc : c ∈ coboundaries X Y) : map₁ f w c ∈ coboundaries X' Y' := by
  obtain ⟨h, rfl⟩ := hc
  exact ⟨map₀ f w h, d₀_map₀ hf hw h⟩

end Functoriality

/-! ### The dimension of `Ext¹` -/

section Dimension

variable [Fintype I] [∀ i j, Fintype (Q i j)]

/-- The trace pairing `(f, g) ↦ tr(f g)` of maps `V → W` and `W → V` is nondegenerate. -/
lemma eq_zero_of_forall_trace_comp_eq_zero {V W : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    {f : V →ₗ[k] W} (h : ∀ g : W →ₗ[k] V, LinearMap.trace k W (f ∘ₗ g) = 0) : f = 0 := by
  refine LinearMap.ext fun x ↦ (Module.forall_dual_apply_eq_zero_iff k (f x)).mp fun φ ↦ ?_
  have hφ := h (φ.smulRight x)
  rwa [show f ∘ₗ φ.smulRight x = φ.smulRight (f x) from LinearMap.ext fun y ↦ by simp,
    LinearMap.trace_smulRight] at hφ

variable (k Q V W)

/-- The trace pairing between one-cochains of `(X, Y)` and of `(Y, X)`,
`⟨c, c'⟩ = ∑_{a : i → j} tr(c_a c'_{a*}) - tr(c_{a*} c'_a)`. -/
noncomputable def tracePairing₁ : Cochain₁ k Q V W →ₗ[k] Module.Dual k (Cochain₁ k Q W V) :=
  LinearMap.mk₂ k (fun c c' ↦ ∑ i, ∑ j, ∑ a : Q i j,
      (LinearMap.trace k (W j) (c.1 i j a ∘ₗ c'.2 i j a) -
        LinearMap.trace k (W i) (c.2 i j a ∘ₗ c'.1 i j a)))
    (fun c c' c'' ↦ by
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, LinearMap.add_comp, map_add,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
        Finset.sum_congr rfl fun a _ ↦ by ring)
    (fun r c c' ↦ by
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, LinearMap.smul_comp, map_smul,
        smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
        Finset.sum_congr rfl fun a _ ↦ by ring)
    (fun c c' c'' ↦ by
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, LinearMap.comp_add, map_add,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
        Finset.sum_congr rfl fun a _ ↦ by ring)
    (fun r c c' ↦ by
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, LinearMap.comp_smul, map_smul,
        smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
        Finset.sum_congr rfl fun a _ ↦ by ring)

lemma tracePairing₁_apply (c : Cochain₁ k Q V W) (c' : Cochain₁ k Q W V) :
    tracePairing₁ k Q V W c c' = ∑ i, ∑ j, ∑ a : Q i j,
      (LinearMap.trace k (W j) (c.1 i j a ∘ₗ c'.2 i j a) -
        LinearMap.trace k (W i) (c.2 i j a ∘ₗ c'.1 i j a)) :=
  rfl

/-- The trace pairing between two-cochains of `(X, Y)` and zero-cochains of `(Y, X)`,
`⟨z, h⟩ = ∑_i tr(z_i h_i)`. -/
noncomputable def tracePairing₀ : Cochain₀ k V W →ₗ[k] Module.Dual k (Cochain₀ k W V) :=
  LinearMap.mk₂ k (fun z h ↦ ∑ i, LinearMap.trace k (W i) (z i ∘ₗ h i))
    (fun z z' h ↦ by
      simp only [Pi.add_apply, LinearMap.add_comp, map_add, Finset.sum_add_distrib])
    (fun r z h ↦ by
      simp only [Pi.smul_apply, LinearMap.smul_comp, map_smul, smul_eq_mul, Finset.mul_sum])
    (fun z h h' ↦ by
      simp only [Pi.add_apply, LinearMap.comp_add, map_add, Finset.sum_add_distrib])
    (fun r z h ↦ by
      simp only [Pi.smul_apply, LinearMap.comp_smul, map_smul, smul_eq_mul, Finset.mul_sum])

lemma tracePairing₀_apply (z : Cochain₀ k V W) (h : Cochain₀ k W V) :
    tracePairing₀ k V W z h = ∑ i, LinearMap.trace k (W i) (z i ∘ₗ h i) :=
  rfl

variable {k Q V W}

private lemma sum_comp {U U' U'' : Type*} [AddCommGroup U] [Module k U] [AddCommGroup U']
    [Module k U'] [AddCommGroup U''] [Module k U''] {ι : Type*} (s : Finset ι)
    (F : ι → U' →ₗ[k] U'') (G : U →ₗ[k] U') : (∑ i ∈ s, F i) ∘ₗ G = ∑ i ∈ s, F i ∘ₗ G :=
  LinearMap.ext fun x ↦ by simp [LinearMap.sum_apply]

variable [∀ i, FiniteDimensional k (W i)]

lemma tracePairing₀_injective : Function.Injective (tracePairing₀ k V W) := by
  classical
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro z hz
  rw [LinearMap.mem_ker] at hz
  refine funext fun i ↦ eq_zero_of_forall_trace_comp_eq_zero fun g ↦ ?_
  have := LinearMap.congr_fun hz (Pi.single i g)
  rw [tracePairing₀_apply, Finset.sum_eq_single i
    (fun j _ hj ↦ by simp [Pi.single_eq_of_ne hj]) (by simp)] at this
  simpa using this

lemma tracePairing₁_injective : Function.Injective (tracePairing₁ k Q V W) := by
  classical
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro c hc
  rw [LinearMap.mem_ker] at hc
  refine Prod.ext (funext fun i ↦ funext fun j ↦ funext fun a ↦
      eq_zero_of_forall_trace_comp_eq_zero fun g ↦ ?_)
    (funext fun i ↦ funext fun j ↦ funext fun a ↦
      eq_zero_of_forall_trace_comp_eq_zero fun g ↦ ?_)
  · have := LinearMap.congr_fun hc (0, Pi.single i (Pi.single j (Pi.single a g)))
    rw [tracePairing₁_apply, Finset.sum_eq_single i
        (fun i' _ hi' ↦ by simp [Pi.single_eq_of_ne hi']) (by simp),
      Finset.sum_eq_single j (fun j' _ hj' ↦ by simp [Pi.single_eq_of_ne hj']) (by simp),
      Finset.sum_eq_single a (fun a' _ ha' ↦ by simp [Pi.single_eq_of_ne ha']) (by simp)] at this
    simpa using this
  · have := LinearMap.congr_fun hc (Pi.single i (Pi.single j (Pi.single a g)), 0)
    rw [tracePairing₁_apply, Finset.sum_eq_single i
        (fun i' _ hi' ↦ by simp [Pi.single_eq_of_ne hi']) (by simp),
      Finset.sum_eq_single j (fun j' _ hj' ↦ by simp [Pi.single_eq_of_ne hj']) (by simp),
      Finset.sum_eq_single a (fun a' _ ha' ↦ by simp [Pi.single_eq_of_ne ha']) (by simp)] at this
    simpa using this

/-- The dimension of the one-cochains of `(X, Y)`. -/
lemma finrank_cochain₁ [∀ i, FiniteDimensional k (V i)] :
    finrank k (Cochain₁ k Q V W) = ∑ i, ∑ j, Fintype.card (Q i j) *
      (finrank k (V i) * finrank k (W j) + finrank k (V j) * finrank k (W i)) := by
  simp only [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_linearMap,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Finset.sum_add_distrib, mul_add]

/-- The dimension of the zero-cochains of `(X, Y)`. -/
lemma finrank_cochain₀ [∀ i, FiniteDimensional k (V i)] :
    finrank k (Cochain₀ k V W) = ∑ i, finrank k (V i) * finrank k (W i) := by
  simp only [Module.finrank_pi_fintype, Module.finrank_linearMap]

lemma tracePairing₁_surjective [∀ i, FiniteDimensional k (V i)] :
    Function.Surjective (tracePairing₁ k Q V W) := by
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp tracePairing₁_injective
  rw [Subspace.dual_finrank_eq, finrank_cochain₁, finrank_cochain₁]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  ring

/-- **The duality of the two differentials.** Under the trace pairings, `d₁` of `(X, Y)` is the
transpose of `d₀` of `(Y, X)`. This is the Calabi–Yau symmetry of the complex. -/
theorem dualMap_d₀_comp_tracePairing₁ (X : DoubledRep k Q V) (Y : DoubledRep k Q W) :
    (d₀ Y X).dualMap ∘ₗ tracePairing₁ k Q V W = tracePairing₀ k V W ∘ₗ d₁ X Y := by
  refine LinearMap.ext fun c ↦ LinearMap.ext fun h ↦ ?_
  have e₁ : ∀ i j (a : Q i j), LinearMap.trace k (W j) (c.1 i j a ∘ₗ h i ∘ₗ Y.B a) =
      LinearMap.trace k (W i) (Y.B a ∘ₗ c.1 i j a ∘ₗ h i) := fun i j a ↦ by
    rw [← LinearMap.comp_assoc, LinearMap.trace_comp_comm']
  have e₂ : ∀ i j (a : Q i j), LinearMap.trace k (W i) (c.2 i j a ∘ₗ h j ∘ₗ Y.A a) =
      LinearMap.trace k (W j) (Y.A a ∘ₗ c.2 i j a ∘ₗ h j) := fun i j a ↦ by
    rw [← LinearMap.comp_assoc, LinearMap.trace_comp_comm']
  simp only [LinearMap.comp_apply, LinearMap.dualMap_apply, tracePairing₁_apply,
    tracePairing₀_apply, d₀_apply_fst, d₀_apply_snd, d₁_apply, LinearMap.comp_sub,
    LinearMap.sub_comp, sum_comp, LinearMap.add_comp, LinearMap.comp_assoc, map_sub, map_sum,
    map_add, e₁, e₂]
  rw [Finset.sum_sub_distrib, Finset.sum_comm (f := fun i j ↦ ∑ a : Q j i, _)]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  ring

/-- `rank d₁(X, Y) = rank d₀(Y, X)`. -/
theorem finrank_range_d₁ [∀ i, FiniteDimensional k (V i)] (X : DoubledRep k Q V)
    (Y : DoubledRep k Q W) :
    finrank k (LinearMap.range (d₁ X Y)) = finrank k (LinearMap.range (d₀ Y X)) := by
  rw [← LinearMap.finrank_range_dualMap_eq_finrank_range (d₀ Y X),
    ← LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr tracePairing₁_surjective),
    dualMap_d₀_comp_tracePairing₁, LinearMap.range_comp]
  exact (Submodule.equivMapOfInjective _ tracePairing₀_injective _).finrank_eq

variable [∀ i, FiniteDimensional k (V i)]

/-- **Crawley-Boevey's formula**, in natural numbers: for representations `X`, `Y` with the
preprojective relations, `dim Ext¹(X, Y) + 2 ∑_i x_i y_i` equals
`∑_{a : i → j} (x_i y_j + x_j y_i) + dim Hom(X, Y) + dim Hom(Y, X)`. -/
theorem finrank_Ext1 {X : DoubledRep k Q V} {Y : DoubledRep k Q W} (hX : X.IsPreprojective)
    (hY : Y.IsPreprojective) :
    finrank k (Ext1 X Y) + 2 * ∑ i, finrank k (V i) * finrank k (W i) =
      ∑ i, ∑ j, Fintype.card (Q i j) *
        (finrank k (V i) * finrank k (W j) + finrank k (V j) * finrank k (W i)) +
        finrank k (Hom X Y) + finrank k (Hom Y X) := by
  have e₁ : finrank k (Ext1 X Y) + finrank k (coboundaries X Y) =
      finrank k (cocycles X Y) := by
    rw [← Submodule.finrank_quotient_add_finrank
      ((coboundaries X Y).comap (cocycles X Y).subtype)]
    congr 1
    exact (Submodule.comapSubtypeEquivOfLe (coboundaries_le_cocycles hX hY)).finrank_eq.symm
  have e₂ : finrank k (LinearMap.range (d₁ X Y)) + finrank k (cocycles X Y) =
      finrank k (Cochain₁ k Q V W) :=
    LinearMap.finrank_range_add_finrank_ker _
  have e₃ : finrank k (coboundaries X Y) + finrank k (Hom X Y) =
      finrank k (Cochain₀ k V W) := by
    rw [← ker_d₀]
    exact LinearMap.finrank_range_add_finrank_ker _
  have e₄ : finrank k (LinearMap.range (d₀ Y X)) + finrank k (Hom Y X) =
      finrank k (Cochain₀ k W V) := by
    rw [← ker_d₀]
    exact LinearMap.finrank_range_add_finrank_ker _
  have e₅ := finrank_range_d₁ X Y
  rw [finrank_cochain₁] at e₂
  rw [finrank_cochain₀] at e₃ e₄
  have e₆ : ∑ i, finrank k (W i) * finrank k (V i) = ∑ i, finrank k (V i) * finrank k (W i) :=
    Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
  rw [e₆] at e₄
  omega

/-- **Crawley-Boevey's formula**, `dim Ext¹(X, Y) = dim Hom(X, Y) + dim Hom(Y, X) - (x, y)` with
`(x, y)` the symmetric Euler form of `Q` (Crawley-Boevey, Amer. J. Math. 122 (2000), Lemma 1). -/
theorem finrank_Ext1_eq {X : DoubledRep k Q V} {Y : DoubledRep k Q W} (hX : X.IsPreprojective)
    (hY : Y.IsPreprojective) :
    (finrank k (Ext1 X Y) : ℤ) = finrank k (Hom X Y) + finrank k (Hom Y X) -
      eulerForm Q (fun i ↦ (finrank k (V i) : ℤ)) (fun i ↦ (finrank k (W i) : ℤ)) := by
  have h := finrank_Ext1 hX hY
  zify at h
  simp only [eulerForm]
  rw [Finset.mul_sum] at h
  have e : ∑ i, (2 : ℤ) * (finrank k (V i) * finrank k (W i)) =
      ∑ i, 2 * (finrank k (V i) : ℤ) * finrank k (W i) :=
    Finset.sum_congr rfl fun i _ ↦ by ring
  rw [e] at h
  linear_combination h

end Dimension

/-! ### Self-extensions -/

section SelfExt

variable [Fintype I] [∀ i j, Fintype (Q i j)] [∀ i, FiniteDimensional k (V i)]

/-- `e(X) = dim Ext¹(X, X)`, the dimension of the self-extensions of a representation. -/
noncomputable def selfExtDim (X : DoubledRep k Q V) : ℕ :=
  finrank k (Ext1 X X)

/-- **Riemann–Roch in the model**: `e(X) = 2 dim End X - 2 q(x)`, with `q` the Tits form of `Q`;
in Mukai's notation `e = 2 dim End + v²`. -/
theorem selfExtDim_eq {X : DoubledRep k Q V} (hX : X.IsPreprojective) :
    (selfExtDim X : ℤ) =
      2 * finrank k (Hom X X) - 2 * titsForm Q (fun i ↦ (finrank k (V i) : ℤ)) := by
  rw [selfExtDim, finrank_Ext1_eq hX hX, eulerForm_self]
  ring

/-- `e` is even. -/
theorem even_selfExtDim {X : DoubledRep k Q V} (hX : X.IsPreprojective) :
    Even (selfExtDim X) := by
  rw [← Int.even_natCast, selfExtDim_eq hX]
  exact ⟨finrank k (Hom X X) - titsForm Q (fun i ↦ (finrank k (V i) : ℤ)), by ring⟩

/-- For a brick, `End X = k`, Riemann–Roch reads `e(X) = 2 - 2 q(x)`. -/
theorem selfExtDim_eq_of_brick {X : DoubledRep k Q V} (hX : X.IsPreprojective)
    (hb : finrank k (Hom X X) = 1) :
    (selfExtDim X : ℤ) = 2 - 2 * titsForm Q (fun i ↦ (finrank k (V i) : ℤ)) := by
  rw [selfExtDim_eq hX, hb]
  norm_num

/-- A brick has `q(x) ≤ 1`. -/
theorem titsForm_le_one_of_brick {X : DoubledRep k Q V} (hX : X.IsPreprojective)
    (hb : finrank k (Hom X X) = 1) : titsForm Q (fun i ↦ (finrank k (V i) : ℤ)) ≤ 1 := by
  have h := selfExtDim_eq_of_brick hX hb
  have := (selfExtDim X).cast_nonneg (α := ℤ)
  omega

/-- A brick is rigid exactly when `q(x) = 1`, a real root. -/
theorem selfExtDim_eq_zero_iff_of_brick {X : DoubledRep k Q V} (hX : X.IsPreprojective)
    (hb : finrank k (Hom X X) = 1) :
    selfExtDim X = 0 ↔ titsForm Q (fun i ↦ (finrank k (V i) : ℤ)) = 1 := by
  have h := selfExtDim_eq_of_brick hX hb
  omega

/-- A brick has `e = 2` exactly when `q(x) = 0`, an isotropic root. -/
theorem selfExtDim_eq_two_iff_of_brick {X : DoubledRep k Q V} (hX : X.IsPreprojective)
    (hb : finrank k (Hom X X) = 1) :
    selfExtDim X = 2 ↔ titsForm Q (fun i ↦ (finrank k (V i) : ℤ)) = 0 := by
  have h := selfExtDim_eq_of_brick hX hb
  omega

/-- **Rigid and semirigid bricks**: a brick with `e ≤ 2` has `q = 1` (rigid) or `q = 0`
(`e = 2`). -/
theorem titsForm_eq_one_or_eq_zero_of_brick {X : DoubledRep k Q V} (hX : X.IsPreprojective)
    (hb : finrank k (Hom X X) = 1) (he : selfExtDim X ≤ 2) :
    titsForm Q (fun i ↦ (finrank k (V i) : ℤ)) = 1 ∨
      titsForm Q (fun i ↦ (finrank k (V i) : ℤ)) = 0 := by
  have h := selfExtDim_eq_of_brick hX hb
  have h' := even_selfExtDim hX
  obtain ⟨m, hm⟩ := h'
  omega

end SelfExt

/-! ### Invariance under isomorphism -/

section IsoInvariance

variable [Fintype I] [∀ i j, Fintype (Q i j)] {V' : I → Type*} [∀ i, AddCommGroup (V' i)]
  [∀ i, Module k (V' i)] {X : DoubledRep k Q V} {X' : DoubledRep k Q V'}

/-- The map `Ext¹(X, X) → Ext¹(X', X')`, `c ↦ u c u⁻¹`, of an isomorphism `u : X ≅ X'`. -/
noncomputable def Iso.extMap (u : Iso X X') : Ext1 X X →ₗ[k] Ext1 X' X' :=
  Submodule.mapQ _ _
    ((map₁ (fun i ↦ (u.symm.e i : V' i →ₗ[k] V i)) (fun i ↦ (u.e i : V i →ₗ[k] V' i))).restrict
      fun _ hc ↦ map₁_mem_cocycles u.symm.mem_Hom u.mem_Hom hc)
    fun _ hc ↦ map₁_mem_coboundaries u.symm.mem_Hom u.mem_Hom hc

theorem Iso.extMap_symm_extMap (u : Iso X X') (x : Ext1 X X) :
    u.symm.extMap (u.extMap x) = x := by
  induction x using Submodule.Quotient.induction_on with
  | H c =>
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    congr 1
    refine Subtype.ext (Prod.ext (funext fun i ↦ funext fun j ↦ funext fun a ↦ ?_)
      (funext fun i ↦ funext fun j ↦ funext fun a ↦ ?_)) <;>
    · refine LinearMap.ext fun x ↦ ?_
      simp [Iso.symm]

theorem Iso.selfExtDim_le [∀ i, FiniteDimensional k (V i)] [∀ i, FiniteDimensional k (V' i)]
    (u : Iso X X') : selfExtDim X ≤ selfExtDim X' :=
  LinearMap.finrank_le_finrank_of_injective
    (f := u.extMap) fun x y h ↦ by
      rw [← u.extMap_symm_extMap x, ← u.extMap_symm_extMap y, h]

/-- Isomorphic representations have the same `e`. -/
theorem Iso.selfExtDim_eq [∀ i, FiniteDimensional k (V i)] [∀ i, FiniteDimensional k (V' i)]
    (u : Iso X X') : selfExtDim X = selfExtDim X' :=
  le_antisymm u.selfExtDim_le u.symm.selfExtDim_le

end IsoInvariance

end DoubledRep

end Quiver.Preprojective
