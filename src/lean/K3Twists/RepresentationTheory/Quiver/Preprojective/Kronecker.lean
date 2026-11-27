/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.RepresentationTheory.Quiver.Preprojective.Budget
import K3Twists.RepresentationTheory.Quiver.Kronecker.Budget
import K3Twists.RepresentationTheory.Quiver.Kronecker.TwoExtensions

/-!
# The Kronecker files as instances of the general wall model

A wall with two stable objects `S`, `U` and `g = ext¹(S, U)` has the half `Ext`-quiver
`wallArrow ι L` on the vertices `false` (for `S`) and `true` (for `U`): the arrows `ι`, `|ι| = g`,
from `false` to `true`, and `L` loops at `true`, with `2|L| = ext¹(U, U)`. The doubled Kronecker
files are the two cases used by the notes:

* **Two spheres** (`L` empty): a representation of the doubled `ι`-Kronecker quiver
  (`Quiver.Kronecker.DoubledRep`) is a representation of the double of `wallArrow ι PEmpty`
  (`Quiver.Preprojective.DoubledRep.ofKronecker`). The preprojective relations, the morphisms,
  the subrepresentations with their dimension vectors and `e = dim Ext¹(M, M)` agree
  (`isPreprojective_ofKronecker_iff`, `finrank_Hom_ofKronecker`, `ofKroneckerSubrepsIso`,
  `selfExtDim_ofKronecker`). In particular the rigid representation of dimension `(g², g)` is
  rigid in the general model (`selfExtDim_ofKronecker_rigidRep`).
* **A sphere and an isotropic object** (`L` one loop): the wall group that carries the point. The
  Kronecker file models a wall object in which `U` occurs once on the line `k` at vertex `true`,
  where the two loops act by commuting scalars. In the general model with the loop, Crawley-Boevey's
  formula reads `e(M) = 2 dim End M - 2 (p² - g p)` (`selfExtDim_pointWall`), so the hypothesis
  `dim End M + p(g - p) = 1` of the lemma on the wall group that carries the point is exactly
  `e(M) = 2` in the model with the loop, and the lemma holds for every preprojective
  representation of the wall quiver with the loop and dimension vector `(p, 1)`
  (`twoExtensions_of_selfExtDim_eq_two`). The loops need no vanishing hypothesis: on a line they
  commute, so the relation at `true` is the Kronecker relation.

So the Kronecker files are the case of two vertices of the general model, with the Ext of the
general complex. This is the bridge of `twoExtensions` and `rigidRep` to the general model.
-/

namespace Quiver.Preprojective

open Module

universe u

/-- The half `Ext`-quiver of a wall with two stable objects: the arrows `ι` from `false` to
`true`, the loops `L` at `true`, and no other arrows. -/
def wallArrow (ι L : Type u) : Bool → Bool → Type u
  | false, true => ι
  | true, true => L
  | _, _ => PEmpty

instance (ι L : Type u) [Fintype ι] [Fintype L] : ∀ i j, Fintype (wallArrow ι L i j)
  | false, true => show Fintype ι from inferInstance
  | true, true => show Fintype L from inferInstance
  | false, false => show Fintype PEmpty from inferInstance
  | true, false => show Fintype PEmpty from inferInstance

instance (ι L : Type u) : IsEmpty (wallArrow ι L false false) :=
  show IsEmpty PEmpty from inferInstance

instance (ι L : Type u) : IsEmpty (wallArrow ι L true false) :=
  show IsEmpty PEmpty from inferInstance

lemma card_wallArrow_false_true (ι L : Type u) [Fintype ι] [Fintype L] :
    Fintype.card (wallArrow ι L false true) = Fintype.card ι :=
  rfl

lemma card_wallArrow_true_true (ι L : Type u) [Fintype ι] [Fintype L] :
    Fintype.card (wallArrow ι L true true) = Fintype.card L :=
  rfl

/-- The vertex spaces `V₀` at `false` and `V₁` at `true`. -/
def kroneckerSpace (V₀ V₁ : Type u) : Bool → Type u
  | false => V₀
  | true => V₁

instance (V₀ V₁ : Type u) [AddCommGroup V₀] [AddCommGroup V₁] :
    ∀ i, AddCommGroup (kroneckerSpace V₀ V₁ i)
  | false => show AddCommGroup V₀ from inferInstance
  | true => show AddCommGroup V₁ from inferInstance

instance (k V₀ V₁ : Type u) [Field k] [AddCommGroup V₀] [Module k V₀] [AddCommGroup V₁]
    [Module k V₁] : ∀ i, Module k (kroneckerSpace V₀ V₁ i)
  | false => show Module k V₀ from inferInstance
  | true => show Module k V₁ from inferInstance

instance (k V₀ V₁ : Type u) [Field k] [AddCommGroup V₀] [Module k V₀] [AddCommGroup V₁]
    [Module k V₁] [FiniteDimensional k V₀] [FiniteDimensional k V₁] :
    ∀ i, FiniteDimensional k (kroneckerSpace V₀ V₁ i)
  | false => show FiniteDimensional k V₀ from inferInstance
  | true => show FiniteDimensional k V₁ from inferInstance

variable {k ι L V₀ V₁ : Type u} [Field k] [AddCommGroup V₀] [Module k V₀] [AddCommGroup V₁]
  [Module k V₁]

namespace DoubledRep

/-! ### The Kronecker part of a representation of the wall quiver -/

/-- The Kronecker part of a representation of the double of the wall quiver: the arrows `ι` and
their reverses, forgetting the loops. -/
def toKronecker (M : DoubledRep k (wallArrow ι L) (kroneckerSpace V₀ V₁)) :
    Kronecker.DoubledRep k ι V₀ V₁ where
  A i := M.A (i := false) (j := true) i
  B i := M.B (i := false) (j := true) i

section Sums

variable [Fintype ι] [Fintype L] {N : Type*} [AddCommMonoid N]

lemma sum_bool (f : Bool → N) : ∑ i, f i = f false + f true :=
  Fintype.sum_bool f |>.trans (add_comm _ _)

lemma sum_wallArrow_false_false (f : wallArrow ι L false false → N) : ∑ a, f a = 0 :=
  Finset.sum_of_isEmpty _

lemma sum_wallArrow_true_false (f : wallArrow ι L true false → N) : ∑ a, f a = 0 :=
  Finset.sum_of_isEmpty _

end Sums

variable [Fintype ι] [Fintype L]

/-- The relation at `false` of a representation of the wall quiver is `-∑ B_i A_i`. -/
lemma relation_false (M : DoubledRep k (wallArrow ι L) (kroneckerSpace V₀ V₁)) :
    M.relation false =
      -∑ i : ι, M.B (i := false) (j := true) i ∘ₗ M.A (i := false) (j := true) i := by
  simp only [relation, sum_bool, sum_wallArrow_false_false, sum_wallArrow_true_false, zero_add,
    add_zero, zero_sub]
  rfl

/-- The relation at `true`: `∑ A_i B_i` plus the commutators of the loops. -/
lemma relation_true (M : DoubledRep k (wallArrow ι L) (kroneckerSpace V₀ V₁)) :
    M.relation true =
      ∑ i : ι, M.A (i := false) (j := true) i ∘ₗ M.B (i := false) (j := true) i +
        ∑ l : L, (M.A (i := true) (j := true) l ∘ₗ M.B (i := true) (j := true) l -
          M.B (i := true) (j := true) l ∘ₗ M.A (i := true) (j := true) l) := by
  simp only [relation, sum_bool, sum_wallArrow_true_false, zero_add, Finset.sum_sub_distrib]
  rw [add_sub_assoc]
  rfl

/-! ### Two spheres: the doubled Kronecker quiver -/

section TwoSpheres

/-- A representation of the doubled `ι`-Kronecker quiver as a representation of the double of
the wall quiver with no loops. -/
def ofKronecker (M : Kronecker.DoubledRep k ι V₀ V₁) :
    DoubledRep k (wallArrow ι PEmpty) (kroneckerSpace V₀ V₁) where
  A {i j} a := match i, j, a with
    | false, true, a => M.A a
    | true, true, a => PEmpty.elim a
    | false, false, a => PEmpty.elim a
    | true, false, a => PEmpty.elim a
  B {i j} a := match i, j, a with
    | false, true, a => M.B a
    | true, true, a => PEmpty.elim a
    | false, false, a => PEmpty.elim a
    | true, false, a => PEmpty.elim a

omit [Fintype ι] [Fintype L] in
@[simp]
lemma toKronecker_ofKronecker (M : Kronecker.DoubledRep k ι V₀ V₁) :
    (ofKronecker M).toKronecker = M :=
  rfl

omit [Fintype L] in
/-- **The relations agree.** -/
theorem isPreprojective_ofKronecker_iff (M : Kronecker.DoubledRep k ι V₀ V₁) :
    (ofKronecker M).IsPreprojective ↔ M.IsPreprojective := by
  have hf := relation_false (ofKronecker M)
  have ht := relation_true (ofKronecker M)
  simp only [Fintype.sum_empty, add_zero] at ht
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := h false
      rw [hf, neg_eq_zero] at this
      exact this
    · have := h true
      rw [ht] at this
      exact this
  · rintro ⟨h₀, h₁⟩ i
    cases i
    · rw [hf]
      exact neg_eq_zero.mpr h₀
    · rw [ht]
      exact h₁

variable {W₀ W₁ : Type u} [AddCommGroup W₀] [Module k W₀] [AddCommGroup W₁] [Module k W₁]

/-- The cochains of the general complex at the two vertices, as pairs. -/
def cochainEquiv :
    (∀ i, kroneckerSpace V₀ V₁ i →ₗ[k] kroneckerSpace W₀ W₁ i) ≃ₗ[k]
      (V₀ →ₗ[k] W₀) × (V₁ →ₗ[k] W₁) where
  toFun f := (f false, f true)
  invFun f i := match i with
    | false => f.1
    | true => f.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := funext fun i ↦ by cases i <;> rfl
  right_inv _ := rfl

omit [Fintype ι] [Fintype L] in
/-- **The morphisms agree.** -/
theorem map_cochainEquiv_Hom (M : Kronecker.DoubledRep k ι V₀ V₁)
    (N : Kronecker.DoubledRep k ι W₀ W₁) :
    (Hom (ofKronecker M) (ofKronecker N)).map
        (cochainEquiv (k := k) (V₀ := V₀) (V₁ := V₁) (W₀ := W₀) (W₁ := W₁)).toLinearMap =
      Kronecker.DoubledRep.Hom M N := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩ i
    exact hg false true i
  · intro hf
    refine ⟨cochainEquiv.symm f, ?_, cochainEquiv.apply_symm_apply f⟩
    intro i j a
    match i, j, a with
    | false, true, a => exact hf a
    | true, true, a => exact PEmpty.elim a
    | false, false, a => exact PEmpty.elim a
    | true, false, a => exact PEmpty.elim a

omit [Fintype ι] [Fintype L] in
theorem finrank_Hom_ofKronecker (M : Kronecker.DoubledRep k ι V₀ V₁)
    (N : Kronecker.DoubledRep k ι W₀ W₁) :
    finrank k (Hom (ofKronecker M) (ofKronecker N)) = finrank k (Kronecker.DoubledRep.Hom M N) := by
  rw [← map_cochainEquiv_Hom M N]
  exact (Submodule.equivMapOfInjective _ cochainEquiv.injective _).finrank_eq

omit [Fintype ι] [Fintype L] in
/-- **The subrepresentations agree**, with their dimension vectors
(`dimVec_ofKroneckerSubrepsIso`). -/
def ofKroneckerSubrepsIso (M : Kronecker.DoubledRep k ι V₀ V₁) :
    (ofKronecker M).subreps ≃o M.subreps where
  toFun P := ⟨((P : ∀ i, Submodule k (kroneckerSpace V₀ V₁ i)) false,
      (P : ∀ i, Submodule k (kroneckerSpace V₀ V₁ i)) true), fun i ↦ P.2 false true i⟩
  invFun P := ⟨fun i ↦ match i with
      | false => (P : Submodule k V₀ × Submodule k V₁).1
      | true => (P : Submodule k V₀ × Submodule k V₁).2, fun i j a ↦ match i, j, a with
      | false, true, a => P.2 a
      | true, true, a => PEmpty.elim a
      | false, false, a => PEmpty.elim a
      | true, false, a => PEmpty.elim a⟩
  left_inv P := Subtype.ext (funext fun i ↦ by cases i <;> rfl)
  right_inv _ := rfl
  map_rel_iff' {P P'} := by
    change ((P : ∀ i, Submodule k (kroneckerSpace V₀ V₁ i)) false ≤
        (P' : ∀ i, Submodule k (kroneckerSpace V₀ V₁ i)) false ∧
      (P : ∀ i, Submodule k (kroneckerSpace V₀ V₁ i)) true ≤
        (P' : ∀ i, Submodule k (kroneckerSpace V₀ V₁ i)) true) ↔ P ≤ P'
    refine ⟨fun h i ↦ ?_, fun h ↦ ⟨h false, h true⟩⟩
    cases i
    exacts [h.1, h.2]

omit [Fintype ι] [Fintype L] in
lemma dimVec_ofKroneckerSubrepsIso (M : Kronecker.DoubledRep k ι V₀ V₁)
    (P : (ofKronecker M).subreps) :
    Kronecker.DoubledRep.dimVec (ofKroneckerSubrepsIso M P) = (dimVec P false, dimVec P true) :=
  rfl

omit [Fintype L] in
/-- The Tits form of the wall quiver with no loops is `x₀² + x₁² - g x₀ x₁`. -/
lemma titsForm_wallArrow_pEmpty (x : Bool → ℤ) :
    titsForm (wallArrow ι PEmpty) x =
      x false ^ 2 + x true ^ 2 - Fintype.card ι * (x false * x true) := by
  simp only [titsForm, sum_bool]
  rw [Fintype.card_eq_zero (α := wallArrow ι PEmpty false false),
    Fintype.card_eq_zero (α := wallArrow ι PEmpty true false), card_wallArrow_false_true,
    card_wallArrow_true_true, Fintype.card_eq_zero (α := PEmpty)]
  push_cast
  ring

omit [Fintype L] in
/-- **`e` agrees**: the general complex and the Kronecker complex give the same dimension of
`Ext¹(M, M)`, by Crawley-Boevey's formula on both sides. -/
theorem selfExtDim_ofKronecker [FiniteDimensional k V₀] [FiniteDimensional k V₁]
    {M : Kronecker.DoubledRep k ι V₀ V₁} (hM : M.IsPreprojective) :
    selfExtDim (ofKronecker M) = Kronecker.DoubledRep.selfExtDim M := by
  have h₁ := selfExtDim_eq ((isPreprojective_ofKronecker_iff M).mpr hM)
  have h₂ := Kronecker.DoubledRep.selfExtDim_eq hM
  rw [titsForm_wallArrow_pEmpty, finrank_Hom_ofKronecker] at h₁
  change (selfExtDim (ofKronecker M) : ℤ) = 2 * finrank k (Kronecker.DoubledRep.Hom M M) -
    2 * ((finrank k V₀ : ℤ) ^ 2 + (finrank k V₁ : ℤ) ^ 2 -
      Fintype.card ι * ((finrank k V₀ : ℤ) * finrank k V₁)) at h₁
  have : (selfExtDim (ofKronecker M) : ℤ) = Kronecker.DoubledRep.selfExtDim M := by
    rw [h₁, h₂]
    ring
  exact_mod_cast this

omit [Fintype L] in
/-- **The rigid representation is rigid in the general model**: the representation of dimension
`(g², g)` of `Quiver.Kronecker.rigidRep` has `e = 0` for the general complex of the wall quiver
of two spheres. -/
theorem selfExtDim_ofKronecker_rigidRep [DecidableEq ι] [Nonempty ι] :
    selfExtDim (ofKronecker (Kronecker.rigidRep k ι)) = 0 := by
  have := Kronecker.subsingleton_Ext1_rigidRep (k := k) (ι := ι)
  rw [selfExtDim_ofKronecker (Kronecker.rigidRep_isPreprojective (k := k) (ι := ι)),
    Kronecker.DoubledRep.selfExtDim, Module.finrank_zero_of_subsingleton]

end TwoSpheres

/-! ### A sphere and an isotropic object: the wall group that carries the point -/

section PointWall

variable {V : Type u} [AddCommGroup V] [Module k V]

/-- Linear maps of the line `k` commute. -/
private lemma comm_of_line (f g : k →ₗ[k] k) : f ∘ₗ g = g ∘ₗ f := by
  have hf : ∀ t, f t = t * f 1 := fun t ↦ by rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  have hg : ∀ t, g t = t * g 1 := fun t ↦ by rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  refine LinearMap.ext fun t ↦ ?_
  simp only [LinearMap.comp_apply]
  rw [hf (g t), hg t, hg (f t), hf t]
  ring

/-- On the line `k` at vertex `true` the loops commute, so the relation at `true` is the
Kronecker relation. -/
lemma relation_true_line (M : DoubledRep k (wallArrow ι L) (kroneckerSpace V k)) :
    M.relation true =
      ∑ i : ι, M.A (i := false) (j := true) i ∘ₗ M.B (i := false) (j := true) i := by
  rw [relation_true]
  exact add_eq_left.mpr (Finset.sum_eq_zero fun l _ ↦ sub_eq_zero.mpr (comm_of_line _ _))

/-- **The Kronecker part of a preprojective representation is preprojective** when the vertex
`true` carries a line. -/
theorem isPreprojective_toKronecker {M : DoubledRep k (wallArrow ι L) (kroneckerSpace V k)}
    (hM : M.IsPreprojective) : (M.toKronecker).IsPreprojective := by
  refine ⟨?_, ?_⟩
  · have := hM false
    rw [relation_false, neg_eq_zero] at this
    exact this
  · have := hM true
    rw [relation_true_line] at this
    exact this

omit [Fintype ι] [Fintype L] in
/-- **The morphisms agree** when the vertex `true` carries a line: the loops act by scalars, which
commute with every endomorphism of the line. -/
theorem map_cochainEquiv_Hom_toKronecker (M : DoubledRep k (wallArrow ι L) (kroneckerSpace V k)) :
    (Hom M M).map (cochainEquiv (k := k) (V₀ := V) (V₁ := k) (W₀ := V) (W₁ := k)).toLinearMap =
      Kronecker.DoubledRep.Hom (M.toKronecker) (M.toKronecker) := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩ i
    exact hg false true i
  · intro hf
    refine ⟨cochainEquiv.symm f, ?_, cochainEquiv.apply_symm_apply f⟩
    intro i j a
    match i, j, a with
    | false, true, a => exact hf a
    | true, true, a => exact ⟨comm_of_line _ _, comm_of_line _ _⟩
    | false, false, a => exact PEmpty.elim a
    | true, false, a => exact PEmpty.elim a

omit [Fintype ι] [Fintype L] in
theorem finrank_Hom_toKronecker (M : DoubledRep k (wallArrow ι L) (kroneckerSpace V k)) :
    finrank k (Hom M M) = finrank k (Kronecker.DoubledRep.Hom (M.toKronecker) (M.toKronecker)) := by
  rw [← map_cochainEquiv_Hom_toKronecker M]
  exact (Submodule.equivMapOfInjective _ cochainEquiv.injective _).finrank_eq

/-- The Tits form of the wall quiver with one loop at `true` is `x₀² - g x₀ x₁`: the loop cancels
`x₁²`, so the vertex `true` is isotropic. -/
lemma titsForm_wallArrow_pUnit (x : Bool → ℤ) :
    titsForm (wallArrow ι PUnit) x = x false ^ 2 - Fintype.card ι * (x false * x true) := by
  simp only [titsForm, sum_bool]
  rw [Fintype.card_eq_zero (α := wallArrow ι PUnit false false),
    Fintype.card_eq_zero (α := wallArrow ι PUnit true false), card_wallArrow_false_true,
    card_wallArrow_true_true, Fintype.card_unique (α := PUnit)]
  push_cast
  ring

/-- **Crawley-Boevey's formula for the wall that carries the point**: for a preprojective
representation of the wall quiver with one loop at `true`, of dimension vector `(p, 1)`,
`e(M) = 2 dim End M - 2(p² - g p)`, that is `e = 2 dim End M + v²` with `v² = 2 p (g - p)`. -/
theorem selfExtDim_pointWall [FiniteDimensional k V]
    {M : DoubledRep k (wallArrow ι PUnit) (kroneckerSpace V k)} (hM : M.IsPreprojective) :
    (selfExtDim M : ℤ) = 2 * finrank k (Kronecker.DoubledRep.Hom (M.toKronecker) (M.toKronecker)) -
      2 * ((finrank k V : ℤ) ^ 2 - Fintype.card ι * finrank k V) := by
  rw [selfExtDim_eq hM, titsForm_wallArrow_pUnit, finrank_Hom_toKronecker]
  change 2 * _ - 2 * ((finrank k V : ℤ) ^ 2 - _ * ((finrank k V : ℤ) * finrank k k)) = _
  rw [Module.finrank_self]
  ring

/-- **The lemma on the wall group that carries the point, in the general model.** Let `M` be a
preprojective representation of the double of the wall quiver with `g` arrows and one loop at the
isotropic vertex, of dimension vector `(p, 1)` with `p > 0` and `e(M) = 2` for the general complex.
Then either every `B_i` vanishes and the `A_i` are linearly independent (`M = S^{p-g} ⊕ T_S U`), or
every `A_i` vanishes and the `B_i 1` are linearly independent (`M = S^{p-g} ⊕ T_S⁻¹ U`). -/
theorem twoExtensions_of_selfExtDim_eq_two [FiniteDimensional k V]
    {M : DoubledRep k (wallArrow ι PUnit) (kroneckerSpace V k)} (hM : M.IsPreprojective)
    (he : selfExtDim M = 2) (hp : 0 < finrank k V) :
    ((∀ i, (M.toKronecker).B i = 0) ∧ LinearIndependent k (M.toKronecker).A) ∨
      ((∀ i, (M.toKronecker).A i = 0) ∧ LinearIndependent k fun i ↦ (M.toKronecker).B i 1) := by
  have h := selfExtDim_pointWall hM
  rw [he] at h
  push_cast at h
  refine (M.toKronecker).twoExtensions' (isPreprojective_toKronecker hM) ?_ hp
  refine mul_left_cancel₀ (two_ne_zero (α := ℤ)) ?_
  linear_combination -h

end PointWall

end DoubledRep

end Quiver.Preprojective
