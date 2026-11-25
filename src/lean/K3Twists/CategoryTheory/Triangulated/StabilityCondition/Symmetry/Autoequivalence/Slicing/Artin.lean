/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.GroupTheory.Coxeter.ArtinGroup
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Autoequivalence.Slicing.HarderNarasimhan

/-!
# Artin groups acting by autoequivalences

Spherical twists `T_i` satisfy the braid relations of a Coxeter matrix `M` up to natural
isomorphism (Seidel–Thomas, arXiv:math/0001043), so `σ_i ↦ [T_i]` defines a homomorphism
`Art(M) →* AutQuot C`. This file builds that homomorphism once, for any family of exact
autoequivalences whose classes satisfy the braid relations, proves its corollaries on slicings
and HN filtrations, and gives three ways to check the braid relations:

* `AutQuot.isBraidLiftable_of_iso`: one natural isomorphism per braid relation;
* `AutQuot.isBraidLiftable_ofExt`: the Seidel–Thomas form, commuting twists where the total Ext
  vanishes and the length-three relation where it is one;
* `TwistConjugation.Configuration.isBraidLiftable`: the conjugation formula
  `T_{Φ S} ≅ Φ T_S Φ⁻¹` together with one object identity per edge. No pairwise braid
  isomorphism is assumed, and it holds for every Coxeter matrix at once.

## Main definitions

* `TriEquiv.ofWord T ω`, `TriEquiv.ofSignedWord T L`: the composite autoequivalence of a word.
* `AutQuot.artinHom T h`: the homomorphism `Art(M) →* AutQuot C`, `σ_i ↦ [T_i]`, from a proof
  `h` that the classes `[T_i]` satisfy the braid relations.
* `TwistConjugation C`: twists as a conjugation-equivariant map `τ : C → AutQuot C`, invariant
  under shifts and isomorphisms, with `τ(Φ S) = [Φ] τ(S) [Φ]⁻¹` for spherical `S`.
* `TwistConjugation.Configuration H M`: spherical objects `x_i` and autoequivalences `T_i`,
  with the link `[T_i] = τ(x_i)` and one object identity per edge of `M`.
* `TwistConjugation.toAutQuot H K`: the homomorphism `Art(M) →* AutQuot C` of a configuration.

## Main results

* `AutQuot.nonempty_iso_of_ofSignedWord_eq`, `AutQuot.hn_of_ofSignedWord_eq`: two signed words
  with equal images in `Art(M)` give naturally isomorphic autoequivalences; they act equally on
  slicings and carry HN filtrations to each other, with the same phases and isomorphic factors.
* `AutQuot.map_pureArtinGroup_le`: the image of the pure Artin group lies in the normal closure
  of the squares `[T_i]²`.
* `AutQuot.exists_factor`, `AutQuot.artinHom_eq_one_of_mem_pureArtinGroup`: any homomorphism out
  of `AutQuot C` in which every `[T_i]` is an involution (the action on the Mukai lattice, where
  `T_S` acts by the reflection in `v(S)`) makes `Art(M)` act through the Coxeter group, so it
  sees no element of the pure Artin group.
* `TwistConjugation.commute_of_iso`: if `Φ Y ≅ Y[n]` for a spherical `Y`, then `[Φ]` commutes
  with `τ(Y)`; for `Φ = T_X` this is the commutation of twists at orthogonal objects.
* The same corollaries on the `TwistConjugation` route: `TwistConjugation.hn_of_eq`,
  `TwistConjugation.map_pureArtinGroup_le`, `TwistConjugation.exists_factor`.

## The content of `TwistConjugation`

The four fields of `TwistConjugation` hold for `τ ≡ 1` with any spherical predicate, so a
theorem about `TwistConjugation` alone says nothing. The content sits in a `Configuration`: the
link `[T_i] = τ(x_i)` ties the autoequivalences to the objects, and each edge `i — i'` of `M`
needs one object identity, `T_i x_{i'} ≅ x_{i'}[n]` for `m = 2` and `T_{i'} T_i x_{i'} ≅ x_i[n]`
for `m = 3`. The proofs use the conjugation field only at the objects `x_{i'}` and only for the
autoequivalences of alternating words.

In `D^b(X)` the twist `T_S` is the Fourier–Mukai transform with kernel
`cone(S^∨ ⊠ S → 𝒪_Δ)`; the conjugation field is Seidel–Thomas, arXiv:math/0001043, Lemma 2.11,
and `T_{S[n]} ≅ T_S` holds because the evaluation triangle of `S[n]` is that of `S`. Mathlib has no
twist functor, so the library builds no `TwistConjugation` from geometry.

## Conventions

`AutQuot` composes in the usual order: `mk Φ * mk Ψ` has functor `Φ ∘ Ψ`. `ofWord T [i₁, …, i_k]`
is `T_{i₁} ∘ ⋯ ∘ T_{i_k}` and its class is `[T_{i₁}] ⋯ [T_{i_k}]`, so words are read as in
`CoxeterMatrix.IsBraidLiftable`, with no reversal.
-/

open CoxeterSystem CoxeterMatrix
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w u

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {B : Type*}

/-! ### Words of autoequivalences -/

namespace TriEquiv

/-- `ofWord T [i₁, …, i_k]` is `T_{i₁} ∘ ⋯ ∘ T_{i_k}`: the rightmost letter is applied first. -/
def ofWord (T : B → TriEquiv C) : List B → TriEquiv C
  | [] => TriEquiv.id
  | i :: ω => (ofWord T ω).comp (T i)

@[simp] theorem ofWord_nil_obj (T : B → TriEquiv C) (X : C) :
    (ofWord T []).e.functor.obj X = X := rfl

@[simp] theorem ofWord_cons_obj (T : B → TriEquiv C) (i : B) (ω : List B) (X : C) :
    (ofWord T (i :: ω)).e.functor.obj X = (T i).e.functor.obj ((ofWord T ω).e.functor.obj X) :=
  rfl

/-- The word of an `m = 2` edge: `alternatingWord i' i 1 = [i]`. -/
theorem ofWord_alternatingWord_one_obj (T : B → TriEquiv C) (i i' : B) (X : C) :
    (ofWord T (alternatingWord i' i 1)).e.functor.obj X = (T i).e.functor.obj X := rfl

/-- The word of an `m = 3` edge: `alternatingWord i' i 2 = [i', i]`. -/
theorem ofWord_alternatingWord_two_obj (T : B → TriEquiv C) (i i' : B) (X : C) :
    (ofWord T (alternatingWord i' i 2)).e.functor.obj X =
      (T i').e.functor.obj ((T i).e.functor.obj X) := rfl

/-- Signed words: the letter `(i, true)` is `T_i` and `(i, false)` is `T_i⁻¹`, as in
`FreeGroup.mk`. -/
def ofSignedWord (T : B → TriEquiv C) : List (B × Bool) → TriEquiv C
  | [] => TriEquiv.id
  | x :: L => (ofSignedWord T L).comp (cond x.2 (T x.1) (T x.1).symm)

end TriEquiv

namespace AutQuot

theorem mk_ofWord (T : B → TriEquiv C) (ω : List B) :
    mk (TriEquiv.ofWord T ω) = (ω.map (mk ∘ T)).prod := by
  induction ω with
  | nil => rfl
  | cons i ω ih =>
    rw [List.map_cons, List.prod_cons, ← ih]
    rfl

theorem mk_ofSignedWord (T : B → TriEquiv C) (L : List (B × Bool)) :
    mk (TriEquiv.ofSignedWord T L) =
      (L.map fun x => cond x.2 (mk (T x.1)) (mk (T x.1))⁻¹).prod := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    rw [List.map_cons, List.prod_cons, ← ih]
    obtain ⟨i, b⟩ := x
    cases b <;> rfl

/-! ### Three ways to the braid relations -/

/-- **Pairwise braid isomorphisms.** The classes `[T_i]` satisfy the braid relations of `M` if,
for each pair `i ≠ i'` with `M i i' ≠ 0`, the two braid words are naturally isomorphic. -/
theorem isBraidLiftable_of_iso {M : CoxeterMatrix B} (T : B → TriEquiv C)
    (h : ∀ i i', i ≠ i' → M i i' ≠ 0 →
      Nonempty ((TriEquiv.ofWord T (braidWord M i i')).e.functor ≅
        (TriEquiv.ofWord T (braidWord M i' i)).e.functor)) :
    M.IsBraidLiftable (mk ∘ T) :=
  (M.isBraidLiftable_iff _).2 fun i i' hii hm => by
    rw [← mk_ofWord, ← mk_ofWord]
    exact _root_.Quotient.sound (h i i' hii hm)

/-- **The Seidel–Thomas form.** For spherical objects with total Ext dimensions `e i j`, the
classes `[T_i]` satisfy the braid relations of `CoxeterMatrix.ofExt e` if twists commute where
`e = 0` and satisfy the length-three relation where `e = 1` (Seidel–Thomas, arXiv:math/0001043,
§2). -/
theorem isBraidLiftable_ofExt [DecidableEq B] (e : B → B → ℕ) (he : ∀ i j, e i j = e j i)
    (T : B → TriEquiv C)
    (h0 : ∀ i j, i ≠ j → e i j = 0 →
      Nonempty ((T j).e.functor ⋙ (T i).e.functor ≅ (T i).e.functor ⋙ (T j).e.functor))
    (h1 : ∀ i j, i ≠ j → e i j = 1 →
      Nonempty ((T i).e.functor ⋙ (T j).e.functor ⋙ (T i).e.functor ≅
        (T j).e.functor ⋙ (T i).e.functor ⋙ (T j).e.functor)) :
    (ofExt e he).IsBraidLiftable (mk ∘ T) :=
  CoxeterMatrix.isBraidLiftable_ofExt e he _
    (fun i j hij h => _root_.Quotient.sound (h0 i j hij h))
    (fun i j hij h => _root_.Quotient.sound (h1 i j hij h))

/-! ### The homomorphism and its corollaries -/

variable {M : CoxeterMatrix B}

/-- **The Artin group acts by autoequivalences.** The homomorphism `Art(M) →* AutQuot C`,
`σ_i ↦ [T_i]`, for autoequivalences whose classes satisfy the braid relations of `M`. -/
def artinHom (T : B → TriEquiv C) (h : M.IsBraidLiftable (mk ∘ T)) :
    M.ArtinGroup →* AutQuot C :=
  ArtinGroup.lift _ h

variable (T : B → TriEquiv C) (h : M.IsBraidLiftable (mk ∘ T))

@[simp] theorem artinHom_of (i : B) : artinHom T h (M.artinGen i) = mk (T i) :=
  ArtinGroup.lift_of _ _ i

/-- A signed word of `Art(M)` goes to the class of the composite autoequivalence. -/
theorem artinHom_ofSignedWord (L : List (B × Bool)) :
    artinHom T h (ArtinGroup.ofSignedWord M L) = mk (TriEquiv.ofSignedWord T L) := by
  rw [artinHom, ArtinGroup.lift_ofSignedWord, mk_ofSignedWord]
  rfl

/-- The Artin group acts on slicings through `artinHom`, a signed word as its composite. -/
theorem artinHom_ofSignedWord_smul (L : List (B × Bool)) (s : Slicing C) :
    artinHom T h (ArtinGroup.ofSignedWord M L) • s = (TriEquiv.ofSignedWord T L).act s := by
  rw [artinHom_ofSignedWord]; rfl

include h in
/-- **Words with equal Artin images are isomorphic autoequivalences**: their forward functors
are naturally isomorphic, and they act equally on slicings. -/
theorem nonempty_iso_of_ofSignedWord_eq {L L' : List (B × Bool)}
    (hL : ArtinGroup.ofSignedWord M L = ArtinGroup.ofSignedWord M L') :
    Nonempty ((TriEquiv.ofSignedWord T L).e.functor ≅ (TriEquiv.ofSignedWord T L').e.functor) ∧
      ∀ s : Slicing C, (TriEquiv.ofSignedWord T L).act s = (TriEquiv.ofSignedWord T L').act s := by
  have h' : mk (TriEquiv.ofSignedWord T L) = mk (TriEquiv.ofSignedWord T L') := by
    rw [← artinHom_ofSignedWord T h, ← artinHom_ofSignedWord T h, hL]
  have hiso := _root_.Quotient.exact h'
  exact ⟨hiso, fun s => TriEquiv.act_congr hiso.some s⟩

include h in
/-- **Words with equal Artin images carry HN filtrations to each other.** Let `Φ` and `Ψ` be the
autoequivalences of two signed words with the same image in `Art(M)`. Every HN filtration of
`Ψ E` for `Ψ s` with nonzero factors has the length and phases of a given HN filtration `F` of `E`
for `s` with nonzero factors, and factors isomorphic to the images under `Φ` of those of `F`. So
which word of an Artin element is used makes no difference to the HN filtration. -/
theorem hn_of_ofSignedWord_eq {L L' : List (B × Bool)}
    (hL : ArtinGroup.ofSignedWord M L = ArtinGroup.ofSignedWord M L')
    (s : Slicing C) {E : C} (F : HNFiltration C s.P E)
    (G : HNFiltration C ((TriEquiv.ofSignedWord T L').act s).P
      ((TriEquiv.ofSignedWord T L').e.functor.obj E))
    (hF : ∀ i, ¬IsZero (F.factor i)) (hG : ∀ j, ¬IsZero (G.factor j)) :
    ∃ hn : F.n = G.n, ∀ i : Fin F.n, F.φ i = G.φ (Fin.cast hn i) ∧
      Nonempty ((TriEquiv.ofSignedWord T L).e.functor.obj (F.factor i) ≅
        G.factor (Fin.cast hn i)) := by
  obtain ⟨⟨α⟩, -⟩ := nonempty_iso_of_ofSignedWord_eq T h hL
  obtain ⟨hn, hi⟩ := TriEquiv.exists_iso_of_hnFiltration _ s F G hF hG
  exact ⟨hn, fun i => ⟨(hi i).1, ⟨(α.app _).trans (hi i).2.some⟩⟩⟩

/-- The image of the pure Artin group lies in the normal closure of the squares `[T_i]²`. -/
theorem map_pureArtinGroup_le :
    M.pureArtinGroup.map (artinHom T h) ≤
      Subgroup.normalClosure (Set.range fun i => mk (T i) ^ 2) := by
  rw [pureArtinGroup_eq_normalClosure]
  refine (Subgroup.map_normalClosure_le _ _).trans (Subgroup.normalClosure_mono ?_)
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  exact ⟨i, by simp⟩

/-- **Involutive representations see only the Coxeter group.** If `ρ : AutQuot C →* G` sends every
`[T_i]` to an involution (the action on the Mukai lattice, where a twist acts by a reflection),
then `ρ ∘ artinHom` factors through `W(M)`. -/
theorem exists_factor {G : Type*} [Group G] (ρ : AutQuot C →* G)
    (hsq : ∀ i, ρ (mk (T i)) ^ 2 = 1) :
    ∃ ψ : M.Group →* G, ψ.comp M.toCoxeterGroup = ρ.comp (artinHom T h) :=
  M.exists_factor_of_sq _ (fun i => by simpa using hsq i)

/-- **Involutive representations cannot see pure braids.** Under the hypotheses of
`exists_factor`, every element of the pure Artin group acts trivially. -/
theorem artinHom_eq_one_of_mem_pureArtinGroup {G : Type*} [Group G] (ρ : AutQuot C →* G)
    (hsq : ∀ i, ρ (mk (T i)) ^ 2 = 1) {g : M.ArtinGroup} (hg : g ∈ M.pureArtinGroup) :
    ρ (artinHom T h g) = 1 :=
  M.pure_mem_ker_of_sq (ρ.comp (artinHom T h)) (fun i => by simpa using hsq i) hg

end AutQuot

/-! ### Twists as a conjugation-equivariant map -/

/-- **Twists as a conjugation-equivariant map.** A predicate `IsSpherical` and a map
`twist : C → AutQuot C`, the class `[T_X]` of the twist along `X` (its values off the spherical
objects are irrelevant), with:

* `twist_eq`: `T_{X[n]} = T_X`, and isomorphic objects have the same twist;
* `twist_conj`: `T_{Φ S} ≅ Φ ∘ T_S ∘ Φ⁻¹` for every exact autoequivalence `Φ` and spherical `S`
  (Seidel–Thomas, arXiv:math/0001043, Lemma 2.11).

These fields hold for `twist ≡ 1`, so they carry no content alone; see
`TwistConjugation.Configuration` for where the content enters. -/
structure TwistConjugation (C : Type u) [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] where
  /-- The spherical objects (in the K3 case, `2`-spherical objects of `D^b(X)`). -/
  IsSpherical : C → Prop
  /-- The class `[T_X]` of the twist along `X`. -/
  twist : C → AutQuot C
  /-- The twist depends only on the object up to isomorphism and shift: `T_{X[n]} = T_X`. -/
  twist_eq : ∀ (X Y : C) (n : ℤ), Nonempty (X ≅ (shiftFunctor C n).obj Y) → twist X = twist Y
  /-- Seidel–Thomas, arXiv:math/0001043, Lemma 2.11: `T_{Φ S} ≅ Φ ∘ T_S ∘ Φ⁻¹` for spherical
  `S`. -/
  twist_conj : ∀ (Φ : TriEquiv C) (X : C), IsSpherical X →
    twist (Φ.e.functor.obj X) = AutQuot.mk Φ * twist X * (AutQuot.mk Φ)⁻¹

/-- **The object identity of an edge.** For objects `x i` and autoequivalences `T i`, the
identity of the ordered edge `(i, i')` of `M`: the autoequivalence of
`alternatingWord i' i (M i i' - 1)` sends `x i'` to a shift of `x c`, where `c = i` for odd
`M i i'` and `c = i'` for even `M i i'`. For `m = 2` it is `T_i x_{i'} ≅ x_{i'}[n]`
(`isEdgeIdentity_iff_of_eq_two`), for `m = 3` it is `T_{i'} T_i x_{i'} ≅ x_i[n]`
(`isEdgeIdentity_iff_of_eq_three`). -/
def IsEdgeIdentity (M : CoxeterMatrix B) (x : B → C) (T : B → TriEquiv C) (i i' : B) : Prop :=
  ∃ n : ℤ, Nonempty ((TriEquiv.ofWord T (alternatingWord i' i (M i i' - 1))).e.functor.obj (x i') ≅
    (shiftFunctor C n).obj (x (if Even (M i i' - 1) then i else i')))

theorem isEdgeIdentity_iff_of_eq_two {M : CoxeterMatrix B} (x : B → C) (T : B → TriEquiv C)
    {i i' : B} (hm : M i i' = 2) :
    IsEdgeIdentity M x T i i' ↔
      ∃ n : ℤ, Nonempty ((T i).e.functor.obj (x i') ≅ (shiftFunctor C n).obj (x i')) := by
  simp only [IsEdgeIdentity, hm, Nat.add_one_sub_one, Nat.not_even_one, ↓reduceIte]
  rfl

theorem isEdgeIdentity_iff_of_eq_three {M : CoxeterMatrix B} (x : B → C) (T : B → TriEquiv C)
    {i i' : B} (hm : M i i' = 3) :
    IsEdgeIdentity M x T i i' ↔ ∃ n : ℤ, Nonempty
      ((T i').e.functor.obj ((T i).e.functor.obj (x i')) ≅ (shiftFunctor C n).obj (x i)) := by
  simp only [IsEdgeIdentity, hm, Nat.add_one_sub_one, even_two, ↓reduceIte]
  rfl

namespace TwistConjugation

variable (H : TwistConjugation C)

/-- **Commuting twists.** If `Φ Y ≅ Y[n]` for a spherical `Y`, then `[Φ]` commutes with the twist
along `Y`. With `[Φ] = τ(X)`: twists along `X` and `Y` commute as soon as `T_X Y ≅ Y[n]`, for
instance when `Hom^•(X, Y) = 0`. -/
theorem commute_of_iso (Φ : TriEquiv C) {Y : C} (hY : H.IsSpherical Y) {n : ℤ}
    (e : Φ.e.functor.obj Y ≅ (shiftFunctor C n).obj Y) :
    Commute (AutQuot.mk Φ) (H.twist Y) := by
  have h1 := H.twist_eq _ _ n ⟨e⟩
  rw [H.twist_conj Φ Y hY, mul_inv_eq_iff_eq_mul] at h1
  exact h1

/-- **A configuration of type `M`** for twists `H`: spherical objects `obj i`, exact
autoequivalences `T i`, and

* the link `[T_i] = τ(obj i)`: `T i` is the twist along `obj i`;
* one object identity per edge `i — i'` with `M i i' ≠ 0`, in either orientation
  (`IsEdgeIdentity`). For `m = 2` it is `T_i x_{i'} ≅ x_{i'}[n]`, which holds when
  `Hom^•(x_i, x_{i'}) = 0`; for `m = 3` it is `T_{i'} T_i x_{i'} ≅ x_i[n]`, which holds when
  `Hom^•(x_i, x_{i'})` is one-dimensional, by the twist triangles. Edges with `M i i' = 0`
  (`m = ∞`) ask for nothing. -/
structure Configuration (M : CoxeterMatrix B) where
  /-- The spherical objects `x_i`. -/
  obj : B → C
  isSpherical_obj : ∀ i, H.IsSpherical (obj i)
  /-- The autoequivalences `T_i`. -/
  T : B → TriEquiv C
  /-- The link: `T_i` is the twist along `x_i`. -/
  mk_T : ∀ i, AutQuot.mk (T i) = H.twist (obj i)
  /-- One object identity per edge, in either orientation. -/
  edge : ∀ i i', i ≠ i' → M i i' ≠ 0 →
    IsEdgeIdentity M obj T i i' ∨ IsEdgeIdentity M obj T i' i

variable {H} {M : CoxeterMatrix B}

/-- **The braid relations of every Coxeter matrix from object identities.** The classes of the
twists of a configuration satisfy the braid relations of `M`: by the conjugation field, the
braid relation of an edge is the image under `τ` of its object identity
(`CoxeterMatrix.braid_iff_conj`). -/
theorem Configuration.isBraidLiftable (K : H.Configuration M) :
    M.IsBraidLiftable (AutQuot.mk ∘ K.T) := by
  have key : ∀ i i', M i i' ≠ 0 → IsEdgeIdentity M K.obj K.T i i' →
      ((braidWord M i i').map (AutQuot.mk ∘ K.T)).prod =
        ((braidWord M i' i).map (AutQuot.mk ∘ K.T)).prod := by
    rintro i i' hm ⟨n, ⟨e⟩⟩
    rw [M.braid_iff_conj _ i i' hm]
    have h1 := H.twist_eq _ _ n ⟨e⟩
    rw [H.twist_conj _ _ (K.isSpherical_obj i')] at h1
    rw [← AutQuot.mk_ofWord, Function.comp_apply, K.mk_T, h1, Function.comp_apply, K.mk_T]
  refine (M.isBraidLiftable_iff _).2 fun i i' hii hm => ?_
  rcases K.edge i i' hii hm with he | he
  · exact key i i' hm he
  · exact (key i' i (by rwa [M.symmetric]) he).symm

variable (H) in
/-- **The homomorphism `Art(M) →* AutQuot C` of a configuration**, `σ_i ↦ [T_i]`. -/
def toAutQuot (K : H.Configuration M) : M.ArtinGroup →* AutQuot C :=
  AutQuot.artinHom K.T K.isBraidLiftable

variable (K : H.Configuration M)

@[simp] theorem toAutQuot_of (i : B) : H.toAutQuot K (M.artinGen i) = AutQuot.mk (K.T i) :=
  AutQuot.artinHom_of _ _ i

theorem toAutQuot_of_eq_twist (i : B) : H.toAutQuot K (M.artinGen i) = H.twist (K.obj i) := by
  rw [toAutQuot_of, K.mk_T]

theorem toAutQuot_ofSignedWord (L : List (B × Bool)) :
    H.toAutQuot K (ArtinGroup.ofSignedWord M L) = AutQuot.mk (TriEquiv.ofSignedWord K.T L) :=
  AutQuot.artinHom_ofSignedWord _ _ L

/-- Words with equal Artin images are naturally isomorphic and act equally on slicings. -/
theorem nonempty_iso_of_eq {L L' : List (B × Bool)}
    (hL : ArtinGroup.ofSignedWord M L = ArtinGroup.ofSignedWord M L') :
    Nonempty ((TriEquiv.ofSignedWord K.T L).e.functor ≅
        (TriEquiv.ofSignedWord K.T L').e.functor) ∧
      ∀ s : Slicing C,
        (TriEquiv.ofSignedWord K.T L).act s = (TriEquiv.ofSignedWord K.T L').act s :=
  AutQuot.nonempty_iso_of_ofSignedWord_eq _ K.isBraidLiftable hL

/-- **Equal Artin images give isomorphic HN filtrations**, on the `TwistConjugation` route
(`AutQuot.hn_of_ofSignedWord_eq`). -/
theorem hn_of_eq {L L' : List (B × Bool)}
    (hL : ArtinGroup.ofSignedWord M L = ArtinGroup.ofSignedWord M L')
    (s : Slicing C) {E : C} (F : HNFiltration C s.P E)
    (G : HNFiltration C ((TriEquiv.ofSignedWord K.T L').act s).P
      ((TriEquiv.ofSignedWord K.T L').e.functor.obj E))
    (hF : ∀ i, ¬IsZero (F.factor i)) (hG : ∀ j, ¬IsZero (G.factor j)) :
    ∃ hn : F.n = G.n, ∀ i : Fin F.n, F.φ i = G.φ (Fin.cast hn i) ∧
      Nonempty ((TriEquiv.ofSignedWord K.T L).e.functor.obj (F.factor i) ≅
        G.factor (Fin.cast hn i)) :=
  AutQuot.hn_of_ofSignedWord_eq _ K.isBraidLiftable hL s F G hF hG

/-- The image of the pure Artin group lies in the normal closure of the squared twists. -/
theorem map_pureArtinGroup_le :
    M.pureArtinGroup.map (H.toAutQuot K) ≤
      Subgroup.normalClosure (Set.range fun i => H.twist (K.obj i) ^ 2) := by
  simp_rw [← K.mk_T]
  exact AutQuot.map_pureArtinGroup_le _ K.isBraidLiftable

/-- **Lattice data cannot see pure braids.** If `ρ : AutQuot C →* G` sends every twist of the
configuration to an involution (as the action on the Mukai lattice does), then
`ρ ∘ toAutQuot` factors through the Coxeter group `W(M)`. -/
theorem exists_factor {G : Type*} [Group G] (ρ : AutQuot C →* G)
    (hsq : ∀ i, ρ (H.twist (K.obj i)) ^ 2 = 1) :
    ∃ ψ : M.Group →* G, ψ.comp M.toCoxeterGroup = ρ.comp (H.toAutQuot K) :=
  AutQuot.exists_factor _ K.isBraidLiftable ρ fun i => by rw [K.mk_T]; exact hsq i

/-- Under the hypotheses of `exists_factor`, every pure braid acts trivially. -/
theorem toAutQuot_eq_one_of_mem_pureArtinGroup {G : Type*} [Group G] (ρ : AutQuot C →* G)
    (hsq : ∀ i, ρ (H.twist (K.obj i)) ^ 2 = 1) {g : M.ArtinGroup}
    (hg : g ∈ M.pureArtinGroup) : ρ (H.toAutQuot K g) = 1 :=
  AutQuot.artinHom_eq_one_of_mem_pureArtinGroup _ K.isBraidLiftable ρ
    (fun i => by rw [K.mk_T]; exact hsq i) hg

end TwistConjugation

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction
