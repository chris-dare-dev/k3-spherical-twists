/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.IntrinsicPhases

/-!
# Uniqueness of Harder–Narasimhan filtrations

Two HN filtrations of one object whose factors are all nonzero have the same length, the same
phases, and isomorphic factors in the same positions. This is the uniqueness that Bridgeland
records after the definition of a slicing (arXiv:math/0212237, §3); the draft *Harder–Narasimhan
towers of spherical twist words on a Picard-rank-one K3 surface* uses it to identify the tower
its algorithm produces with "the" HN tower.

The proof peels off the last factor. The last phases agree
(`HNFiltration.phiMinus_eq_of_lastFactors_nonzero`), and then the last triangles
`A → E → B → A⟦1⟧` of the two filtrations are isomorphic, by a general fact about distinguished
triangles: two of them on the same middle object are isomorphic when the first vertex of each maps
trivially to the third vertex of the other and to the shifted third vertex `B⟦-1⟧` of its own
triangle (`Pretriangulated.exists_iso_of_hom_eq_zero`). Here the first vertices have all phases
strictly above the common last phase `ψ`, and the third vertices lie in `P(ψ)` and `P(ψ - 1)`.

## Main results

* `CategoryTheory.Pretriangulated.exists_iso_of_hom_eq_zero`: the isomorphism of two such
  distinguished triangles, extending the given isomorphism of middle objects.
* `CategoryTheory.Triangulated.HNFiltration.exists_iso_of_nonzero`: uniqueness of HN filtrations
  with nonzero factors.
* `CategoryTheory.Triangulated.HNFiltration.isZero_of_n_eq_zero`,
  `CategoryTheory.Triangulated.HNFiltration.n_eq_zero_of_isZero`: an HN filtration with nonzero
  factors is empty exactly when its object is zero.

## Implementation notes

`HNFiltration` allows zero factors, so uniqueness is stated for filtrations whose factors are all
nonzero; `Slicing.exists_hn_nonzero_boundaries` and `HNFiltration.dropFirst`, `dropLast` remove
zero factors at the ends. The triangles of a `PostnikovTower` are tied to its chain only by
isomorphisms of objects, so the statement compares factors and phases, not the maps of the
chains.

## Tags

Harder–Narasimhan filtration, slicing, uniqueness, distinguished triangle
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

namespace CategoryTheory.Pretriangulated

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- An endomorphism of the first vertex of a distinguished triangle `A → E → B → A⟦1⟧` that
vanishes after `A → E` is zero, when every map `A ⟶ B⟦-1⟧` vanishes. -/
theorem endo_eq_zero_of_comp_mor₁_eq_zero {T : Triangle C} (hT : T ∈ distTriang C)
    (h : ∀ f : T.obj₁ ⟶ T.obj₃⟦(-1 : ℤ)⟧, f = 0) (x : T.obj₁ ⟶ T.obj₁)
    (hx : x ≫ T.mor₁ = 0) : x = 0 := by
  obtain ⟨y, hy⟩ := Triangle.coyoneda_exact₂ T.invRotate (inv_rot_of_distTriang _ hT) x hx
  have hy0 : y = 0 := h y
  rw [hy, hy0, zero_comp]
  rfl

/-- **Two orthogonal triangles on one object are isomorphic.** Let `A → E → B → A⟦1⟧` and
`A' → E' → B' → A'⟦1⟧` be distinguished, with `e : E ≅ E'`. If every map `A ⟶ B'`, `A' ⟶ B`,
`A ⟶ B⟦-1⟧` and `A' ⟶ B'⟦-1⟧` vanishes, then the triangles are isomorphic by an isomorphism
whose middle component is `e`. -/
theorem exists_iso_of_hom_eq_zero {T T' : Triangle C} (hT : T ∈ distTriang C)
    (hT' : T' ∈ distTriang C) (e : T.obj₂ ≅ T'.obj₂)
    (h₁ : ∀ f : T.obj₁ ⟶ T'.obj₃, f = 0) (h₂ : ∀ f : T'.obj₁ ⟶ T.obj₃, f = 0)
    (h₃ : ∀ f : T.obj₁ ⟶ T.obj₃⟦(-1 : ℤ)⟧, f = 0)
    (h₄ : ∀ f : T'.obj₁ ⟶ T'.obj₃⟦(-1 : ℤ)⟧, f = 0) :
    ∃ i : T ≅ T', i.hom.hom₂ = e.hom := by
  obtain ⟨a, ha⟩ := Triangle.coyoneda_exact₂ T' hT' (T.mor₁ ≫ e.hom) (h₁ _)
  obtain ⟨a', ha'⟩ := Triangle.coyoneda_exact₂ T hT (T'.mor₁ ≫ e.inv) (h₂ _)
  have h_aa' : a ≫ a' = 𝟙 _ := by
    have hx : (a ≫ a' - 𝟙 _) ≫ T.mor₁ = 0 := by
      rw [Preadditive.sub_comp, Category.assoc, ← ha', ← Category.assoc, ← ha]
      simp
    exact sub_eq_zero.mp (endo_eq_zero_of_comp_mor₁_eq_zero hT h₃ _ hx)
  have h_a'a : a' ≫ a = 𝟙 _ := by
    have hx : (a' ≫ a - 𝟙 _) ≫ T'.mor₁ = 0 := by
      rw [Preadditive.sub_comp, Category.assoc, ← ha, ← Category.assoc, ← ha']
      simp
    exact sub_eq_zero.mp (endo_eq_zero_of_comp_mor₁_eq_zero hT' h₄ _ hx)
  let e₁ : T.obj₁ ≅ T'.obj₁ := ⟨a, a', h_aa', h_a'a⟩
  exact ⟨isoTriangleOfIso₁₂ T T' hT hT' e₁ e ha, rfl⟩

end CategoryTheory.Pretriangulated

namespace CategoryTheory.Triangulated

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The last chain object of a Postnikov tower with at least one factor is the second vertex of
its last triangle, up to isomorphism. -/
noncomputable def PostnikovTower.lastTriangleObj₂Iso {E : C} (P : PostnikovTower C E)
    (hn : 0 < P.n) : (P.triangle ⟨P.n - 1, by omega⟩).obj₂ ≅ E :=
  (Classical.choice (P.triangle_obj₂ ⟨P.n - 1, by omega⟩)).trans
    ((eqToIso (congrArg P.chain.obj (Fin.ext (by simp; omega)))).trans
      (Classical.choice P.top_iso))

/-- The first vertex of the last triangle of a Postnikov tower is its next-to-last chain
object. -/
noncomputable def PostnikovTower.lastTriangleObj₁Iso {E : C} (P : PostnikovTower C E)
    (hn : 0 < P.n) :
    (P.triangle ⟨P.n - 1, by omega⟩).obj₁ ≅ P.chain.obj ⟨P.n - 1, by omega⟩ :=
  Classical.choice (P.triangle_obj₁ ⟨P.n - 1, by omega⟩)

/-- An HN filtration of a zero object whose factors are nonzero has no factors. -/
theorem HNFiltration.n_eq_zero_of_isZero (s : Slicing C) {E : C} (F : HNFiltration C s.P E)
    (hF : ∀ i, ¬IsZero (F.factor i)) (hE : IsZero E) : F.n = 0 := by
  by_contra hn
  have hpos : 0 < F.n := Nat.pos_of_ne_zero hn
  exact hF _ (F.firstFactor_isZero_of_hom_eq_zero C s hpos (fun f => hE.eq_of_tgt f 0))

/-- An HN filtration with no factors filters a zero object. -/
theorem HNFiltration.isZero_of_n_eq_zero {P : ℝ → ObjectProperty C} {E : C}
    (F : HNFiltration C P E) (hn : F.n = 0) : IsZero E :=
  F.isZero_of_length_zero hn

/-- A prefix of an HN filtration keeps the requested number of factors. -/
@[simp]
theorem HNFiltration.prefix_n {P : ℝ → ObjectProperty C} {E : C}
    (F : HNFiltration C P E) (k : ℕ) (hk : k ≤ F.n) : (F.prefix C k hk).n = k := rfl

/-- Moving an HN filtration along an isomorphism of its object keeps its length. -/
@[simp]
theorem HNFiltration.ofIso_n {P : ℝ → ObjectProperty C} {E E' : C}
    (F : HNFiltration C P E) (e : E ≅ E') : (F.ofIso C e).n = F.n := rfl

/-- The factors of a prefix of an HN filtration are factors of the filtration. -/
theorem HNFiltration.prefix_factor {P : ℝ → ObjectProperty C} {E : C}
    (F : HNFiltration C P E) (k : ℕ) (hk : k ≤ F.n) (i : Fin (F.prefix C k hk).n) :
    (F.prefix C k hk).factor i = F.factor ⟨i, lt_of_lt_of_le i.isLt hk⟩ := rfl

/-- The phases of a prefix of an HN filtration are phases of the filtration. -/
theorem HNFiltration.prefix_φ' {P : ℝ → ObjectProperty C} {E : C}
    (F : HNFiltration C P E) (k : ℕ) (hk : k ≤ F.n) (i : Fin (F.prefix C k hk).n) :
    (F.prefix C k hk).φ i = F.φ ⟨i, lt_of_lt_of_le i.isLt hk⟩ := rfl

/-- The factors of an HN filtration moved along an isomorphism of its object are unchanged. -/
@[simp]
theorem HNFiltration.ofIso_factor {P : ℝ → ObjectProperty C} {E E' : C}
    (F : HNFiltration C P E) (e : E ≅ E') (i : Fin (F.ofIso C e).n) :
    (F.ofIso C e).factor i = F.factor i := rfl

/-- The phases of an HN filtration moved along an isomorphism of its object are unchanged. -/
@[simp]
theorem HNFiltration.ofIso_φ {P : ℝ → ObjectProperty C} {E E' : C}
    (F : HNFiltration C P E) (e : E ≅ E') (i : Fin (F.ofIso C e).n) :
    (F.ofIso C e).φ i = F.φ i := rfl

/-- Every map from the next-to-last chain object of an HN filtration to an object of phase at
most the last phase vanishes. -/
private theorem HNFiltration.hom_chain_pred_eq_zero (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (hn : 0 < F.n) {X : C} {ψ : ℝ} (hX : s.P ψ X)
    (hψ : ψ ≤ F.φ ⟨F.n - 1, by omega⟩) (f : F.chain.obj ⟨F.n - 1, by omega⟩ ⟶ X) : f = 0 :=
  s.hom_eq_zero_of_phase_gap C (F.prefix C (F.n - 1) (by omega))
    (HNFiltration.single C X ψ hX)
    (fun i _ => hψ.trans_lt (F.hφ (Fin.mk_lt_mk.mpr (by omega)))) f

/-- **Uniqueness of HN filtrations.** Two HN filtrations of one object whose factors are all
nonzero have the same length, and the same phase and isomorphic factors in each position. -/
theorem HNFiltration.exists_iso_of_nonzero (s : Slicing C) {E : C}
    (F G : HNFiltration C s.P E) (hF : ∀ i, ¬IsZero (F.factor i))
    (hG : ∀ j, ¬IsZero (G.factor j)) :
    ∃ h : F.n = G.n, ∀ i : Fin F.n,
      F.φ i = G.φ (Fin.cast h i) ∧ Nonempty (F.factor i ≅ G.factor (Fin.cast h i)) := by
  suffices key : ∀ (m : ℕ) {E : C} (F G : HNFiltration C s.P E), F.n = m →
      (∀ i, ¬IsZero (F.factor i)) → (∀ j, ¬IsZero (G.factor j)) →
      ∃ h : F.n = G.n, ∀ i : Fin F.n,
        F.φ i = G.φ (Fin.cast h i) ∧ Nonempty (F.factor i ≅ G.factor (Fin.cast h i)) from
    key F.n F G rfl hF hG
  intro m
  induction m with
  | zero =>
      intro E F G hFm hF hG
      have hE : IsZero E := F.isZero_of_n_eq_zero hFm
      have hGn : G.n = 0 := G.n_eq_zero_of_isZero s hG hE
      exact ⟨by omega, fun i => absurd i.isLt (by omega)⟩
  | succ m ih =>
      intro E F G hFm hF hG
      have hFpos : 0 < F.n := by omega
      have hE : ¬IsZero E := fun hE => by
        have := F.n_eq_zero_of_isZero s hF hE
        omega
      have hGpos : 0 < G.n := G.n_pos C hE
      -- The last phases agree.
      have hlast : F.φ ⟨F.n - 1, by omega⟩ = G.φ ⟨G.n - 1, by omega⟩ :=
        F.phiMinus_eq_of_lastFactors_nonzero C s G hFpos hGpos (hF _) (hG _)
      -- The last triangles are isomorphic.
      set TF := F.triangle ⟨F.n - 1, by omega⟩ with hTF
      set TG := G.triangle ⟨G.n - 1, by omega⟩ with hTG
      have hTFd : TF ∈ distTriang C := F.triangle_dist _
      have hTGd : TG ∈ distTriang C := G.triangle_dist _
      let eF₁ := F.lastTriangleObj₁Iso hFpos
      let eG₁ := G.lastTriangleObj₁Iso hGpos
      let e₂ : TF.obj₂ ≅ TG.obj₂ :=
        (F.lastTriangleObj₂Iso hFpos).trans (G.lastTriangleObj₂Iso hGpos).symm
      have hFfac : s.P (F.φ ⟨F.n - 1, by omega⟩) TF.obj₃ := F.semistable _
      have hGfac : s.P (G.φ ⟨G.n - 1, by omega⟩) TG.obj₃ := G.semistable _
      have hshift : ∀ {X : C} {ψ : ℝ}, s.P ψ X → s.P (ψ - 1) (X⟦(-1 : ℤ)⟧) := by
        intro X ψ hX
        have := (s.shift_int C ψ X (-1)).mp hX
        rwa [show ψ + ((-1 : ℤ) : ℝ) = ψ - 1 by push_cast; ring] at this
      obtain ⟨iso, -⟩ := exists_iso_of_hom_eq_zero hTFd hTGd e₂
        (fun f => by
          have := F.hom_chain_pred_eq_zero s hFpos hGfac hlast.ge (eF₁.inv ≫ f)
          simpa using congrArg (eF₁.hom ≫ ·) this)
        (fun f => by
          have := G.hom_chain_pred_eq_zero s hGpos hFfac hlast.le (eG₁.inv ≫ f)
          simpa using congrArg (eG₁.hom ≫ ·) this)
        (fun f => by
          have := F.hom_chain_pred_eq_zero s hFpos (hshift hFfac) (by linarith) (eF₁.inv ≫ f)
          simpa using congrArg (eF₁.hom ≫ ·) this)
        (fun f => by
          have := G.hom_chain_pred_eq_zero s hGpos (hshift hGfac) (by linarith) (eG₁.inv ≫ f)
          simpa using congrArg (eG₁.hom ≫ ·) this)
      -- The prefixes are HN filtrations of isomorphic objects; apply the induction hypothesis.
      let F' := F.prefix C (F.n - 1) (by omega)
      let eA : G.chain.obj ⟨G.n - 1, by omega⟩ ≅ F.chain.obj ⟨F.n - 1, by omega⟩ :=
        eG₁.symm.trans ((Triangle.π₁.mapIso iso).symm.trans eF₁)
      let G' := (G.prefix C (G.n - 1) (by omega)).ofIso C eA
      have hF'n : F'.n = F.n - 1 := rfl
      have hG'n : G'.n = G.n - 1 := rfl
      obtain ⟨hn', hrest⟩ := ih F' G' (by omega)
        (fun i => hF ⟨i, by omega⟩) (fun j => hG ⟨j, by omega⟩)
      have hn'' : F.n - 1 = G.n - 1 := by omega
      refine ⟨by omega, fun i => ?_⟩
      by_cases hi : i.val < F.n - 1
      · obtain ⟨hφ, ⟨fac⟩⟩ := hrest ⟨i, hi⟩
        exact ⟨hφ, ⟨fac⟩⟩
      · have hi' : i = ⟨F.n - 1, Nat.sub_lt hFpos Nat.one_pos⟩ :=
          Fin.ext (by have := i.isLt; simp only at hi ⊢; omega)
        have hci : Fin.cast (show F.n = G.n by omega) i =
            ⟨G.n - 1, Nat.sub_lt hGpos Nat.one_pos⟩ :=
          Fin.ext (by simp only [Fin.val_cast, hi']; omega)
        rw [hci, hi']
        exact ⟨hlast, ⟨Triangle.π₃.mapIso iso⟩⟩

end CategoryTheory.Triangulated
