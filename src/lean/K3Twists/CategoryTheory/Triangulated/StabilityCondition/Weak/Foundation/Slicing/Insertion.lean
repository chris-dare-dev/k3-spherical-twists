/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.Uniqueness
import Mathlib.Algebra.BigOperators.Fin

/-!
# Inserting a filtration by homotopy pullback

The step "insert its subobjects by pullback" of the tower algorithm in the draft
*Harder–Narasimhan towers of spherical twist words on a Picard-rank-one K3 surface*, section
"Recovering the arrows and closing the induction". A piece `A → B → M` of an old tower is
refined by a filtration `0 = M₀ → ⋯ → M_s = M` of its quotient through

  `B_i = B ×_M M_i = fib(B ⊕ M_i → M)`,

with `B₀ = A`, `B_s = B` and `cofib(B_{i-1} → B_i) ≅ cofib(M_{i-1} → M_i)`.

In a triangulated category the homotopy pullback is the fibre of the composite `B → M → M/M_i`,
and the octahedral axiom in its rotated form (`Triangulated.Octahedron'`) gives both triangles
the draft uses: `A → B_i → M_i → A⟦1⟧`, whose last map is `M_i → M → A⟦1⟧`, and
`B_{i-1} → B_i → M_i/M_{i-1} → B_{i-1}⟦1⟧`. The map `B_i → B` lies over `A → B` and over
`M_i → M` (`Pretriangulated.exists_pullback_triangles`).

Iterating gives the two forms in which the algorithm uses the insertion:

* along one triangle `A → B → M → A⟦1⟧`, HN filtrations of `A` and `M` whose phases are separated
  concatenate to an HN filtration of `B` with the factors of `A` followed by those of `M`
  (`HNFiltration.exists_concat`);
* an HN filtration of `E` (for the wall) whose factors carry HN filtrations (for the outgoing
  side) with separated phases refines to an HN filtration of `E` (for the outgoing side) whose
  factors are those of the pieces (`HNFiltration.exists_refinement`). Its phases come from the
  pieces and every isomorphism-closed property of factors is counted additively
  (`PostnikovTower.count`).

## Main results

* `CategoryTheory.Pretriangulated.exists_pullback_triangles`: the homotopy pullback.
* `CategoryTheory.Triangulated.HNFiltration.exists_concat`: concatenation along a triangle.
* `CategoryTheory.Triangulated.HNFiltration.exists_refinement`: refinement of every factor.

## Implementation notes

The statements are existential: a triangulated category without an enhancement has no
functorial cones, so the inserted objects are determined up to non-unique isomorphism. The
phase predicates `P`, `Q` are arbitrary; for a slicing they are its slices.

## Tags

Harder–Narasimhan filtration, Postnikov tower, homotopy pullback, octahedral axiom, wall crossing
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

namespace CategoryTheory.Pretriangulated

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **The homotopy pullback `B ×_M M'`.** Let `A → B → M → A⟦1⟧` and `M' → M → F → M'⟦1⟧` be
distinguished. The fibre `B'` of the composite `B → M → F` sits in distinguished triangles
`A → B' → M' → A⟦1⟧`, whose last map is the composite `M' → M → A⟦1⟧`, and
`B' → B → F → B'⟦1⟧`. The map `B' → B` lies over `A → B` and over `M' → M`, and the connecting
map `F → B'⟦1⟧` lies over the connecting map `F → M'⟦1⟧` and under `M → A⟦1⟧`: this is the
octahedron of the composable pair `B → M → F`. -/
theorem exists_pullback_triangles [IsTriangulated C] {A B M M' F : C}
    {f : A ⟶ B} {g : B ⟶ M} {h : M ⟶ A⟦(1 : ℤ)⟧} (hT : Triangle.mk f g h ∈ distTriang C)
    {ι : M' ⟶ M} {π : M ⟶ F} {δ : F ⟶ M'⟦(1 : ℤ)⟧} (hT' : Triangle.mk ι π δ ∈ distTriang C) :
    ∃ (B' : C) (f' : A ⟶ B') (g' : B' ⟶ M') (u : B' ⟶ B) (w : F ⟶ B'⟦(1 : ℤ)⟧),
      Triangle.mk f' g' (ι ≫ h) ∈ distTriang C ∧ Triangle.mk u (g ≫ π) w ∈ distTriang C ∧
        f' ≫ u = f ∧ g' ≫ ι = u ≫ g ∧ w ≫ g'⟦(1 : ℤ)⟧' = δ ∧ h ≫ f'⟦(1 : ℤ)⟧' = π ≫ w := by
  obtain ⟨B', u, w, hB⟩ := distinguished_cocone_triangle₁ (g ≫ π)
  let o := Triangulated.someOctahedron' rfl hT hT' hB
  exact ⟨B', o.m₁, o.m₃, u, w, o.mem, hB, o.comm₁, o.comm₄, o.comm₃, o.comm₂⟩

end CategoryTheory.Pretriangulated

namespace CategoryTheory.Triangulated

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-! ### Counting factors -/

open Classical in
/-- The number of factors of a Postnikov tower that have the property `R`. -/
noncomputable def PostnikovTower.count {E : C} (T : PostnikovTower C E) (R : ObjectProperty C) :
    ℕ :=
  ∑ i : Fin T.n, if R (T.factor i) then 1 else 0

/-- Two towers whose factors correspond, position by position up to isomorphism, have the same
count of every isomorphism-closed property. -/
theorem PostnikovTower.count_eq_of_iso {E E' : C} (T : PostnikovTower C E)
    (T' : PostnikovTower C E') (hn : T.n = T'.n)
    (he : ∀ i : Fin T.n, Nonempty (T.factor i ≅ T'.factor (Fin.cast hn i)))
    (R : ObjectProperty C) [R.IsClosedUnderIsomorphisms] : T.count R = T'.count R := by
  classical
  unfold PostnikovTower.count
  refine Fintype.sum_equiv (finCongr hn) _ _ (fun i => ?_)
  obtain ⟨e⟩ := he i
  simp only [finCongr_apply]
  exact if_congr (R.prop_iff_of_iso e) rfl rfl

/-- The count of a tower whose factors are those of `T₁` followed by those of `T₂`. -/
theorem PostnikovTower.count_eq_add {B A M : C} (T : PostnikovTower C B)
    (T₁ : PostnikovTower C A) (T₂ : PostnikovTower C M) (hn : T.n = T₁.n + T₂.n)
    (h₁ : ∀ i : Fin T₁.n, Nonempty (T.factor ⟨i, by omega⟩ ≅ T₁.factor i))
    (h₂ : ∀ j : Fin T₂.n, Nonempty (T.factor ⟨T₁.n + j, by omega⟩ ≅ T₂.factor j))
    (R : ObjectProperty C) [R.IsClosedUnderIsomorphisms] :
    T.count R = T₁.count R + T₂.count R := by
  classical
  unfold PostnikovTower.count
  rw [Fintype.sum_equiv (finCongr hn) _
    (fun i => if R (T.factor ((finCongr hn).symm i)) then 1 else 0) (fun i => by simp),
    Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    obtain ⟨e⟩ := h₁ i
    exact if_congr (R.prop_iff_of_iso e) rfl rfl
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    obtain ⟨e⟩ := h₂ j
    exact if_congr (R.prop_iff_of_iso e) rfl rfl

/-! ### Appending one factor -/

section appendFactor

variable {P : ℝ → ObjectProperty C} {Y Z : C} (G : HNFiltration C P Y) (T : Triangle C)
  (hT : T ∈ distTriang C) (e₁ : T.obj₁ ≅ Y) (e₂ : T.obj₂ ≅ Z) (ψ : ℝ) (hψ : P ψ T.obj₃)
  (hψ_lt : ∀ i : Fin G.n, ψ < G.φ i)

@[simp]
theorem HNFiltration.appendFactor_n : (G.appendFactor C T hT e₁ e₂ ψ hψ hψ_lt).n = G.n + 1 :=
  rfl

theorem HNFiltration.appendFactor_φ_of_lt (i : Fin (G.n + 1)) (hi : i.val < G.n) :
    (G.appendFactor C T hT e₁ e₂ ψ hψ hψ_lt).φ i = G.φ ⟨i, hi⟩ := by
  simp [HNFiltration.appendFactor, hi]

theorem HNFiltration.appendFactor_φ_of_eq (i : Fin (G.n + 1)) (hi : i.val = G.n) :
    (G.appendFactor C T hT e₁ e₂ ψ hψ hψ_lt).φ i = ψ := by
  simp [HNFiltration.appendFactor, hi]

theorem HNFiltration.appendFactor_factor_of_lt (i : Fin (G.n + 1)) (hi : i.val < G.n) :
    (G.appendFactor C T hT e₁ e₂ ψ hψ hψ_lt).factor i = G.factor ⟨i, hi⟩ := by
  simp [HNFiltration.appendFactor, PostnikovTower.factor, hi]

theorem HNFiltration.appendFactor_factor_of_eq (i : Fin (G.n + 1)) (hi : i.val = G.n) :
    (G.appendFactor C T hT e₁ e₂ ψ hψ hψ_lt).factor i = T.obj₃ := by
  simp [HNFiltration.appendFactor, PostnikovTower.factor, hi]

end appendFactor

/-! ### Concatenation along a triangle -/

/-- **Concatenation of HN filtrations along a triangle.** Let `A → B → M → A⟦1⟧` be
distinguished, and let `A` and `M` carry HN filtrations for the same phase predicate, every phase
of `M` below every phase of `A`. Then `B` has an HN filtration whose factors and phases are those
of `A` followed by those of `M`. Its chain is `0 → ⋯ → A = B₀ → B₁ → ⋯ → B_s = B` with
`B_i = B ×_M M_i` (`Pretriangulated.exists_pullback_triangles`). -/
theorem HNFiltration.exists_concat [IsTriangulated C] {P : ℝ → ObjectProperty C} {A B M : C}
    (FA : HNFiltration C P A) (FM : HNFiltration C P M)
    {f : A ⟶ B} {g : B ⟶ M} {h : M ⟶ A⟦(1 : ℤ)⟧} (hT : Triangle.mk f g h ∈ distTriang C)
    (hsep : ∀ i j, FM.φ j < FA.φ i) :
    ∃ (FB : HNFiltration C P B) (hn : FB.n = FA.n + FM.n),
      (∀ i : Fin FA.n, FB.φ ⟨i, by omega⟩ = FA.φ i ∧
        Nonempty (FB.factor ⟨i, by omega⟩ ≅ FA.factor i)) ∧
      (∀ j : Fin FM.n, FB.φ ⟨FA.n + j, by omega⟩ = FM.φ j ∧
        Nonempty (FB.factor ⟨FA.n + j, by omega⟩ ≅ FM.factor j)) := by
  suffices key : ∀ (s : ℕ) {M B : C} (FM : HNFiltration C P M) (f : A ⟶ B) (g : B ⟶ M)
      (h : M ⟶ A⟦(1 : ℤ)⟧), FM.n = s → Triangle.mk f g h ∈ distTriang C →
      (∀ i j, FM.φ j < FA.φ i) →
      ∃ (FB : HNFiltration C P B) (hn : FB.n = FA.n + FM.n),
        (∀ i : Fin FA.n, FB.φ ⟨i, by omega⟩ = FA.φ i ∧
          Nonempty (FB.factor ⟨i, by omega⟩ ≅ FA.factor i)) ∧
        (∀ j : Fin FM.n, FB.φ ⟨FA.n + j, by omega⟩ = FM.φ j ∧
          Nonempty (FB.factor ⟨FA.n + j, by omega⟩ ≅ FM.factor j)) from
    key FM.n FM f g h rfl hT hsep
  intro s
  induction s with
  | zero =>
      intro M B FM f g h hs hT _
      have hM : IsZero M := FM.isZero_of_length_zero hs
      have : IsIso f := (Triangle.isZero₃_iff_isIso₁ _ hT).mp hM
      exact ⟨FA.ofIso C (asIso f), by simp [hs], fun i => ⟨rfl, ⟨Iso.refl _⟩⟩,
        fun j => absurd j.isLt (by omega)⟩
  | succ s ih =>
      intro M B FM f g h hs hT hsep
      have hpos : 0 < FM.n := by omega
      let TM := FM.triangle ⟨FM.n - 1, by omega⟩
      let eM : TM.obj₂ ≅ M := FM.lastTriangleObj₂Iso hpos
      let eM₁ := FM.lastTriangleObj₁Iso hpos
      have hTM : Triangle.mk (TM.mor₁ ≫ eM.hom) (eM.inv ≫ TM.mor₂) TM.mor₃ ∈ distTriang C := by
        refine isomorphic_distinguished _ (FM.triangle_dist ⟨FM.n - 1, by omega⟩) _ ?_
        exact Triangle.isoMk _ _ (Iso.refl _) eM.symm (Iso.refl _) (by dsimp [TM]; simp)
          (by dsimp [TM]; simp) (by dsimp [TM]; simp)
      obtain ⟨B', f', g', u, w, h₁, h₂, -, -, -, -⟩ :=
        Pretriangulated.exists_pullback_triangles hT hTM
      let FM' : HNFiltration C P TM.obj₁ :=
        (FM.prefix C (FM.n - 1) (by omega)).ofIso C eM₁.symm
      have hFM'n : FM'.n = FM.n - 1 := rfl
      have hFM'φ : ∀ j : Fin FM'.n, FM'.φ j = FM.φ ⟨j, by omega⟩ := fun _ => rfl
      have hFM'f : ∀ j : Fin FM'.n, FM'.factor j = FM.factor ⟨j, by omega⟩ := fun _ => rfl
      obtain ⟨FB', hn', hA', hM'⟩ := ih FM' f' g' ((TM.mor₁ ≫ eM.hom) ≫ h) (by omega) h₁
        (fun i j => by rw [hFM'φ]; exact hsep _ _)
      let ψ := FM.φ ⟨FM.n - 1, by omega⟩
      have hψ : P ψ (Triangle.mk u (g ≫ eM.inv ≫ TM.mor₂) w).obj₃ :=
        FM.semistable ⟨FM.n - 1, by omega⟩
      have hψ_lt : ∀ i : Fin FB'.n, ψ < FB'.φ i := by
        intro i
        by_cases hi : i.val < FA.n
        · have := (hA' ⟨i, hi⟩).1
          rw [show i = ⟨(⟨i, hi⟩ : Fin FA.n), by omega⟩ from rfl, this]
          exact hsep _ _
        · have hj : i.val - FA.n < FM'.n := by omega
          have := (hM' ⟨i.val - FA.n, hj⟩).1
          rw [show i = ⟨FA.n + (⟨i.val - FA.n, hj⟩ : Fin FM'.n), by simp; omega⟩ from
            Fin.ext (by simp; omega), this, hFM'φ]
          exact FM.hφ (Fin.mk_lt_mk.mpr (by simp; omega))
      let FB := FB'.appendFactor C (Triangle.mk u (g ≫ eM.inv ≫ TM.mor₂) w) h₂ (Iso.refl _)
        (Iso.refl _) ψ hψ hψ_lt
      have hFBn : FB.n = FB'.n + 1 := rfl
      have hφlt : ∀ (i : Fin (FB'.n + 1)) (hi : i.val < FB'.n), FB.φ i = FB'.φ ⟨i, hi⟩ :=
        fun i hi => HNFiltration.appendFactor_φ_of_lt FB' _ h₂ _ _ ψ hψ hψ_lt i hi
      have hflt : ∀ (i : Fin (FB'.n + 1)) (hi : i.val < FB'.n),
          FB.factor i = FB'.factor ⟨i, hi⟩ :=
        fun i hi => HNFiltration.appendFactor_factor_of_lt FB' _ h₂ _ _ ψ hψ hψ_lt i hi
      have hφeq : ∀ (i : Fin (FB'.n + 1)), i.val = FB'.n → FB.φ i = ψ :=
        fun i hi => HNFiltration.appendFactor_φ_of_eq FB' _ h₂ _ _ ψ hψ hψ_lt i hi
      have hfeq : ∀ (i : Fin (FB'.n + 1)), i.val = FB'.n →
          FB.factor i = FM.factor ⟨FM.n - 1, by omega⟩ :=
        fun i hi => HNFiltration.appendFactor_factor_of_eq FB' _ h₂ _ _ ψ hψ hψ_lt i hi
      refine ⟨FB, by omega, fun i => ?_, fun j => ?_⟩
      · have hi : (⟨i, by omega⟩ : Fin (FB'.n + 1)).val < FB'.n := by simp; omega
        exact ⟨(hφlt _ hi).trans (hA' i).1, (hflt _ hi) ▸ (hA' i).2⟩
      · by_cases hj : j.val < FM.n - 1
        · have hi : (⟨FA.n + j, by omega⟩ : Fin (FB'.n + 1)).val < FB'.n := by simp; omega
          have h1 := (hM' ⟨j, hj⟩).1
          have h2 := (hM' ⟨j, hj⟩).2
          rw [hFM'φ] at h1
          rw [hFM'f] at h2
          exact ⟨(hφlt _ hi).trans h1, (hflt _ hi) ▸ h2⟩
        · have hi : (⟨FA.n + j, by omega⟩ : Fin (FB'.n + 1)).val = FB'.n := by simp; omega
          have hjl : j = ⟨FM.n - 1, by omega⟩ := Fin.ext (by have := j.isLt; simp; omega)
          exact ⟨(hφeq _ hi).trans (by rw [hjl]),
            ⟨eqToIso ((hfeq _ hi).trans (congrArg FM.factor hjl.symm))⟩⟩

/-! ### Refinement of every factor -/

/-- **Refinement of an HN filtration by HN filtrations of its factors.** Let `F` be an HN
filtration of `E` (for a phase predicate `P`, say a wall), and let each factor of `F` carry an HN
filtration for `Q` (say the outgoing side), the phases of later factors below those of earlier
ones. Then `E` has an HN filtration for `Q` whose factors are, up to isomorphism, the factors of
the pieces: each of its phases and factors comes from a piece, and every isomorphism-closed
property of factors is counted as the sum over the pieces. -/
theorem HNFiltration.exists_refinement [IsTriangulated C] {P Q : ℝ → ObjectProperty C} {E : C}
    (F : HNFiltration C P E) (G : ∀ k : Fin F.n, HNFiltration C Q (F.factor k))
    (hsep : ∀ k l : Fin F.n, k < l → ∀ i j, (G l).φ j < (G k).φ i) :
    ∃ H : HNFiltration C Q E,
      (∀ i, ∃ k j, H.φ i = (G k).φ j ∧ Nonempty (H.factor i ≅ (G k).factor j)) ∧
      ∀ (R : ObjectProperty C) [R.IsClosedUnderIsomorphisms],
        H.count R = ∑ k, (G k).count R := by
  classical
  -- The statement for the prefix ending at the `k`-th chain object.
  have step : ∀ (k : ℕ) (hk : k ≤ F.n), ∃ H : HNFiltration C Q (F.chain.obj ⟨k, by omega⟩),
      (∀ i, ∃ (l : Fin F.n) (j : Fin (G l).n), l.val < k ∧ H.φ i = (G l).φ j ∧
        Nonempty (H.factor i ≅ (G l).factor j)) ∧
      ∀ (R : ObjectProperty C) [R.IsClosedUnderIsomorphisms],
        H.count R = ∑ l : Fin F.n, if l.val < k then (G l).count R else 0 := by
    intro k
    induction k with
    | zero =>
        intro hk
        refine ⟨HNFiltration.zero C _ F.base_isZero, fun i => Fin.elim0 i, fun R _ => ?_⟩
        simp [PostnikovTower.count, HNFiltration.zero]
    | succ k ih =>
        intro hk
        obtain ⟨H, hφ, hcount⟩ := ih (by omega)
        let T := F.triangle ⟨k, by omega⟩
        let e₁ : T.obj₁ ≅ F.chain.obj ⟨k, by omega⟩ :=
          Classical.choice (F.triangle_obj₁ ⟨k, by omega⟩)
        let e₂ : T.obj₂ ≅ F.chain.obj ⟨k + 1, by omega⟩ :=
          Classical.choice (F.triangle_obj₂ ⟨k, by omega⟩)
        let FA : HNFiltration C Q T.obj₁ := H.ofIso C e₁.symm
        have hT : Triangle.mk T.mor₁ T.mor₂ T.mor₃ ∈ distTriang C :=
          F.triangle_dist ⟨k, by omega⟩
        let kk : Fin F.n := ⟨k, by omega⟩
        have hsep' : ∀ (i : Fin FA.n) (j : Fin (G kk).n), (G kk).φ j < FA.φ i := by
          intro i j
          obtain ⟨l, j', hl, hφ', -⟩ := hφ i
          rw [show FA.φ i = H.φ i from rfl, hφ']
          exact hsep l kk (Fin.mk_lt_mk.mpr hl) j' j
        obtain ⟨FB, hn, hA, hM⟩ := HNFiltration.exists_concat FA (G kk) hT hsep'
        refine ⟨FB.ofIso C e₂, fun i => ?_, fun R _ => ?_⟩
        · by_cases hi : i.val < FA.n
          · obtain ⟨hφi, ⟨ei⟩⟩ := hA ⟨i, hi⟩
            obtain ⟨l, j', hl, hφ', ⟨e'⟩⟩ := hφ ⟨i, hi⟩
            refine ⟨l, j', by omega, ?_, ⟨?_⟩⟩
            · exact hφi.trans hφ'
            · exact ei.trans e'
          · have hlt : i.val < FA.n + (G kk).n := by
              have h1 := i.isLt
              have h2 : (FB.ofIso C e₂).n = FB.n := rfl
              omega
            let j : Fin (G kk).n := ⟨i.val - FA.n, by omega⟩
            have hjv : j.val = i.val - FA.n := rfl
            have hidx : (i : Fin FB.n) = ⟨FA.n + j.val, by omega⟩ :=
              Fin.ext (show i.val = FA.n + j.val by omega)
            obtain ⟨hφj, ⟨ej⟩⟩ := hM j
            exact ⟨kk, j, Nat.lt_succ_self k, (congrArg FB.φ hidx).trans hφj,
              ⟨(eqToIso (congrArg FB.factor hidx)).trans ej⟩⟩
        · have hadd := PostnikovTower.count_eq_add FB.toPostnikovTower FA.toPostnikovTower
            (G ⟨k, by omega⟩).toPostnikovTower hn (fun i => (hA i).2) (fun j => (hM j).2) R
          have hFA : FA.count R = H.count R := rfl
          change FB.count R = _
          have hsplit : ∀ l : Fin F.n, (if l.val < k + 1 then (G l).count R else 0) =
              (if l.val < k then (G l).count R else 0) + (if l = kk then (G l).count R else 0) := by
            intro l
            by_cases h1 : l.val < k
            · have h2 : l ≠ kk := fun h => by
                subst h
                exact lt_irrefl k h1
              simp [h1, h2, show l.val < k + 1 by omega]
            · by_cases h3 : l = kk
              · subst h3
                simp [kk]
              · have h4 : ¬ l.val < k + 1 := fun h => h3 (Fin.ext (by simp [kk]; omega))
                simp [h1, h3, h4]
          rw [hadd, hFA, hcount R, Finset.sum_congr rfl (fun l _ => hsplit l),
            Finset.sum_add_distrib, Finset.sum_ite_eq']
          simp [kk]
  obtain ⟨H, hφ, hcount⟩ := step F.n le_rfl
  let eE : F.chain.obj ⟨F.n, by omega⟩ ≅ E := Classical.choice F.top_iso
  refine ⟨H.ofIso C eE, fun i => ?_, fun R _ => ?_⟩
  · obtain ⟨l, j, -, hφ', he⟩ := hφ i
    exact ⟨l, j, hφ', he⟩
  · rw [show (H.ofIso C eE).count R = H.count R from rfl, hcount R]
    exact Finset.sum_congr rfl (fun l _ => by simp [l.isLt])

end CategoryTheory.Triangulated
