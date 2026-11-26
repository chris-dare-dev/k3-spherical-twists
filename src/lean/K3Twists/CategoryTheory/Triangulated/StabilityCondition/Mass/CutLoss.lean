/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.MassAdditivity

/-!
# The cut-loss lemma

Let `σ = (P, Z)` be a prestability condition on a triangulated category, `m` its mass, and
`E → F → G → E⟦1⟧` a distinguished triangle. The mass of the middle term is controlled by the
part of the third term above the lowest phase `φ⁻(E)` of the first. If `E` has phases at least
`s` and `X → G → Y → X⟦1⟧` cuts `G` at `s`, with `X` of phases at least `s` and `Y` of phases at
most `s` (for instance the truncation `X = G_{>s}`, `Y = G_{≤s}`), then

  `m(E) + m(G) - 2 m(X) ≤ m(F) ≤ m(E) + m(G)`

(`PreStabilityCondition.WithClassMap.mass_add_mass_sub_two_mul_le`; the upper bound is
`PreStabilityCondition.WithClassMap.mass_le_mass_add_mass`). The proof is one octahedron: the
fibre `Y'` of `F → G → Y` is an extension of `X` by `E`
(`Pretriangulated.exists_pullback_triangles`), so it has phases at least `s`; the triangles
`Y' → F → Y` and `X → G → Y` split the masses of `F` and `G` exactly, and subadditivity on
`E → Y' → X` bounds `m(E)` by `m(Y') + m(X)`. Dually, if `G` has phases at most `s` and
`X → E → Y` cuts `E` at `s`, then `m(E) + m(G) - 2 m(Y) ≤ m(F)`
(`PreStabilityCondition.WithClassMap.mass_add_mass_sub_two_mul_le_dual`). The cuts may be any
such triangles: the phase-`s` part may lie on either side. The forms with the canonical
truncations pick `X = G_{>s}` and `Y = E_{<s}`.

Equal phases are allowed throughout. The mass is additive on every distinguished triangle
`U → E → Q → U⟦1⟧` with `U` of phases at least `t` and `Q` of phases at most `t`
(`PreStabilityCondition.WithClassMap.mass_eq_add_of_geProp_leProp`): the cut composite of
`Q → U⟦1⟧` vanishes at every phase (`Slicing.cutVanishes_of_geProp_leProp`), so flag reassembly
applies (`PreStabilityCondition.WithClassMap.mass_eq_add_of_forall_cutVanishes`). This extends
the split identity `PreStabilityCondition.WithClassMap.mass_eq_add_of_triangle`, which needs `U`
of phases above `t`. So the cut `s` may be the lowest phase `φ⁻(E)` of `E`, and when `G` has no
phase above `s` there is no loss: `m(F) = m(E) + m(G)`. The same argument makes the mass additive
on split triangles and on finite biproducts.

The inequalities use Ikeda subadditivity, `m(F) ≤ m(E) + m(G)` on every distinguished triangle,
which for a stability condition is Ikeda, arXiv:1612.00995, Proposition 3.3. The library does not
prove it: it is the hypothesis `PreStabilityCondition.WithClassMap.MassSubadditive`. The
identities do not use it.

## Twist ladders

The intended application is to twist ladders, the cones of `E → T_A^k E` for a spherical twist
`T_A`; twists are not formalized here. When the third term is built from cells `j < k` of phases
`ψ - j`, the cells above a cut `s` number `min k ⌈ψ - s⌉₊`
(`Nat.card_filter_range_lt_sub_eq_min_ceil`), at most `⌈ψ - s⌉₊` whatever the length `k`.

## Main results

* `CategoryTheory.Triangulated.Slicing.cutVanishes_of_geProp_leProp`,
  `PreStabilityCondition.WithClassMap.mass_eq_add_of_geProp_leProp`: **equal-phase additivity**.
* `PreStabilityCondition.WithClassMap.mass_eq_add_of_mor₃_eq_zero`,
  `PreStabilityCondition.WithClassMap.mass_biprod`,
  `PreStabilityCondition.WithClassMap.mass_biproduct`: additivity on split triangles and on
  finite biproducts.
* `PreStabilityCondition.WithClassMap.mass_add_mass_sub_two_mul_le`: **the cut-loss lemma**, with
  the upper bound `PreStabilityCondition.WithClassMap.mass_le_mass_add_mass`, the dual
  `PreStabilityCondition.WithClassMap.mass_add_mass_sub_two_mul_le_dual`, and the forms with the
  canonical truncations `PreStabilityCondition.WithClassMap.exists_mass_add_mass_sub_two_mul_le`
  and `PreStabilityCondition.WithClassMap.exists_mass_add_mass_sub_two_mul_le_dual`.
* `Nat.card_filter_range_lt_eq_min_ceil`, `Nat.card_filter_range_lt_sub_eq_min_ceil`: **the cell
  count**.

## References

* T. Bridgeland, *Stability conditions on triangulated categories*, arXiv:math/0212237, §3, §8.
* A. Ikeda, *Mass growth of objects and categorical entropy*, arXiv:1612.00995, Proposition 3.3.

## Tags

stability condition, mass, triangle, octahedral axiom, spherical twist
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe u v u'

/-! ### The cell count -/

namespace Nat

variable {α : Type*}

/-- **The cell count.** Among `0, 1, …, k - 1`, those below `x` number `min k ⌈x⌉₊`; there are
none when `x ≤ 0`. -/
theorem card_filter_range_lt_eq_min_ceil [Semiring α] [LinearOrder α] [FloorSemiring α]
    (x : α) (k : ℕ) : ((Finset.range k).filter fun j : ℕ ↦ (j : α) < x).card = min k ⌈x⌉₊ := by
  rw [← Finset.card_range (min k ⌈x⌉₊)]
  congr 1
  ext j
  simp [Nat.lt_ceil, lt_min_iff]

/-- **The cell count for a ladder.** Among the phases `ψ - j` for `j < k`, those above a cut `s`
number `min k ⌈ψ - s⌉₊`. -/
theorem card_filter_range_lt_sub_eq_min_ceil [Ring α] [LinearOrder α] [IsOrderedRing α]
    [FloorSemiring α] (ψ s : α) (k : ℕ) :
    ((Finset.range k).filter fun j : ℕ ↦ s < ψ - j).card = min k ⌈ψ - s⌉₊ := by
  rw [← card_filter_range_lt_eq_min_ceil (ψ - s) k]
  congr 1
  exact Finset.filter_congr fun j _ ↦ lt_sub_comm

end Nat

namespace CategoryTheory.Triangulated

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]

/-! ### The cut composite across a weak phase gap -/

/-- **The cut composite vanishes across a weak phase gap.** If `U` has phases at least `t` and `Q`
has phases at most `t`, the cut composite of every map `δ : Q ⟶ U⟦1⟧` vanishes at every phase
`t'`. For `t' ≤ t` the truncation of `U` at `t'` is `U` itself, with zero quotient; for `t' > t`
the coreflection of `Q` into `P(≥ t')` is `0 → Q`. -/
theorem Slicing.cutVanishes_of_geProp_leProp (s : Slicing C) {t : ℝ} {U Q : C}
    (δ : Q ⟶ U⟦(1 : ℤ)⟧) (hU : s.geProp C t U) (hQ : s.leProp C t Q) (t' : ℝ) :
    s.CutVanishes t' δ := by
  rcases le_or_gt t' t with h | h
  · obtain ⟨Q₁, ιQ, hιQ⟩ := s.exists_isCoreflection_geProp t' Q
    refine ⟨U, 0, 𝟙 U, 0, 0, Q₁, ιQ, contractible_distinguished U, s.geProp_anti C h U hU,
      s.ltProp_of_isZero C (isZero_zero C) t', hιQ, ?_⟩
    simp
  · obtain ⟨U₁, U₂, ιU, πU, εU, hTU, hU₁, hU₂⟩ := s.exists_split_geProp_ltProp t' U
    have hQ' : s.ltProp C t' Q := by
      rcases hQ with hQ | ⟨F, hF, hle⟩
      · exact Or.inl hQ
      · exact Or.inr ⟨F, hF, hle.trans_lt h⟩
    refine ⟨U₁, U₂, ιU, πU, εU, 0, 0, hTU, hU₁, hU₂,
      s.isCoreflection_geProp_of_top (contractible_distinguished₁ Q)
        (s.geProp_of_isZero C (isZero_zero C) t') hQ', ?_⟩
    simp

/-- The cut composite of the zero map vanishes at every phase. -/
theorem Slicing.cutVanishes_zero (s : Slicing C) (t : ℝ) (U Q : C) :
    s.CutVanishes t (0 : Q ⟶ U⟦(1 : ℤ)⟧) := by
  obtain ⟨U₁, U₂, ιU, πU, εU, hTU, hU₁, hU₂⟩ := s.exists_split_geProp_ltProp t U
  obtain ⟨Q₁, ιQ, hιQ⟩ := s.exists_isCoreflection_geProp t Q
  exact ⟨U₁, U₂, ιU, πU, εU, Q₁, ιQ, hTU, hU₁, hU₂, hιQ, by simp⟩

namespace PreStabilityCondition.WithClassMap

variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ} (σ : WithClassMap C v)

/-! ### Equal-phase additivity -/

/-- **Equal-phase additivity.** In a distinguished triangle `U → E → Q → U⟦1⟧` with `U` of phases
at least `t` and `Q` of phases at most `t`, `m(E) = m(U) + m(Q)`. Unlike the split identity
`mass_eq_add_of_triangle`, the phase `t` may occur at both ends. In the notation of the cut-loss
lemma this is the case without loss: for `E → F → G` with `E` of phases at least `s` and `G` of
phases at most `s`, `m(F) = m(E) + m(G)`. -/
theorem mass_eq_add_of_geProp_leProp {t : ℝ} {U E Q : C} {u : U ⟶ E} {e : E ⟶ Q}
    {δ : Q ⟶ U⟦(1 : ℤ)⟧} (hT : Triangle.mk u e δ ∈ distTriang C)
    (hU : σ.slicing.geProp C t U) (hQ : σ.slicing.leProp C t Q) :
    σ.mass E = σ.mass U + σ.mass Q :=
  σ.mass_eq_add_of_forall_cutVanishes hT (σ.slicing.cutVanishes_of_geProp_leProp δ hU hQ)

/-! ### Split triangles and biproducts -/

/-- **Additivity on split triangles.** In a distinguished triangle `U → E → Q → U⟦1⟧` whose
connecting map vanishes, `m(E) = m(U) + m(Q)`. -/
theorem mass_eq_add_of_mor₃_eq_zero {U E Q : C} {u : U ⟶ E} {e : E ⟶ Q}
    {δ : Q ⟶ U⟦(1 : ℤ)⟧} (hT : Triangle.mk u e δ ∈ distTriang C) (hδ : δ = 0) :
    σ.mass E = σ.mass U + σ.mass Q := by
  subst hδ
  exact σ.mass_eq_add_of_forall_cutVanishes hT fun t ↦ σ.slicing.cutVanishes_zero t U Q

/-- **The mass is additive on biproducts**: `m(X ⊞ Y) = m(X) + m(Y)`. -/
theorem mass_biprod (X Y : C) : σ.mass (X ⊞ Y) = σ.mass X + σ.mass Y :=
  σ.mass_eq_add_of_mor₃_eq_zero (binaryBiproductTriangle_distinguished X Y) rfl

omit [IsTriangulated C] in
/-- A biproduct indexed by `Fin (n + 1)` splits off its first summand. -/
private def biproductFinSuccIso {n : ℕ} (g : Fin (n + 1) → C) :
    ⨁ g ≅ g 0 ⊞ ⨁ fun i : Fin n ↦ g i.succ where
  hom := biprod.lift (biproduct.π g 0) (biproduct.lift fun i ↦ biproduct.π g i.succ)
  inv := biprod.desc (biproduct.ι g 0) (biproduct.desc fun i ↦ biproduct.ι g i.succ)
  hom_inv_id := by
    rw [biprod.lift_desc, biproduct.lift_desc, ← biproduct.total, Fin.sum_univ_succ]
  inv_hom_id := by
    ext i j <;> simp [biproduct.ι_π, eq_comm (a := (0 : Fin (n + 1)))]

/-- **The mass is additive on finite biproducts**: `m(⨁ f) = ∑ i, m(f i)`. -/
theorem mass_biproduct {ι : Type*} [Fintype ι] (f : ι → C) :
    σ.mass (⨁ f) = ∑ i, σ.mass (f i) := by
  suffices h : ∀ (n : ℕ) (g : Fin n → C), σ.mass (⨁ g) = ∑ i, σ.mass (g i) by
    let e := Finite.equivFin ι
    rw [σ.mass_iso (biproduct.whiskerEquiv e fun j ↦ eqToIso (by simp) :
      ⨁ f ≅ ⨁ fun k ↦ f (e.symm k)), h, e.symm.sum_comp fun i ↦ σ.mass (f i)]
  intro n
  induction n with
  | zero =>
    intro g
    have hz : IsZero (⨁ g) := (IsZero.iff_id_eq_zero _).2 (by rw [← biproduct.total]; simp)
    simp [σ.mass_of_isZero hz]
  | succ n ih =>
    intro g
    rw [σ.mass_iso (biproductFinSuccIso g), σ.mass_biprod, ih, Fin.sum_univ_succ]

/-! ### The cut-loss lemma -/

omit [IsTriangulated C] in
/-- The upper bound of the cut-loss lemma is Ikeda subadditivity: `m(F) ≤ m(E) + m(G)` for every
distinguished triangle `E → F → G → E⟦1⟧`. -/
theorem mass_le_mass_add_mass (hσ : σ.MassSubadditive) {E F G : C} {f : E ⟶ F} {g : F ⟶ G}
    {h : G ⟶ E⟦(1 : ℤ)⟧} (hT : Triangle.mk f g h ∈ distTriang C) :
    σ.mass F ≤ σ.mass E + σ.mass G :=
  hσ _ hT

/-- **The cut-loss lemma.** In a triangle `E → F → G`, the mass of `F` is at most `m(E) + m(G)`
(`mass_le_mass_add_mass`) and loses at most twice the mass of the part of `G` of phases above a
cut `s ≤ φ⁻(E)`. Precisely: let `E → F → G → E⟦1⟧` be distinguished with `E` of phases at least
`s`, and `X → G → Y → X⟦1⟧` distinguished with `X` of phases at least `s` and `Y` of phases at
most `s` (for instance the truncation `X = G_{>s}`, `Y = G_{≤s}`). Under Ikeda subadditivity
(`MassSubadditive`; for a stability condition, Ikeda, arXiv:1612.00995, Proposition 3.3),
`m(E) + m(G) - 2 m(X) ≤ m(F)`. Equal phases are allowed: `s` may be the lowest phase of `E`. -/
theorem mass_add_mass_sub_two_mul_le (hσ : σ.MassSubadditive) {s : ℝ} {E F G : C} {f : E ⟶ F}
    {g : F ⟶ G} {h : G ⟶ E⟦(1 : ℤ)⟧} (hT : Triangle.mk f g h ∈ distTriang C)
    (hE : σ.slicing.geProp C s E) {X Y : C} {i : X ⟶ G} {p : G ⟶ Y} {q : Y ⟶ X⟦(1 : ℤ)⟧}
    (hTX : Triangle.mk i p q ∈ distTriang C) (hX : σ.slicing.geProp C s X)
    (hY : σ.slicing.leProp C s Y) :
    σ.mass E + σ.mass G - 2 * σ.mass X ≤ σ.mass F := by
  -- the fibre `Y'` of `F → G → Y` is an extension of `X` by `E`
  obtain ⟨Y', f', g', u, w, h₁, h₂, -, -, -, -⟩ := exists_pullback_triangles hT hTX
  have hY' : σ.slicing.geProp C s Y' := σ.slicing.geProp_ext₂ h₁ hE hX
  have hF := σ.mass_eq_add_of_geProp_leProp h₂ hY' hY
  have hG := σ.mass_eq_add_of_geProp_leProp hTX hX hY
  have hE' := hσ _ (inv_rot_of_distTriang _ h₁)
  simp only [Triangle.invRotate_obj₁, Triangle.invRotate_obj₂, Triangle.invRotate_obj₃,
    Triangle.mk_obj₁, Triangle.mk_obj₂, Triangle.mk_obj₃, σ.mass_shift] at hE'
  linarith

/-- **The dual cut-loss lemma.** Let `E → F → G → E⟦1⟧` be distinguished with `G` of phases at
most `s`, and `X → E → Y → X⟦1⟧` distinguished with `X` of phases at least `s` and `Y` of phases
at most `s` (for instance the truncation `X = E_{≥s}`, `Y = E_{<s}`). Under Ikeda subadditivity,
`m(E) + m(G) - 2 m(Y) ≤ m(F)`: the mass of `F` loses at most twice the mass of the part of `E`
of phases below a cut `s ≥ φ⁺(G)`. -/
theorem mass_add_mass_sub_two_mul_le_dual (hσ : σ.MassSubadditive) {s : ℝ} {E F G : C}
    {f : E ⟶ F} {g : F ⟶ G} {h : G ⟶ E⟦(1 : ℤ)⟧} (hT : Triangle.mk f g h ∈ distTriang C)
    (hG : σ.slicing.leProp C s G) {X Y : C} {i : X ⟶ E} {p : E ⟶ Y} {q : Y ⟶ X⟦(1 : ℤ)⟧}
    (hTX : Triangle.mk i p q ∈ distTriang C) (hX : σ.slicing.geProp C s X)
    (hY : σ.slicing.leProp C s Y) :
    σ.mass E + σ.mass G - 2 * σ.mass Y ≤ σ.mass F := by
  -- the cofibre `W` of `X → E → F` is an extension of `G` by `Y`
  obtain ⟨W, p', w, m₁, m₃, hW, hM, -, -, -, -⟩ := exists_cofib_triangles hT hTX
  have hW' : σ.slicing.leProp C s W := σ.slicing.leProp_ext₂ hM hY hG
  have hF := σ.mass_eq_add_of_geProp_leProp hW hX hW'
  have hE := σ.mass_eq_add_of_geProp_leProp hTX hX hY
  have hG' := hσ _ (rot_of_distTriang _ hM)
  simp only [Triangle.rotate_obj₁, Triangle.rotate_obj₂, Triangle.rotate_obj₃,
    Triangle.mk_obj₁, Triangle.mk_obj₂, Triangle.mk_obj₃, σ.mass_shift] at hG'
  linarith

/-- **The cut-loss lemma with the canonical truncation.** Let `E → F → G → E⟦1⟧` be
distinguished with `E` of phases at least `s`. Under Ikeda subadditivity, the truncation
`G_{>s} → G → G_{≤s}` satisfies `m(E) + m(G) - 2 m(G_{>s}) ≤ m(F)`. -/
theorem exists_mass_add_mass_sub_two_mul_le (hσ : σ.MassSubadditive) {s : ℝ} {E F G : C}
    {f : E ⟶ F} {g : F ⟶ G} {h : G ⟶ E⟦(1 : ℤ)⟧} (hT : Triangle.mk f g h ∈ distTriang C)
    (hE : σ.slicing.geProp C s E) :
    ∃ (X Y : C) (i : X ⟶ G) (p : G ⟶ Y) (q : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk i p q ∈ distTriang C ∧ σ.slicing.gtProp C s X ∧ σ.slicing.leProp C s Y ∧
        σ.mass E + σ.mass G - 2 * σ.mass X ≤ σ.mass F := by
  obtain ⟨X, Y, i, p, q, hTX, hX, hY⟩ := σ.slicing.exists_split_gtProp_leProp s G
  exact ⟨X, Y, i, p, q, hTX, hX, hY,
    σ.mass_add_mass_sub_two_mul_le hσ hT hE hTX (σ.slicing.geProp_of_gtProp C _ hX) hY⟩

/-- **The dual cut-loss lemma with the canonical truncation.** Let `E → F → G → E⟦1⟧` be
distinguished with `G` of phases at most `s`. Under Ikeda subadditivity, the truncation
`E_{≥s} → E → E_{<s}` satisfies `m(E) + m(G) - 2 m(E_{<s}) ≤ m(F)`. -/
theorem exists_mass_add_mass_sub_two_mul_le_dual (hσ : σ.MassSubadditive) {s : ℝ} {E F G : C}
    {f : E ⟶ F} {g : F ⟶ G} {h : G ⟶ E⟦(1 : ℤ)⟧} (hT : Triangle.mk f g h ∈ distTriang C)
    (hG : σ.slicing.leProp C s G) :
    ∃ (X Y : C) (i : X ⟶ E) (p : E ⟶ Y) (q : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk i p q ∈ distTriang C ∧ σ.slicing.geProp C s X ∧ σ.slicing.ltProp C s Y ∧
        σ.mass E + σ.mass G - 2 * σ.mass Y ≤ σ.mass F := by
  obtain ⟨X, Y, i, p, q, hTX, hX, hY⟩ := σ.slicing.exists_split_geProp_ltProp s E
  exact ⟨X, Y, i, p, q, hTX, hX, hY,
    σ.mass_add_mass_sub_two_mul_le_dual hσ hT hG hTX hX (σ.slicing.leProp_of_ltProp C _ hY)⟩

end PreStabilityCondition.WithClassMap

end CategoryTheory.Triangulated
