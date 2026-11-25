/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Foundation.PreStabilityCondition
import K3Twists.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.ConeHN

/-!
# One unit of weight

Fix a pre-stability condition `σ = (P, Z)` and a real number `a`, and write

  `w(E) = Im(e^{-iπa} Z(E))`

(`PreStabilityCondition.WithClassMap.imChargeAt`). It is additive on distinguished triangles,
vanishes on the slices `P(a)` and `P(a + 1)`, and is positive on nonzero semistable objects of
phase in `(a, a + 1)`. The **one-unit-of-weight lemma**
(`PreStabilityCondition.WithClassMap.one_unit_of_weight`): suppose every nonzero semistable
object with phase in `(a, a + 1)` has `w ≥ δ`, for some `δ > 0` (for example when
`w(Λ) ⊆ δℤ`: `PreStabilityCondition.WithClassMap.le_imChargeAt_of_mem_zmultiples`). If `E` has
all phases in `[a, a + 1]` (for instance if it is the middle term of a distinguished triangle
whose ends have that property: `PreStabilityCondition.WithClassMap.one_unit_of_weight_of_triangle`)
and `0 < w(E) < 2δ`, then the HN tower of `E` is

  `0 → T → E' → E`,  with factors `T`, `S`, `B`,

where `T = E_{≥ a+1}` is the full top term of phase `a + 1`, `B` is the full bottom quotient of
phase `a`, `E' = fib(E → B) = E_{> a}`, and `S = cofib(T → E')` is semistable of a phase
`ψ ∈ (a, a + 1)` with `w(S) = w(E)` and *stable*: it has no proper extension of two nonzero
objects of `P(ψ)`. Any of `T` and `B` may be zero.

## Implementation notes

The hypothesis is stated for nonzero semistable objects of phase in `(a, a + 1)` rather than for
their stable factors. When the slices are of finite length (a locally finite stability
condition), the two agree: a semistable object has a Jordan–Hölder filtration in its slice, and
`w` adds over it. Stability of `S` is stated as the absence of a distinguished triangle
`S₁ → S → S₂ → S₁⟦1⟧` with `S₁`, `S₂` nonzero objects of `P(ψ)`, which is simplicity in the
abelian slice `P(ψ)` (Bridgeland, arXiv:math/0212237, Lemma 5.2).

## Tags

stability condition, central charge, Harder–Narasimhan filtration, stable object
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v u'

namespace CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

/-! ### The rotated imaginary charge -/

/-- The imaginary part `Im(e^{-iπa} Z(E))` of the central charge rotated so that the ray of
phase `a` is the positive real axis. -/
def imChargeAt (σ : WithClassMap C v) (a : ℝ) (E : C) : ℝ :=
  (Complex.exp ((-(Real.pi * a) : ℝ) * Complex.I) * σ.charge E).im

variable (σ : WithClassMap C v) (a : ℝ)

/-- The rotated imaginary charge of a zero object vanishes. -/
theorem imChargeAt_isZero {E : C} (hE : IsZero E) : σ.imChargeAt a E = 0 := by
  simp [imChargeAt, σ.charge_isZero hE]

/-- The rotated imaginary charge is additive on distinguished triangles. -/
theorem imChargeAt_triangle (T : Triangle C) (hT : T ∈ distTriang C) :
    σ.imChargeAt a T.obj₂ = σ.imChargeAt a T.obj₁ + σ.imChargeAt a T.obj₃ := by
  simp only [imChargeAt, charge_def, classOf_triangle C v T hT, map_add, mul_add,
    Complex.add_im]

/-- The rotated imaginary charge of an object is the sum over the factors of a Postnikov tower. -/
theorem imChargeAt_postnikovTower_eq_sum {E : C} (P : PostnikovTower C E) :
    σ.imChargeAt a E = ∑ i : Fin P.n, σ.imChargeAt a (P.factor i) := by
  simp only [imChargeAt, σ.charge_postnikovTower_eq_sum P, Finset.mul_sum, Complex.im_sum]

/-- On a semistable object of phase `ψ`, the rotated imaginary charge is `m sin(π(ψ - a))` for
some `m ≥ 0`, positive when the object is nonzero. -/
theorem exists_imChargeAt_eq_of_semistable {ψ : ℝ} {X : C} (hX : σ.slicing.P ψ X) :
    ∃ m : ℝ, 0 ≤ m ∧ (¬IsZero X → 0 < m) ∧
      σ.imChargeAt a X = m * Real.sin (Real.pi * (ψ - a)) := by
  by_cases hX0 : IsZero X
  · exact ⟨0, le_rfl, fun h => absurd hX0 h, by simp [σ.imChargeAt_isZero a hX0]⟩
  obtain ⟨m, hm, hZ⟩ := σ.compat ψ X hX hX0
  refine ⟨m, hm.le, fun _ => hm, ?_⟩
  have hrot : Complex.exp ((-(Real.pi * a) : ℝ) * Complex.I) *
      ((m : ℂ) * Complex.exp ((Real.pi * ψ : ℝ) * Complex.I)) =
      (m : ℂ) * Complex.exp ((Real.pi * (ψ - a) : ℝ) * Complex.I) := by
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [imChargeAt, hZ, hrot, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]

/-- The rotated imaginary charge vanishes on the slice of phase `a`. -/
theorem imChargeAt_eq_zero_of_semistable_bottom {X : C} (hX : σ.slicing.P a X) :
    σ.imChargeAt a X = 0 := by
  obtain ⟨m, -, -, h⟩ := σ.exists_imChargeAt_eq_of_semistable a hX
  simp [h]

/-- The rotated imaginary charge vanishes on the slice of phase `a + 1`. -/
theorem imChargeAt_eq_zero_of_semistable_top {X : C} (hX : σ.slicing.P (a + 1) X) :
    σ.imChargeAt a X = 0 := by
  obtain ⟨m, -, -, h⟩ := σ.exists_imChargeAt_eq_of_semistable a hX
  simp [h, Real.sin_pi]

/-- The rotated imaginary charge is nonnegative on semistable objects of phase in
`[a, a + 1]`. -/
theorem imChargeAt_nonneg_of_semistable {ψ : ℝ} {X : C} (hX : σ.slicing.P ψ X) (h₁ : a ≤ ψ)
    (h₂ : ψ ≤ a + 1) : 0 ≤ σ.imChargeAt a X := by
  obtain ⟨m, hm, -, h⟩ := σ.exists_imChargeAt_eq_of_semistable a hX
  rw [h]
  exact mul_nonneg hm (Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos])
    (by nlinarith [Real.pi_pos]))

/-- The rotated imaginary charge is positive on nonzero semistable objects of phase in
`(a, a + 1)`. -/
theorem imChargeAt_pos_of_semistable {ψ : ℝ} {X : C} (hX : σ.slicing.P ψ X) (hX0 : ¬IsZero X)
    (h₁ : a < ψ) (h₂ : ψ < a + 1) : 0 < σ.imChargeAt a X := by
  obtain ⟨m, -, hm, h⟩ := σ.exists_imChargeAt_eq_of_semistable a hX
  rw [h]
  exact mul_pos (hm hX0) (Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos])
    (by nlinarith [Real.pi_pos]))

/-- **Integral weights.** If the rotated imaginary charge takes values in `δℤ` on the lattice
`Λ`, then every nonzero semistable object of phase in `(a, a + 1)` has rotated imaginary charge
at least `δ`. -/
theorem le_imChargeAt_of_mem_zmultiples {δ : ℝ} (hδ : 0 < δ)
    (hΛ : ∀ γ : Λ, ∃ n : ℤ, (Complex.exp ((-(Real.pi * a) : ℝ) * Complex.I) * σ.Z γ).im = n * δ)
    {ψ : ℝ} {X : C} (hX : σ.slicing.P ψ X) (hX0 : ¬IsZero X) (h₁ : a < ψ) (h₂ : ψ < a + 1) :
    δ ≤ σ.imChargeAt a X := by
  have hpos := σ.imChargeAt_pos_of_semistable a hX hX0 h₁ h₂
  obtain ⟨n, hn⟩ := hΛ (classOf C v X)
  have hn' : σ.imChargeAt a X = n * δ := hn
  rw [hn'] at hpos ⊢
  have : (0 : ℝ) < n := pos_of_mul_pos_left hpos hδ.le
  have : (1 : ℝ) ≤ n := by exact_mod_cast (show (0 : ℤ) < n by exact_mod_cast this)
  nlinarith

/-! ### The lemma -/

/-- Phases at least `a + 1` are above `a`. -/
private theorem gtProp_of_geProp_add_one (s : Slicing C) {X : C} (hX : s.geProp C (a + 1) X) :
    s.gtProp C a X := by
  rcases hX with hX | ⟨F, hF, hle⟩
  · exact Or.inl hX
  · exact Or.inr ⟨F, hF, by linarith⟩

/-- **The one-unit-of-weight lemma.** Let `σ` be a pre-stability condition, `a` real, `δ > 0`,
and suppose every nonzero semistable object of phase in `(a, a + 1)` has `w = Im(e^{-iπa} Z)` at
least `δ`. Let `E` have all phases in `[a, a + 1]` with `0 < w(E) < 2δ`. Then `E` has the HN
tower `0 → T → E' → E`: there are distinguished triangles `T → E' → S → T⟦1⟧` and
`E' → E → B → E'⟦1⟧` with

* `T` semistable of phase `a + 1`, and `T → E' → E` the top truncation `E_{≥ a+1}`;
* `B` semistable of phase `a`, and `E' → E` the truncation `E_{> a}`, so `E' = fib(E → B)`;
* `S` nonzero, semistable of a phase `ψ ∈ (a, a + 1)`, with `w(S) = w(E)`, and stable: no
  distinguished triangle `S₁ → S → S₂ → S₁⟦1⟧` has `S₁`, `S₂` nonzero objects of `P(ψ)`. -/
theorem one_unit_of_weight [IsTriangulated C] {δ : ℝ}
    (hw : ∀ (ψ : ℝ) (X : C), a < ψ → ψ < a + 1 → σ.slicing.P ψ X → ¬IsZero X →
      δ ≤ σ.imChargeAt a X)
    {E : C} (hE₁ : σ.slicing.geProp C a E) (hE₂ : σ.slicing.leProp C (a + 1) E)
    (hpos : 0 < σ.imChargeAt a E) (hlt : σ.imChargeAt a E < 2 * δ) :
    ∃ (T E' S B : C) (f : T ⟶ E') (g : E' ⟶ S) (h : S ⟶ T⟦(1 : ℤ)⟧) (ι : E' ⟶ E)
      (π : E ⟶ B) (ε : B ⟶ E'⟦(1 : ℤ)⟧) (ψ : ℝ),
      Triangle.mk f g h ∈ distTriang C ∧ Triangle.mk ι π ε ∈ distTriang C ∧
      σ.slicing.P (a + 1) T ∧ (σ.slicing.geProp C (a + 1)).IsCoreflection (f ≫ ι) ∧
      σ.slicing.P a B ∧ (σ.slicing.gtProp C a).IsCoreflection ι ∧
      a < ψ ∧ ψ < a + 1 ∧ σ.slicing.P ψ S ∧ ¬IsZero S ∧
      σ.imChargeAt a S = σ.imChargeAt a E ∧
      ∀ ⦃S₁ S₂ : C⦄ {f₁ : S₁ ⟶ S} {g₁ : S ⟶ S₂} {h₁ : S₂ ⟶ S₁⟦(1 : ℤ)⟧},
        Triangle.mk f₁ g₁ h₁ ∈ distTriang C → σ.slicing.P ψ S₁ → σ.slicing.P ψ S₂ →
          IsZero S₁ ∨ IsZero S₂ := by
  set s := σ.slicing
  -- The top term `T = E_{≥ a+1}` and the rest `R`.
  obtain ⟨T, R, f₀, p, h₀, hTR, hT, hR⟩ := s.exists_split_geProp_ltProp (a + 1) E
  have hf₀ := s.isCoreflection_geProp_of_top hTR hT hR
  have hTP : s.P (a + 1) T := s.semistable_of_isCoreflection_geProp hf₀ hE₂
  have hRa : s.geProp C a R := s.geProp_ext₂ (rot_of_distTriang _ hTR) hE₁
    (s.geProp_anti C (by linarith) _ (s.geProp_shift_one hT))
  -- The bottom quotient `B = R_{≤ a}` and the middle `S = R_{> a}`.
  obtain ⟨S, B, f₁, π, h₁, hSB, hS, hB⟩ := s.exists_split_gtProp_leProp a R
  have hf₁ := s.isCoreflection_gtProp_of_triangle hSB hS hB
  have hBa : s.geProp C a B := s.geProp_ext₂ (rot_of_distTriang _ hSB) hRa
    (s.geProp_of_gtProp C _ (s.gtProp_shift_one hS))
  have hBP : s.P a B := s.semistable_of_geProp_of_leProp hBa hB
  have hSlt : s.ltProp C (a + 1) S := s.ltProp_iff_hom_eq_zero.2 fun X hX g =>
    hf₁.hom_ext (gtProp_of_geProp_add_one a s hX)
      (by rw [zero_comp]; exact s.hom_eq_zero_of_geProp_ltProp hX hR _)
  -- `E' = fib(E → R → B)`, the homotopy pullback.
  obtain ⟨E', f, g, ι, ε, hE'₁, hE'₂, hfι, -, -, -⟩ := exists_pullback_triangles hTR hSB
  have hE'gt : s.gtProp C a E' :=
    s.gtProp_ext₂ hE'₁ (gtProp_of_geProp_add_one a s hT) hS
  -- Weights.
  have hwT : σ.imChargeAt a T = 0 := σ.imChargeAt_eq_zero_of_semistable_top a hTP
  have hwB : σ.imChargeAt a B = 0 := σ.imChargeAt_eq_zero_of_semistable_bottom a hBP
  have hwS : σ.imChargeAt a S = σ.imChargeAt a E := by
    have h₁ := σ.imChargeAt_triangle a _ hTR
    have h₂ := σ.imChargeAt_triangle a _ hSB
    simp only [Triangle.mk_obj₁, Triangle.mk_obj₂, Triangle.mk_obj₃] at h₁ h₂
    linarith
  have hS0 : ¬IsZero S := fun h0 => by
    rw [σ.imChargeAt_isZero a h0] at hwS
    linarith
  -- `S` is semistable: its HN filtration has a single nonzero factor.
  obtain ⟨F, hn, hfirst, hlast⟩ := s.exists_hn_nonzero_boundaries C hS0
  have hplus : F.phiPlus C hn < a + 1 := by
    rcases hSlt with hZ | ⟨G, hG, hGlt⟩
    · exact absurd hZ hS0
    · exact (F.phiPlus_le_of_firstFactor_nonzero C s G hn hG hfirst).trans_lt hGlt
  have hminus : a < F.phiMinus C hn := by
    rcases hS with hZ | ⟨G, hG, hGgt⟩
    · exact absurd hZ hS0
    · exact hGgt.trans_le (G.phiMinus_le_of_lastFactor_nonzero C s F hG hn hlast)
  have hrange : ∀ i : Fin F.n, a < F.φ i ∧ F.φ i < a + 1 := fun i =>
    ⟨hminus.trans_le (F.phase_mem_range C hn i).1, (F.phase_mem_range C hn i).2.trans_lt hplus⟩
  have hnonneg : ∀ i : Fin F.n, 0 ≤ σ.imChargeAt a (F.factor i) := fun i =>
    σ.imChargeAt_nonneg_of_semistable a (F.semistable i) (hrange i).1.le (hrange i).2.le
  have hn1 : F.n = 1 := by
    by_contra hne
    have hsum := σ.imChargeAt_postnikovTower_eq_sum a F.toPostnikovTower
    have hne' : (⟨0, hn⟩ : Fin F.n) ≠ ⟨F.n - 1, by omega⟩ := fun h => hne (by
      have := congrArg Fin.val h
      simp at this
      omega)
    have hpair : σ.imChargeAt a (F.factor ⟨0, hn⟩) +
        σ.imChargeAt a (F.factor ⟨F.n - 1, by omega⟩) ≤ σ.imChargeAt a S := by
      rw [hsum, ← Finset.sum_pair (f := fun i => σ.imChargeAt a (F.factor i)) hne']
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => hnonneg i)
    have h₁ := hw _ _ (hrange _).1 (hrange _).2 (F.semistable ⟨0, hn⟩) hfirst
    have h₂ := hw _ _ (hrange _).1 (hrange _).2 (F.semistable ⟨F.n - 1, by omega⟩) hlast
    linarith
  have hSP : s.P (F.φ ⟨0, by omega⟩) S := F.semistable_of_length_one C s.closedUnderIso hn1
  refine ⟨T, E', S, B, f, g, f₁ ≫ h₀, ι, p ≫ π, ε, F.φ ⟨0, by omega⟩, hE'₁, hE'₂, hTP,
    hfι ▸ hf₀, hBP, s.isCoreflection_gtProp_of_triangle hE'₂ hE'gt hB, (hrange _).1,
    (hrange _).2, hSP, hS0, hwS, ?_⟩
  -- Stability of `S`.
  intro S₁ S₂ f₁' g₁' h₁' hT' hS₁ hS₂
  by_contra hcon
  rw [not_or] at hcon
  have hadd := σ.imChargeAt_triangle a _ hT'
  simp only [Triangle.mk_obj₁, Triangle.mk_obj₂, Triangle.mk_obj₃] at hadd
  have h₁ := hw _ _ (hrange _).1 (hrange _).2 hS₁ hcon.1
  have h₂ := hw _ _ (hrange _).1 (hrange _).2 hS₂ hcon.2
  linarith

/-- **The one-unit-of-weight lemma for a triangle.** If `U → E → Q → U⟦1⟧` is distinguished with
both ends of phases in `[a, a + 1]`, so is `E`, and
`PreStabilityCondition.WithClassMap.one_unit_of_weight` applies to `E`. -/
theorem one_unit_of_weight_of_triangle [IsTriangulated C] {δ : ℝ}
    (hw : ∀ (ψ : ℝ) (X : C), a < ψ → ψ < a + 1 → σ.slicing.P ψ X → ¬IsZero X →
      δ ≤ σ.imChargeAt a X)
    {U E Q : C} {u : U ⟶ E} {e : E ⟶ Q} {d : Q ⟶ U⟦(1 : ℤ)⟧}
    (hT : Triangle.mk u e d ∈ distTriang C) (hU₁ : σ.slicing.geProp C a U)
    (hU₂ : σ.slicing.leProp C (a + 1) U) (hQ₁ : σ.slicing.geProp C a Q)
    (hQ₂ : σ.slicing.leProp C (a + 1) Q) (hpos : 0 < σ.imChargeAt a E)
    (hlt : σ.imChargeAt a E < 2 * δ) :
    ∃ (T E' S B : C) (f : T ⟶ E') (g : E' ⟶ S) (h : S ⟶ T⟦(1 : ℤ)⟧) (ι : E' ⟶ E)
      (π : E ⟶ B) (ε : B ⟶ E'⟦(1 : ℤ)⟧) (ψ : ℝ),
      Triangle.mk f g h ∈ distTriang C ∧ Triangle.mk ι π ε ∈ distTriang C ∧
      σ.slicing.P (a + 1) T ∧ (σ.slicing.geProp C (a + 1)).IsCoreflection (f ≫ ι) ∧
      σ.slicing.P a B ∧ (σ.slicing.gtProp C a).IsCoreflection ι ∧
      a < ψ ∧ ψ < a + 1 ∧ σ.slicing.P ψ S ∧ ¬IsZero S ∧
      σ.imChargeAt a S = σ.imChargeAt a E ∧
      ∀ ⦃S₁ S₂ : C⦄ {f₁ : S₁ ⟶ S} {g₁ : S ⟶ S₂} {h₁ : S₂ ⟶ S₁⟦(1 : ℤ)⟧},
        Triangle.mk f₁ g₁ h₁ ∈ distTriang C → σ.slicing.P ψ S₁ → σ.slicing.P ψ S₂ →
          IsZero S₁ ∨ IsZero S₂ :=
  σ.one_unit_of_weight a hw (σ.slicing.geProp_ext₂ hT hU₁ hQ₁)
    (σ.slicing.leProp_ext₂ hT hU₂ hQ₂) hpos hlt

end CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap
