/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.CategoryTheory.Abelian.Uniserial
import Mathlib.Basic.Real.Basic

/-!
# The semirigid length-three object at a wall of pairing two

Let `A`, `B` be spherical objects of a K3 surface, stable of one phase at a wall of a stability
condition, with `dim Ext¹(B, A) = 2`; for instance `A = 𝒪_C`, `B = 𝒪_C(-1)[1]` at the wall
where a smooth rational curve `C` is contracted. In the abelian category of semistable objects
of that phase, `A` and `B` are simple. A nonzero `α ∈ Ext¹(B, A)` gives `0 → A → P → B → 0`; a
generator of the line `Ext¹(A, P)` gives `0 → P → M → A → 0`; and the pushout of `M` along
`P → B` is `0 → B → U → A → 0` with `U = M/A`. For a point `x ∈ C` these are `P = 𝒪_x`,
`M = 𝒪_X/(I_C I_x)`, the curve with an embedded point, and `U = T_A 𝒪_x`.

`PairingTwoWallHypotheses` packages these extensions; the `Ext` computations that produce them
are its cited inputs. From them alone, in any abelian category, this file proves:

* `subobject_M`: the subobjects of `M` form the single chain `0 ⊂ A ⊂ P ⊂ M`;
* `hn_of_phase_lt`: on the side of the wall where `B` has the larger phase, `P` is stable,
  every other nonzero subobject of `M` has smaller phase than `P`, and the quotient `M/P = A`
  has smaller phase: the HN filtration of `M` is `0 ⊂ P ⊂ M`, with factors `P`, `A`;
* `hn_of_phase_gt`: on the other side `A ⊂ M` has the largest phase, `U = M/A` is stable of
  smaller phase: the HN filtration is `0 ⊂ A ⊂ M`, with factors `A`, `U`;
* `semistable_of_phase_eq`: on the wall every nonzero subobject of `M` has the phase of `M`:
  `M` is semistable with Jordan–Hölder factors `A`, `B`, `A`.

The phases near the wall are an input as well (`SeesawPhaseHypotheses`): a phase function on
the wall category with the see-saw property, which the restricted central charge has.
-/

namespace AlgebraicGeometry.K3

open CategoryTheory Limits

/-- **A phase function with the see-saw property.** In a short exact sequence
`0 → X₁ → X₂ → X₃ → 0` of nonzero objects the phase of `X₂` lies strictly between those of `X₁`
and `X₃`, or equals both when they agree.

Source: the phase `arg Z(E)/π` of a stability function `Z` on an abelian category has this
property, because `Z(X₂) = Z(X₁) + Z(X₃)` with arguments in `(0, π]` (Bridgeland,
arXiv:math/0212237, §2; Rudakov, *Stability for an abelian category*, J. Algebra 197 (1997)).
Near a wall the HN filtration of a fixed object of the wall category is computed by the charge
restricted to that category (Bayer–Bridgeland, arXiv:1310.8266, Lemma 2.7 and Remark 2.8). -/
structure SeesawPhaseHypotheses (C : Type*) [Category C] [Abelian C] where
  /-- The phase of an object. -/
  phase : C → ℝ
  /-- Isomorphic objects have the same phase. -/
  phase_congr : ∀ {X Y : C}, (X ≅ Y) → phase X = phase Y
  /-- See-saw: a subobject of smaller phase than the quotient. -/
  seesaw_lt : ∀ S : ShortComplex C, S.ShortExact → ¬IsZero S.X₁ → ¬IsZero S.X₃ →
    phase S.X₁ < phase S.X₃ → phase S.X₁ < phase S.X₂ ∧ phase S.X₂ < phase S.X₃
  /-- See-saw: a subobject of larger phase than the quotient. -/
  seesaw_gt : ∀ S : ShortComplex C, S.ShortExact → ¬IsZero S.X₁ → ¬IsZero S.X₃ →
    phase S.X₃ < phase S.X₁ → phase S.X₃ < phase S.X₂ ∧ phase S.X₂ < phase S.X₁
  /-- See-saw: a subobject and a quotient of the same phase. -/
  seesaw_eq : ∀ S : ShortComplex C, S.ShortExact → ¬IsZero S.X₁ → ¬IsZero S.X₃ →
    phase S.X₁ = phase S.X₃ → phase S.X₂ = phase S.X₁

/-- **The extensions at a wall of pairing two.** Simple objects `A`, `B` of the wall category
and the length-three object `M` glued from them:

* `0 → A → P → B → 0` (`j`, `q`), the extension by a nonzero `α ∈ Ext¹(B, A)`, nonsplit;
* `0 → P → M → A → 0` (`i`, `p`), by a generator of `Ext¹(A, P) ≅ (ℂα)^⊥`. This is a line:
  applying `Hom(A, -)` to `P`, with `Ext¹(A, A) = 0`, identifies `Ext¹(A, P)` with the kernel of
  the Yoneda pairing `Ext¹(A, B) → Ext²(A, A) = ℂ` with `α`, and `Ext¹(A, B) = Ext¹(B, A)^*` is
  two-dimensional by Serre duality;
* `0 → A → M → U → 0` (`j ≫ i`, `π`), the quotient `U = M/A`, and `0 → B → U → A → 0`
  (`k`, `l`), the pushout of `M` along `q`, compatible with `p` (`π ≫ l = p`). It is nonsplit
  because `Ext¹(A, A) = 0` makes `Ext¹(A, P) → Ext¹(A, B)` injective.

The `Ext` computations use Serre duality on the K3 surface and the stability of `A`, `B`; they
are the inputs here, not formalized. -/
structure PairingTwoWallHypotheses (C : Type*) [Category C] [Abelian C] where
  /-- The first simple, `𝒪_C` at a curve wall. -/
  A : C
  /-- The second simple, `𝒪_C(-1)[1]` at a curve wall. -/
  B : C
  /-- The length-two extension, `𝒪_x` at a curve wall. -/
  P : C
  /-- The length-three object, `𝒪_X/(I_C I_x)` at a curve wall. -/
  M : C
  /-- The quotient `M/A`, `T_A 𝒪_x` at a curve wall. -/
  U : C
  /-- `A` is simple in the wall category: it is stable of the wall's phase. -/
  simple_A : Simple A
  /-- `B` is simple in the wall category. -/
  simple_B : Simple B
  /-- `A → P`. -/
  j : A ⟶ P
  /-- `P → B`. -/
  q : P ⟶ B
  /-- `P → M`. -/
  i : P ⟶ M
  /-- `M → A`. -/
  p : M ⟶ A
  /-- `B → U`. -/
  k : B ⟶ U
  /-- `U → A`. -/
  l : U ⟶ A
  /-- `M → U = M/A`. -/
  π : M ⟶ U
  zero_jq : j ≫ q = 0
  zero_ip : i ≫ p = 0
  zero_kl : k ≫ l = 0
  zero_π : (j ≫ i) ≫ π = 0
  /-- `0 → A → P → B → 0` is short exact. -/
  shortExact_P : (ShortComplex.mk j q zero_jq).ShortExact
  /-- `0 → P → M → A → 0` is short exact. -/
  shortExact_M : (ShortComplex.mk i p zero_ip).ShortExact
  /-- `0 → B → U → A → 0` is short exact. -/
  shortExact_U : (ShortComplex.mk k l zero_kl).ShortExact
  /-- `0 → A → M → U → 0` is short exact. -/
  shortExact_π : (ShortComplex.mk (j ≫ i) π zero_π).ShortExact
  /-- The projections of `M` and `U` onto `A` agree. -/
  π_l : π ≫ l = p
  /-- `P` does not split: `α ≠ 0`. -/
  nonsplit_P : ∀ σ : B ⟶ P, σ ≫ q ≠ 𝟙 B
  /-- `U` does not split. -/
  nonsplit_U : ∀ σ : A ⟶ U, σ ≫ l ≠ 𝟙 A

namespace PairingTwoWallHypotheses

variable {C : Type*} [Category C] [Abelian C] (W : PairingTwoWallHypotheses C)

attribute [instance] simple_A simple_B

instance : Mono W.j := W.shortExact_P.mono_f
instance : Mono W.i := W.shortExact_M.mono_f
instance : Mono W.k := W.shortExact_U.mono_f

/-- The subobjects of `P` are `0`, `A` and `P`. -/
theorem subobject_P (T : Subobject W.P) : T = ⊥ ∨ T = Subobject.mk W.j ∨ T = ⊤ :=
  W.shortExact_P.subobject_eq_of_nonsplit W.nonsplit_P T

/-- The subobjects of `U` are `0`, `B` and `U`. -/
theorem subobject_U (T : Subobject W.U) : T = ⊥ ∨ T = Subobject.mk W.k ∨ T = ⊤ :=
  W.shortExact_U.subobject_eq_of_nonsplit W.nonsplit_U T

/-- **The subobjects of `M` form a single chain** `0 ⊂ A ⊂ P ⊂ M`. In particular `A` is the
unique simple subobject of `M`, and `M` has no subobject isomorphic to `B`. -/
theorem subobject_M (T : Subobject W.M) :
    T = ⊥ ∨ T = Subobject.mk (W.j ≫ W.i) ∨ T = Subobject.mk W.i ∨ T = ⊤ :=
  subobject_eq_of_nonsplit_of_nonsplit W.zero_jq W.zero_ip W.zero_kl W.zero_π W.shortExact_P
    W.shortExact_M W.shortExact_U W.shortExact_π W.π_l W.nonsplit_P W.nonsplit_U T

lemma not_isZero_A : ¬IsZero W.A := Simple.not_isZero W.A

lemma not_isZero_B : ¬IsZero W.B := Simple.not_isZero W.B

lemma not_isZero_P : ¬IsZero W.P := fun h =>
  id_ne_zero W.A (zero_of_comp_mono W.j (h.eq_of_tgt _ _))

lemma not_isZero_M : ¬IsZero W.M := fun h =>
  id_ne_zero W.A (zero_of_comp_mono (W.j ≫ W.i) (h.eq_of_tgt _ _))

lemma not_isZero_U : ¬IsZero W.U := fun h =>
  id_ne_zero W.B (zero_of_comp_mono W.k (h.eq_of_tgt _ _))

variable (Φ : SeesawPhaseHypotheses C)

lemma phase_mk {X Y : C} (f : X ⟶ Y) [Mono f] :
    Φ.phase (Subobject.mk f : C) = Φ.phase X :=
  Φ.phase_congr (Subobject.underlyingIso f)

lemma phase_top (X : C) : Φ.phase ((⊤ : Subobject X) : C) = Φ.phase X :=
  Φ.phase_congr (asIso (⊤ : Subobject X).arrow)

/-! ### The side where `B` has the larger phase -/

/-- **The HN filtration `0 ⊂ P ⊂ M` where `φ(A) < φ(B)`.** `P` is stable; every nonzero
subobject of `M` other than `P` has phase smaller than `φ(P)`, so `P` is the first step of the
HN filtration of `M`; the quotient `M/P = A` is simple, of phase smaller than `φ(P)`. In
particular `M` is not semistable there: `φ(M) < φ(P)`. -/
theorem hn_of_phase_lt (h : Φ.phase W.A < Φ.phase W.B) :
    (∀ T : Subobject W.P, T ≠ ⊥ → T ≠ ⊤ → Φ.phase (T : C) < Φ.phase W.P) ∧
      (∀ T : Subobject W.M, T ≠ ⊥ → T ≠ Subobject.mk W.i →
        Φ.phase (T : C) < Φ.phase W.P) ∧
      Φ.phase W.A < Φ.phase W.P ∧ Φ.phase W.M < Φ.phase W.P := by
  obtain ⟨hAP, -⟩ := Φ.seesaw_lt _ W.shortExact_P W.not_isZero_A W.not_isZero_B h
  obtain ⟨-, hMP⟩ := Φ.seesaw_gt _ W.shortExact_M W.not_isZero_P W.not_isZero_A hAP
  refine ⟨fun T h0 h1 => ?_, fun T h0 h1 => ?_, hAP, hMP⟩
  · rcases W.subobject_P T with rfl | rfl | rfl
    · exact absurd rfl h0
    · rw [phase_mk]; exact hAP
    · exact absurd rfl h1
  · rcases W.subobject_M T with rfl | rfl | rfl | rfl
    · exact absurd rfl h0
    · rw [phase_mk]; exact hAP
    · exact absurd rfl h1
    · rw [phase_top]; exact hMP

/-! ### The side where `A` has the larger phase -/

/-- **The HN filtration `0 ⊂ A ⊂ M` where `φ(B) < φ(A)`.** `U = M/A` is stable; every nonzero
subobject of `M` other than `A` has phase smaller than `φ(A)`, so `A` is the first step of the
HN filtration of `M`; the quotient `U` has phase smaller than `φ(A)`. -/
theorem hn_of_phase_gt (h : Φ.phase W.B < Φ.phase W.A) :
    (∀ T : Subobject W.U, T ≠ ⊥ → T ≠ ⊤ → Φ.phase (T : C) < Φ.phase W.U) ∧
      (∀ T : Subobject W.M, T ≠ ⊥ → T ≠ Subobject.mk (W.j ≫ W.i) →
        Φ.phase (T : C) < Φ.phase W.A) ∧
      Φ.phase W.U < Φ.phase W.A ∧ Φ.phase W.M < Φ.phase W.A := by
  obtain ⟨hBU, hUA⟩ := Φ.seesaw_lt _ W.shortExact_U W.not_isZero_B W.not_isZero_A h
  obtain ⟨-, hPA⟩ := Φ.seesaw_gt _ W.shortExact_P W.not_isZero_A W.not_isZero_B h
  obtain ⟨-, hMA⟩ := Φ.seesaw_lt _ W.shortExact_M W.not_isZero_P W.not_isZero_A hPA
  refine ⟨fun T h0 h1 => ?_, fun T h0 h1 => ?_, hUA, hMA⟩
  · rcases W.subobject_U T with rfl | rfl | rfl
    · exact absurd rfl h0
    · rw [phase_mk]; exact hBU
    · exact absurd rfl h1
  · rcases W.subobject_M T with rfl | rfl | rfl | rfl
    · exact absurd rfl h0
    · exact absurd rfl h1
    · rw [phase_mk]; exact hPA
    · rw [phase_top]; exact hMA

/-! ### On the wall -/

/-- **On the wall `M` is semistable.** Where `φ(A) = φ(B)`, every nonzero subobject of `M` has
the phase of `M`; the chain `0 ⊂ A ⊂ P ⊂ M` is a Jordan–Hölder filtration with factors `A`, `B`,
`A`. -/
theorem semistable_of_phase_eq (h : Φ.phase W.A = Φ.phase W.B) :
    ∀ T : Subobject W.M, T ≠ ⊥ → Φ.phase (T : C) = Φ.phase W.M := by
  have hP : Φ.phase W.P = Φ.phase W.A :=
    Φ.seesaw_eq _ W.shortExact_P W.not_isZero_A W.not_isZero_B h
  have hM : Φ.phase W.M = Φ.phase W.P :=
    Φ.seesaw_eq _ W.shortExact_M W.not_isZero_P W.not_isZero_A hP
  intro T h0
  rcases W.subobject_M T with rfl | rfl | rfl | rfl
  · exact absurd rfl h0
  · rw [phase_mk, hM, hP]
  · rw [phase_mk, hM]
  · rw [phase_top]

end PairingTwoWallHypotheses

end AlgebraicGeometry.K3
