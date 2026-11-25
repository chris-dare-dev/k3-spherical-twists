/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.Order.HarderNarasimhan
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.CategoryTheory.Subobject.NoetherianObject

/-!
# Additive functions are valuations on subobjects

Let `C` be an abelian category and `Z : C → G` a function to an additive commutative group that
is additive on short exact sequences: `Z X₂ = Z X₁ + Z X₃` for every short exact
`0 → X₁ → X₂ → X₃ → 0`, as a central charge factoring through the Grothendieck group is.

* `Subobject.infSupShortComplex_shortExact`: for subobjects `A`, `B` of `X`, the sequence
  `0 → A ⊓ B → A ⊞ B → A ⊔ B → 0`, with maps `(ι, -ι)` and `[ι, ι]`, is short exact.
* `Subobject.additive_sup_add_inf`: **the subobject valuation lemma**,
  `Z (A ⊔ B) + Z (A ⊓ B) = Z A + Z B`.
* `Subobject.isModularLattice_of_additive`: if `Z` vanishes only on zero objects, the lattice of
  subobjects of every object is modular (`Order.isModularLattice_of_valuation`).
* `Subobject.chargeFunction`: additive `rk, deg : C → K` with `(rk E, deg E)` lexicographically
  positive for every nonzero `E` form a charge function on `Subobject X`. With `Z = -deg + i rk`
  this says that `Z E` lies in the upper half-plane or on the negative real axis for `E ≠ 0`:
  `Z` is a stability function on `C` (Bridgeland, arXiv:math/0212237, Definition 2.1), and the
  subobjects of phase one, `Z` on the negative real axis, give vertical steps.
* `Subobject.nonempty_hnFiltration`: on a Noetherian object, a stability function whose maximal
  phase is attained on every interval `[A, X]` gives a Harder–Narasimhan filtration of the
  subobjects of `X`, which is unique (`Order.ChargeFunction.HNChain.instSubsingleton`).
  Whether the objects of a given heart are Noetherian is a separate question, not addressed here.
-/

namespace CategoryTheory

open Limits

variable {C : Type*} [Category C] [Abelian C]

namespace Subobject

variable {X : C}

/-- The short complex `A ⊓ B → A ⊞ B → A ⊔ B` of subobjects of `X`, with maps `(ι, -ι)` and
`[ι, ι]`. -/
noncomputable abbrev infSupShortComplex (A B : Subobject X) : ShortComplex C :=
  ShortComplex.mk
    (biprod.lift (ofLE (A ⊓ B) A _root_.inf_le_left) (-ofLE (A ⊓ B) B _root_.inf_le_right))
    (biprod.desc (ofLE A (A ⊔ B) _root_.le_sup_left) (ofLE B (A ⊔ B) _root_.le_sup_right)) (by
      rw [biprod.lift_desc, Preadditive.neg_comp, ofLE_comp_ofLE, ofLE_comp_ofLE,
        add_neg_cancel])

lemma infSupShortComplex_g_arrow (A B : Subobject X) :
    (infSupShortComplex A B).g ≫ (A ⊔ B).arrow = biprod.desc A.arrow B.arrow := by
  apply biprod.hom_ext' <;> simp [infSupShortComplex]

/-- **`0 → A ⊓ B → A ⊞ B → A ⊔ B → 0` is short exact.** -/
theorem infSupShortComplex_shortExact (A B : Subobject X) :
    (infSupShortComplex A B).ShortExact := by
  have hmono : Mono (infSupShortComplex A B).f :=
    mono_of_mono_fac (show (infSupShortComplex A B).f ≫ biprod.fst =
      ofLE (A ⊓ B) A _root_.inf_le_left by simp [infSupShortComplex])
  have hepi : Epi (infSupShortComplex A B).g := by
    have himg : imageSubobject (biprod.desc A.arrow B.arrow) = A ⊔ B := by
      rw [sup_eq_imageSubobject, ← imageSubobject_iso_comp (biprod.isoCoprod _ _).hom]
      congr 1
      ext <;> simp [biprod_isoCoprod_hom]
    have : (infSupShortComplex A B).g =
        factorThruImageSubobject (biprod.desc A.arrow B.arrow) ≫ ofLE _ _ himg.le := by
      rw [← cancel_mono (A ⊔ B).arrow, infSupShortComplex_g_arrow, Category.assoc, ofLE_arrow,
        imageSubobject_arrow_comp]
    rw [this]
    have : IsIso (ofLE _ _ himg.le) := (isoOfEq _ _ himg).isIso_hom
    infer_instance
  refine ShortComplex.ShortExact.mk' ?_ hmono hepi
  refine ShortComplex.exact_of_f_is_kernel _
    (KernelFork.IsLimit.ofι' _ (infSupShortComplex A B).zero fun {T} k hk ↦ ?_)
  have hk' : (k ≫ biprod.fst) ≫ A.arrow = (-(k ≫ biprod.snd)) ≫ B.arrow := by
    have h2 : k ≫ biprod.desc A.arrow B.arrow = 0 := by
      rw [← infSupShortComplex_g_arrow, ← Category.assoc, hk, zero_comp]
    rw [biprod.desc_eq, Preadditive.comp_add, ← Category.assoc, ← Category.assoc] at h2
    rw [Preadditive.neg_comp]
    exact eq_neg_of_add_eq_zero_left h2
  refine ⟨(inf_isPullback A B).lift _ _ hk', ?_⟩
  ext
  · simp [infSupShortComplex]
  · simp [infSupShortComplex]

variable {G : Type*} [AddCommGroup G] {Z : C → G}

/-- An additive function is additive on biproducts. -/
lemma additive_biprod (hZ : ∀ S : ShortComplex C, S.ShortExact → Z S.X₂ = Z S.X₁ + Z S.X₃)
    (Y₁ Y₂ : C) : Z (Y₁ ⊞ Y₂) = Z Y₁ + Z Y₂ :=
  hZ _ (ShortComplex.Splitting.ofHasBinaryBiproduct Y₁ Y₂).shortExact

/-- **The subobject valuation lemma.** An additive function is a valuation on the subobjects of
every object: `Z (A ⊔ B) + Z (A ⊓ B) = Z A + Z B`. -/
theorem additive_sup_add_inf
    (hZ : ∀ S : ShortComplex C, S.ShortExact → Z S.X₂ = Z S.X₁ + Z S.X₃) (A B : Subobject X) :
    Z ((A ⊔ B : Subobject X) : C) + Z ((A ⊓ B : Subobject X) : C) = Z A + Z B := by
  have h1 : Z ((A : C) ⊞ (B : C)) = Z ((A ⊓ B : Subobject X) : C) + Z ((A ⊔ B : Subobject X) : C) :=
    hZ _ (infSupShortComplex_shortExact A B)
  rw [← additive_biprod hZ (A : C) (B : C), h1, add_comm]

/-- For `A ≤ B`, an additive function adds over `0 → A → B → B/A → 0`. -/
lemma additive_cokernel_ofLE
    (hZ : ∀ S : ShortComplex C, S.ShortExact → Z S.X₂ = Z S.X₁ + Z S.X₃) {A B : Subobject X}
    (h : A ≤ B) : Z B = Z A + Z (cokernel (ofLE A B h)) :=
  hZ (ShortComplex.mk (ofLE A B h) (cokernel.π _) (cokernel.condition _))
    (ShortComplex.ShortExact.mk'
      (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (ofLE A B h))) inferInstance
      inferInstance)

/-- A subobject `A ≤ B` with `B/A = 0` is `B`. -/
lemma eq_of_le_of_isZero_cokernel {A B : Subobject X} (h : A ≤ B)
    (hz : IsZero (cokernel (ofLE A B h))) : A = B := by
  have : Epi (ofLE A B h) := Preadditive.epi_of_isZero_cokernel _ hz
  have : IsIso (ofLE A B h) := isIso_of_mono_of_epi _
  exact le_antisymm h (le_of_comm (inv (ofLE A B h)) (by
    rw [IsIso.inv_comp_eq, ofLE_arrow]))

/-- **Modularity of subobject lattices.** If an additive function vanishes only on zero
objects, the lattice of subobjects of every object is modular. -/
theorem isModularLattice_of_additive
    (hZ : ∀ S : ShortComplex C, S.ShortExact → Z S.X₂ = Z S.X₁ + Z S.X₃)
    (hZ0 : ∀ Y : C, Z Y = 0 → IsZero Y) (X : C) : IsModularLattice (Subobject X) :=
  Order.isModularLattice_of_valuation (fun A : Subobject X ↦ Z A) (additive_sup_add_inf hZ)
    fun {A B} h e ↦ eq_of_le_of_isZero_cokernel h (hZ0 _ (by
      have := additive_cokernel_ofLE hZ h
      rw [← e] at this
      exact add_eq_left.mp this.symm))

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **The charge function of a stability function on the subobjects of `X`.** Additive functions
`rk, deg : C → K` with `(rk E, deg E)` lexicographically positive for every nonzero `E` give a
charge function on `Subobject X`: for `A < B` the quotient `B/A` is nonzero. -/
noncomputable def chargeFunction {rk deg : C → K}
    (hrk : ∀ S : ShortComplex C, S.ShortExact → rk S.X₂ = rk S.X₁ + rk S.X₃)
    (hdeg : ∀ S : ShortComplex C, S.ShortExact → deg S.X₂ = deg S.X₁ + deg S.X₃)
    (hpos : ∀ E : C, ¬IsZero E → 0 < rk E ∨ (rk E = 0 ∧ 0 < deg E)) (X : C) :
    Order.ChargeFunction (Subobject X) K where
  rk A := rk A
  deg A := deg A
  lex_lt {A B} h := by
    have h1 := additive_cokernel_ofLE hrk h.le
    have h2 := additive_cokernel_ofLE hdeg h.le
    have hQ : ¬IsZero (cokernel (ofLE A B h.le)) := fun hz ↦
      h.ne (eq_of_le_of_isZero_cokernel h.le hz)
    rcases hpos _ hQ with hp | ⟨hp, hp'⟩
    · left; linarith
    · right; constructor <;> linarith
  rk_sup_add_inf := additive_sup_add_inf hrk
  deg_sup_add_inf := additive_sup_add_inf hdeg

/-- **Harder–Narasimhan filtrations of subobjects.** For a stability function, a Noetherian
object whose maximal phase is attained on every interval `[A, X]` has an HN filtration of its
subobjects; it is unique. -/
theorem nonempty_hnFiltration {rk deg : C → K}
    (hrk : ∀ S : ShortComplex C, S.ShortExact → rk S.X₂ = rk S.X₁ + rk S.X₃)
    (hdeg : ∀ S : ShortComplex C, S.ShortExact → deg S.X₂ = deg S.X₁ + deg S.X₃)
    (hpos : ∀ E : C, ¬IsZero E → 0 < rk E ∨ (rk E = 0 ∧ 0 < deg E)) (X : C)
    [IsNoetherianObject X] (hatt : (chargeFunction hrk hdeg hpos X).MaxPhaseAttained) :
    Nonempty (chargeFunction hrk hdeg hpos X).HNFiltration :=
  (chargeFunction hrk hdeg hpos X).nonempty_hnFiltration hatt

end Subobject

end CategoryTheory
