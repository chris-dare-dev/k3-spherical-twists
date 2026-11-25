/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.LinearAlgebra.BilinearForm.Reflection
import K3Twists.LinearAlgebra.Lattice.Mukai.Basic

/-!
# Reflection in a spherical class

For a vector `s` of a Mukai extension with `⟪s, s⟫ = -2`, the map

```
ρ_s(v) = v + ⟪v, s⟫ • s
```

is the reflection in the hyperplane `s^⊥`. The `-2` is what makes the usual
formula `v - 2⟪v,s⟫/⟪s,s⟫ · s` integral: the denominator cancels the `2`, so no
division is needed and the reflection is defined on the lattice rather than on
its rationalisation. This is the only place `IsSpherical` is used below, and it
is used exactly once, in `reflect_reflect`.

**This is not the spherical twist.** On a K3 surface, the twist `T_E` of
Seidel–Thomas acts on the Mukai lattice as `ρ_{v(E)}`, and that statement is the
eventual reason this file exists. But `T_E` is an autoequivalence of
`Dᵇ(Coh X)`, its construction needs an evaluation triangle and a functorial
cone, and none of that is available here or asserted here. `reflect` is a map
of a lattice built from a bilinear form, and every theorem below is a theorem
about **an arbitrary symmetric bilinear module over a commutative ring**, true
whether or not any surface exists — the same discipline `Mukai/Basic.lean`
states in its own docstring.

Every argument below is bilinearity, symmetry, or the single hypothesis
`⟪s,s⟫ = -2`, and none of it is about this carrier. It is therefore proved
once, over an arbitrary form, in `BilinearForm/Reflection.lean`, and this file
specialises it at `mukaiForm b`. In particular `reflectHom b s` is Mathlib's
`Module.preReflection` and `reflectEquiv b s hs` is `Module.reflection`, both by
`rfl`. There is one reflection, not two, and the
record of which hypothesis does what lives with the general statement.

What stays here is the part that is genuinely about the Mukai extension:
`IsSpherical` as the name for `⟪s,s⟫ = -2`, and the preservation of the
distinguished classes `Mukai/Basic.lean` defines.

## Main results

* `reflectHom` — `ρ_s` as an `R`-linear endomorphism, for arbitrary `s`.
* `reflect_reflect` — `ρ_s` is an involution when `s` is spherical.
* `pairing_reflect_reflect` — `ρ_s` preserves the pairing (symmetric `b`).
* `reflectEquiv` — the resulting `R`-linear automorphism.
* `reflectIsometry` — the same map as an isometry of `mukaiForm`.
* `reflect_self` — `ρ_s s = -s`, and `reflect_of_pairing_eq_zero` — `ρ_s`
  fixes `s^⊥` pointwise. Together these say `ρ_s` is a *reflection* rather
  than merely an involutive isometry.
* `IsSpherical.reflect`, `IsIsotropic.reflect`, `expectedDim_reflect` — the
  distinguished classes of `Mukai/Basic.lean` are preserved.
-/

namespace Mukai

variable {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N]
variable (b : N →ₗ[R] N →ₗ[R] R)

/-! ### The map

`Mukai.reflect` is `BilinearForm.reflect` at `mukaiForm b`, named for what
it is in the application: the reflection in a spherical class. -/

/-- Reflection in `s`: `ρ_s(v) = v + ⟪v, s⟫ • s`, specialising
`BilinearForm.reflect` to the Mukai pairing. -/
def reflect (s v : MukaiLattice R N) : MukaiLattice R N :=
  BilinearForm.reflect (mukaiForm b) s v

/-- Not `@[simp]`: unfolding `reflect` everywhere would put `reflect_zero`,
`reflect_self` and `reflect_neg_left` out of simp-normal form. Rewrite with it
explicitly. -/
theorem reflect_apply (s v : MukaiLattice R N) :
    reflect b s v = v + pairing b v s • s :=
  rfl

@[simp]
theorem reflect_zero (s : MukaiLattice R N) : reflect b s 0 = 0 :=
  BilinearForm.reflect_zero _ s

theorem reflect_add (s v w : MukaiLattice R N) :
    reflect b s (v + w) = reflect b s v + reflect b s w :=
  BilinearForm.reflect_add _ s v w

theorem reflect_smul (a : R) (s v : MukaiLattice R N) :
    reflect b s (a • v) = a • reflect b s v :=
  BilinearForm.reflect_smul _ a s v

theorem reflect_neg (s v : MukaiLattice R N) :
    reflect b s (-v) = -reflect b s v :=
  BilinearForm.reflect_neg _ s v

/-- `ρ_s` as an `R`-linear endomorphism of the Mukai lattice: Mathlib's
`Module.preReflection s (-⟪·, s⟫)`.

No hypothesis on `s`: additivity is bilinearity of `pairing`, nothing more. -/
def reflectHom (s : MukaiLattice R N) : MukaiLattice R N →ₗ[R] MukaiLattice R N :=
  BilinearForm.reflectHom (mukaiForm b) s

@[simp]
theorem reflectHom_apply (s v : MukaiLattice R N) :
    reflectHom b s v = reflect b s v :=
  BilinearForm.reflectHom_apply _ s v

/-! ### The pairing against `s`

`IsSpherical b s` is by definition `selfPairing b s = -2`, and
`mukaiForm b s s` reduces to `selfPairing b s`, so a sphericity hypothesis is
accepted directly wherever the general theory asks for `B s s = -2`. -/

/-- Reflecting reverses the pairing against `s` itself. This is where
`⟪s, s⟫ = -2` is spent. -/
theorem pairing_reflect_right (s : MukaiLattice R N) (hs : IsSpherical b s)
    (v : MukaiLattice R N) :
    pairing b (reflect b s v) s = -pairing b v s :=
  BilinearForm.apply_reflect_right (mukaiForm b) s hs v

/-! ### Involutivity -/

/-- **`ρ_s` is an involution** when `s` is spherical. -/
theorem reflect_reflect (s : MukaiLattice R N) (hs : IsSpherical b s)
    (v : MukaiLattice R N) :
    reflect b s (reflect b s v) = v :=
  BilinearForm.reflect_reflect (mukaiForm b) s hs v

theorem reflect_involutive (s : MukaiLattice R N) (hs : IsSpherical b s) :
    Function.Involutive (reflect b s) :=
  reflect_reflect b s hs

theorem reflect_bijective (s : MukaiLattice R N) (hs : IsSpherical b s) :
    Function.Bijective (reflect b s) :=
  (reflect_involutive b s hs).bijective

/-- `ρ_s` as an `R`-linear automorphism, with itself as inverse: Mathlib's
`Module.reflection`. -/
def reflectEquiv (s : MukaiLattice R N) (hs : IsSpherical b s) :
    MukaiLattice R N ≃ₗ[R] MukaiLattice R N :=
  BilinearForm.reflectEquiv (mukaiForm b) s hs

@[simp]
theorem reflectEquiv_apply (s : MukaiLattice R N) (hs : IsSpherical b s)
    (v : MukaiLattice R N) :
    reflectEquiv b s hs v = reflect b s v :=
  BilinearForm.reflectEquiv_apply (mukaiForm b) s hs v

@[simp]
theorem reflectEquiv_symm_apply (s : MukaiLattice R N) (hs : IsSpherical b s)
    (v : MukaiLattice R N) :
    (reflectEquiv b s hs).symm v = reflect b s v :=
  BilinearForm.reflectEquiv_symm_apply (mukaiForm b) s hs v

/-! ### The reflection property

`reflect_self` and `reflect_of_pairing_eq_zero` are what distinguish a
reflection from an arbitrary involutive isometry: the `-1` eigenspace is
spanned by `s` and the `+1` eigenspace contains `s^⊥`. -/

/-- `ρ_s s = -s`. Needs sphericity but not symmetry. -/
@[simp]
theorem reflect_self (s : MukaiLattice R N) (hs : IsSpherical b s) :
    reflect b s s = -s :=
  BilinearForm.reflect_self (mukaiForm b) s hs

/-- `ρ_s` fixes `s^⊥` pointwise. No hypothesis on `s` at all. -/
theorem reflect_of_pairing_eq_zero {s v : MukaiLattice R N}
    (h : pairing b v s = 0) :
    reflect b s v = v :=
  BilinearForm.reflect_of_apply_eq_zero (mukaiForm b) h

/-- The reflected vector lies in `s^⊥` exactly when the original one does. -/
theorem pairing_reflect_eq_zero_iff (s : MukaiLattice R N) (hs : IsSpherical b s)
    (v : MukaiLattice R N) :
    pairing b (reflect b s v) s = 0 ↔ pairing b v s = 0 :=
  BilinearForm.apply_reflect_eq_zero_iff (mukaiForm b) s hs v

/-! ### Isometry

The first statements in this file to need symmetry of `b`. -/

/-- **`ρ_s` preserves the Mukai pairing.** -/
theorem pairing_reflect_reflect (hb : ∀ x y : N, b x y = b y x)
    (s : MukaiLattice R N) (hs : IsSpherical b s) (v w : MukaiLattice R N) :
    pairing b (reflect b s v) (reflect b s w) = pairing b v w :=
  BilinearForm.apply_reflect_reflect (mukaiForm b)
    (fun x y => pairing_comm b hb x y) s hs v w

/-- `ρ_s` preserves `⟪v, v⟫`. -/
theorem selfPairing_reflect (hb : ∀ x y : N, b x y = b y x)
    (s : MukaiLattice R N) (hs : IsSpherical b s) (v : MukaiLattice R N) :
    selfPairing b (reflect b s v) = selfPairing b v := by
  simp only [selfPairing_eq_pairing]
  exact pairing_reflect_reflect b hb s hs v v

/-- `ρ_s` as an isometry of the bundled Mukai form. -/
def reflectIsometry (hb : ∀ x y : N, b x y = b y x)
    (s : MukaiLattice R N) (hs : IsSpherical b s) :
    mukaiForm b →bᵢ mukaiForm b :=
  BilinearForm.reflectIsometry (mukaiForm b)
    (fun x y => pairing_comm b hb x y) s hs

@[simp]
theorem reflectIsometry_apply (hb : ∀ x y : N, b x y = b y x)
    (s : MukaiLattice R N) (hs : IsSpherical b s) (v : MukaiLattice R N) :
    reflectIsometry b hb s hs v = reflect b s v :=
  BilinearForm.reflectIsometry_apply (mukaiForm b) _ s hs v

/-! ### The distinguished classes are preserved

This is the part that is genuinely about the Mukai extension rather than about
an arbitrary form: `Mukai/Basic.lean` names these conditions and downstream
code rewrites with them rather than unfolding to `selfPairing`. -/

theorem IsSpherical.reflect (hb : ∀ x y : N, b x y = b y x)
    {s : MukaiLattice R N} (hs : IsSpherical b s) {v : MukaiLattice R N}
    (hv : IsSpherical b v) :
    IsSpherical b (Mukai.reflect b s v) := by
  rw [isSpherical_iff, selfPairing_reflect b hb s hs]
  exact hv

theorem IsIsotropic.reflect (hb : ∀ x y : N, b x y = b y x)
    {s : MukaiLattice R N} (hs : IsSpherical b s) {v : MukaiLattice R N}
    (hv : IsIsotropic b v) :
    IsIsotropic b (Mukai.reflect b s v) := by
  rw [isIsotropic_iff, selfPairing_reflect b hb s hs]
  exact hv

theorem expectedDim_reflect (hb : ∀ x y : N, b x y = b y x)
    (s : MukaiLattice R N) (hs : IsSpherical b s) (v : MukaiLattice R N) :
    expectedDim b (reflect b s v) = expectedDim b v := by
  rw [expectedDim, expectedDim, selfPairing_reflect b hb s hs]

/-! ### Reflection in `-s`

`IsSpherical.neg` says `-s` is spherical whenever `s` is, so both reflections
exist; they are the same map, because the sign enters the formula twice. -/

@[simp]
theorem reflect_neg_left (s v : MukaiLattice R N) :
    reflect b (-s) v = reflect b s v :=
  BilinearForm.reflect_neg_left (mukaiForm b) s v

end Mukai
