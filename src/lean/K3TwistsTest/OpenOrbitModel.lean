/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.RepresentationTheory.Quiver.Kronecker.IncomingFlag

/-!
# The open-orbit hypothesis can hold

A theorem proved from hypotheses that cannot hold says nothing. `OpenOrbitHypotheses` has one
field, the open-orbit step of the proposition on rigid wall groups. For a quiver without arrows
(`ι` empty) every one-cochain vanishes, so `Ext¹(B, A) = 0` is a single orbit and the field holds
with identity automorphisms; this file proves it.

This is a weak check: with `g ≥ 1` arrows the field is the open-orbit theorem itself, which needs
algebraic groups acting on varieties in Mathlib.
-/

universe u

namespace Quiver.Kronecker

/-- Without arrows the open-orbit hypothesis holds: every one-cochain vanishes. -/
theorem OpenOrbitHypotheses.of_isEmpty (k : Type*) [Field k] [IsAlgClosed k] [CharZero k]
    (ι : Type*) [Fintype ι] [IsEmpty ι] : OpenOrbitHypotheses.{u} k ι where
  exists_aut_of_le_orbitTangent A B _ _ _ _ _ _ _ _ :=
    ⟨DoubledRep.Iso.refl A, DoubledRep.Iso.refl B, by
      rw [Subsingleton.elim (_ - _) 0]
      exact zero_mem _⟩

end Quiver.Kronecker
