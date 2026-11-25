/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import K3Twists.AlgebraicGeometry.Surface.K3.PicardRankOne.EulerMass
import K3TwistsTest.PointMassModel

/-!
# The mass comparison inputs are consistent

A theorem proved from inconsistent hypotheses says nothing. `MassComparisonHypotheses` has two
models: the five-object model of `K3TwistsTest/PointMassModel.lean`, through
`PointMassHypotheses`, where the exponents are zero; and the lattice instance `eulerMass` of the
library, on the Mukai lattice of a K3 surface of Picard rank one, where Theorem C gives the point
class a positive exponent. This file checks that the comparison theorems and Theorem C elaborate
on both.

Built by `lake test`.
-/

namespace MassComparisonModel

open AlgebraicGeometry.K3.PicardRankOne Filter Topology Real

/-- The point-mass model is a model of the comparison inputs. -/
noncomputable example :
    MassComparisonHypotheses PointMassModel.Obj Unit Unit (Fin 3) :=
  PointMassModel.model.toMassComparisonHypotheses

/-- In the lattice model, the lower comparison `h(G, V) ≤ L_g m_g(V)` holds at every point. -/
example (d : ℤ) (hd : 1 ≤ d) (g : mukaiIsometries d) (V : ClassSum) :
    (eulerMass d hd).hom (eulerMass d hd).G V ≤
      (eulerMass d hd).lowerConst g * (eulerMass d hd).mass g V :=
  (eulerMass d hd).hom_G_le_mul_mass g V

/-- In the lattice model, the mass form of the exponent theorem holds for the twist system of
`𝒪_X` and `𝒪_X(H)`. -/
example (d : ℤ) (hd : 1 ≤ d) (g : mukaiIsometries d) :
    Tendsto (fun N : ℕ => log ((eulerMass d hd).massMax (eulerClassTwistSystem d) g N) / N)
      atTop (𝓝 (eulerClassTwistSystem d).homExponent) :=
  (eulerClassTwistSystem_isTwistSystem d hd).tendsto_log_massMax
    (eulerClassTwistSystem_lowerBound d) (eulerClassTwistSystem_isSpherical d)
    (eulerClassTwistSystem_directedConnected d (by omega)) g

/-- Theorem C on the lattice model: the point class grows at a rate at least `log(d + 1)`. -/
example (d : ℤ) (hd : 1 ≤ d) (g : mukaiIsometries d) :
    ∃ η : ℝ, log ((d : ℝ) + 1) ≤ η ∧
      Tendsto (fun n : ℕ => log (Monoid.lenMax (eulerClassTwistSystem d).T
        ((eulerMass d hd).mass g) n (ClassSum.single MukaiVector.point)) / n) atTop (𝓝 η) :=
  eulerClass_exists_tendsto_log_lenMax d hd g

end MassComparisonModel
