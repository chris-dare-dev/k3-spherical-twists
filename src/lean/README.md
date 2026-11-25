# Lean proofs

The statements of the study that Lean 4 and Mathlib can check today: the identities of the Mukai lattice and of central charges, the integer arithmetic of walls with two spherical simples, and the point-mass corollary

  lim m_σ(Φ^{±n} 𝒪_x)^{1/n} = exp h_cat(Φ) = exp h_cat(Φ⁻¹),

derived from a stated list of geometric inputs. Lean 4.36.0, Mathlib `v4.36.0`, no `sorry`, no axiom beyond Lean's three standard ones.

The statements follow the research draft *Harder–Narasimhan towers of spherical twist words on a Picard-rank-one K3 surface*; references to it are by name, because its numbering is still changing.

## Build

Needs [elan](https://github.com/leanprover/elan); it installs the pinned toolchain on first use.

```bash
make lean-deps   # once: Mathlib's build cache, several GB
```

```bash
make lean        # build (any warning fails it), tests, linters, umbrella, axioms, style
```

## What is proved from Mathlib alone

| Statement | Lean |
|---|---|
| A twist acts on Mukai vectors by the reflection in its root: an isometric involution with `T_Y Y = Y[-1]` on classes | `MukaiVector.reflect_reflect`, `MukaiVector.pairing_reflect`, `MukaiVector.reflect_self` |
| The puncture of a root `(r, c, s)` is at height `1/(dr²)` above the parabola: `s/(dr) = (c/r)² + 1/(dr²)` | `MukaiVector.puncture_height` |
| `Z_{b+ia}` vanishes on the kernel line `(1, b, d(b² + a²))` | `charge_kernel` |
| The half-turn: `Z_{f(z)}(T_δ v) = -k Z_z(v)/(z - m)²` for `f(z) = m - k/(z - m)`, `m = c/r`, `k = 1/(dr²)`; `f` is an involution preserving the upper half-plane | `charge_halfTurn`, `halfTurn_halfTurn`, `im_halfTurn_pos` |
| The opening example at `d = 1`, `z = (1 + 4i)/3`: `m(T𝒪_x) = 19/9`, `m(T⁻¹𝒪_x) = 17/9`, one class for both, `m(Tⁿ𝒪_x) = 1 + 10n/9`, and the segment to the cusp of `T⁻¹𝒪_x` meets no puncture | `opening_mass_T`, `opening_mass_Tinv`, `opening_same_class`, `opening_mass_Tpow`, `opening_segment_clear` |
| For `g ≥ 2` the nonnegative solutions of `a² + b² - gab = 1` are exactly `R_m = (u_{m+1}, u_m)` and `L_m = (u_m, u_{m+1})` | `realRoot_classification` |
| `[R_m, R_j] = u_{j-m}`, and every ray-difference minor `[R_m, R_{j+1} - R_j]` is at least one | `det_R`, `det_R_sub_ge_one` |
| The same bound for any fan `v_{j+1} = g_j v_j - v_{j-1}`, `g_j ≥ 2`, with adjacent minors one, on both sides | `fan_minor_ge_one`, `fan_minor_ge_one_left` |
| For `\|g\| ≥ 3` two spherical classes of pairing `±g` span no isotropic class | `no_null_vector`, `span_roots_anisotropic` |
| The wall group carrying the point: `v(N)² = 2q(g - q)`, and `e(N) ≤ 2` leaves `N = U` or a universal extension | `square_roots_plus_isotropic`, `twoExtensions_numerics` |
| The rigid wall example at `g = 3`: `dim End = 9`, the boundary roots `(8, 3) = R₂` and `(1, 3) = L₁` | `rigid_example` |
| The preprojective model of a wall with two spherical simples: representations `A_i : V₀ → V₁`, `B_i : V₁ → V₀` with `∑ B_i A_i = 0 = ∑ A_i B_i`, nilpotence, morphisms, the complete lattice of subrepresentations, on which the dimension vector is a valuation | `DoubledRep.IsPreprojective`, `DoubledRep.IsNilpotent`, `DoubledRep.Hom`, `DoubledRep.subreps`, `DoubledRep.dimVec_sup_add_inf` |
| The example *Arrows in both directions at a rigid wall*, for every `g`: `V₀ = H' ⊕ k·u`, `V₁ = W`, the relations, every path of length three vanishes, `dim End = g²`, and a subrepresentation is everything or lies in `H'` and contains the `g·dim U₁`-dimensional image of `W ⊗ U₁` | `rigidRep_isPreprojective`, `rigidRep_isNilpotent`, `finrank_rigidRep_End`, `RigidRep.eq_endOf`, `RigidRep.eq_top_or`, `RigidRep.dimVec_mem` |
| At `g = 3`: dimension `(9, 3)`, `dim End = 9`; plotting `(i, j)` at `(i + j, j)`, the upper boundary `(0, 0) → (11, 3) → (12, 3)` through `(H', W)` and the lower boundary `(0, 0) → (8, 0) → (12, 3)` through `(H', 0)`; `(H', W)` and `M/(H', 0)` are stable, of the real-root dimensions `(8, 3) = R₂` and `(1, 3) = L₁` | `rigidWall_finrank_End`, `rigidWall_dimVec_mem`, `rigidWall_upper`, `rigidWall_lower`, `rigidWall_upperCorner_stable`, `rigidWall_quotient_stable`, `rigidWall_stable_roots` |
| Harder–Narasimhan filtrations in a lattice with a slope function (valuations `rk`, `deg`, `rk` strictly monotone): the prefix `c_k` with factor slopes `≥ θ` below and `≤ θ` above maximizes `deg - θ rk`, uniquely if the inequalities are strict; hence the HN filtration is unique, it reads the upper boundary of the convex hull of the points `(rk, deg)` and the opposite one reads the lower boundary (Baumann–Kamnitzer–Tingley, arXiv:1110.3661, §3.2), and it only depends on the order of slopes | `HNFiltration.weight_le`, `HNFiltration.eq_of_weight_eq`, `HNFiltration.mem_range_chain_iff`, `HNFiltration.instSubsingleton`, `HNFiltration.convexHull_subset`, `HNFiltration.weight_ge_edge_of_neg`, `HNFiltration.ofSlopeOrder` |
| At a wall with two simples, a charge `i Z₀ + j Z₁` orders the subquotients by `j/(i + j)` on one side and by `i/(i + j)` on the other | `DoubledRep.slopeFunction`, `DoubledRep.slope_le_slope_iff`, `DoubledRep.slope_le_slope_iff_neg` |
| The HN filtrations of the rigid wall example, for every `g` and every charge on either side, are `0 ⊂ (H', W) ⊂ M` and `0 ⊂ (H', 0) ⊂ M`; at `g = 3` their polygons are `(0, 0) → (11, 3) → (12, 3)` and `(0, 0) → (8, 0) → (12, 3)` | `RigidRep.hnUpper`, `RigidRep.hnLower`, `RigidRep.hnUpperOf`, `RigidRep.hnLowerOf`, `rigidWall_hnUpper`, `rigidWall_hnLower` |
| Fekete with a constant: the rate exists, each block certifies `ρ ≤ (K H_k)^{1/k}`, and the bounds converge | `exists_rate_of_submul`, `pow_rate_le` |
| Transfer of rates between comparable sequences, uniformly in parameters; `o(n)` errors; polynomial growth has rate one; the rate per letter of a periodic word | `tendsto_rpow_inv_of_bounds`, `tendstoUniformly_rpow_inv_of_bounds`, `tendsto_log_div_of_bound`, `tendsto_log_div_zero_of_poly`, `tendsto_log_div_of_period` |
| The algebra of Lemma A.1: the slope estimate `V(E) ≤ aR + d^{-1/2}√(Rm)` and the absorption of the square root | `piece_bound`, `slope_bound_of_le`, `fixedTest_of_generic` |
| The Koszul bound `7^s` and the constant `K = 5(2 + 36ν)(2 + 25ν)⁸7⁴⁶` | `koszul_bound`, `diag_constant` |
| A standard word has `H_n = 18 + 12ν + 9du²n²` | `standard_H_formula` |
| `Θ = T_S T_B` with `v(B) = v(S)` acts trivially on classes while `h(B, Θⁿ S) ≥ M(M - 1)^{2n}` | `theta_acts_trivially`, `theta_lower_bound` |
| `Ψ = T_𝒪 T_L` on the plane of `v(𝒪), v(L)`: trace `(d + 2)² - 2`, determinant one, an eigenvalue `ρ > 1`, irrational eigenlines | `psi_action`, `psi_eigenvalue`, `psi_discriminant_not_square` |
| In an abelian category, a nonsplit extension of two simple objects has exactly three subobjects, and an object `M` with `A ⊂ P ⊂ M` glued from two such extensions (`P` and `M/A` nonsplit) has exactly the chain `0 ⊂ A ⊂ P ⊂ M` | `ShortComplex.ShortExact.subobject_eq_of_nonsplit`, `subobject_eq_of_nonsplit_of_nonsplit` |
| `dim(J + XJ) ≥ dim J + 1` for a nonzero finite-dimensional `J ⊆ K[X]`, the dehomogenized `dim(sJ + tJ) ≥ dim J + 1` behind the stability of the section-evaluation objects `Q_d` | `Polynomial.finrank_lt_finrank_sup_map_mulLeft_X` |
| Two HN filtrations of one object with nonzero factors have the same length, phases and factors (Bridgeland, arXiv:math/0212237, §3) | `HNFiltration.exists_iso_of_nonzero` |
| Two distinguished triangles on one object, each first vertex orthogonal to both third vertices, are isomorphic | `Pretriangulated.exists_iso_of_hom_eq_zero` |
| An exact autoequivalence `Φ` carries HN filtrations for `s` to HN filtrations for `Φ s` with the same phases, and by uniqueness to all of them; `Φ(Φ⁻¹ s) = s` | `TriEquiv.mapHN`, `TriEquiv.exists_iso_of_hnFiltration`, `TriEquiv.act_symm_act` |
| The homotopy pullback `B_i = B ×_M M_i` of the tower algorithm, from the octahedral axiom: `A → B_i → M_i`, `B_{i-1} → B_i → M_i/M_{i-1}` and the induced connecting map | `Pretriangulated.exists_pullback_triangles` |
| HN filtrations concatenate along a triangle when their phases are separated; an HN filtration whose factors carry HN filtrations with separated phases refines to one with their factors, counted additively | `HNFiltration.exists_concat`, `HNFiltration.exists_refinement` |
| Exactly one factor carrying the point survives a wall crossing from its local inputs, a finite path of walls, and a letter | `WallCrossing.carriesOnce`, `Leg.carriesOnce`, `TriEquiv.carriesOnce_map` |
| Evaluation of one phase, in any slicing: `Hom(S, M) ≅ Hom(S, D)` for the top quotient `M → D → C` and `S` of phases at least `φ` (and dually at the bottom); a residual of phases at most `φ` with no maps from `P(φ)` has phases below `φ`; the fibre of `D → D_final` is `M → D`; one evaluation step keeps the lower tail `C` | `Slicing.comp_bijective_of_top`, `Slicing.comp_bijective_of_bottom`, `Slicing.ltProp_of_leProp_of_hom_eq_zero`, `Slicing.exists_iso_top`, `Slicing.exists_evaluation_step` |

## What is proved from stated inputs

`PointMassHypotheses` lists what the corollary uses about `D^b(X)`. Mathlib does not yet have derived categories of coherent sheaves on a K3 surface, Bridgeland stability or categorical entropy, so these are hypotheses (fields), each with its source in its docstring:

- Serre duality `h(U, V) = h(V, U)`, invariance of total Hom under autoequivalences, additivity on `G = S₀ ⊕ S₁ ⊕ S₂`;
- the diagonal estimate `h(U, V) ≤ K h(U, G) h(G, V)` (Orlov, arXiv:0804.1163, Theorem 4, with regularity for `K`);
- the point test `h(E, 𝒪_x) = R(E)` and `ν R(E) ≤ h(E, G)` for spherical `E`, and `m_τ ≍ h(G, ·)` (the article's point-measurement lemma);
- Lemma A.1 (for spherical `E`) and Lemma A.2 of the article;
- standard words: their powers are standard, they move points to shifted points, their `H_n` grows quadratically;
- Bridgeland's metric bound on masses (arXiv:math/0212237, Proposition 8.1), the action on stability conditions, positive masses;
- the entropy formula for smooth proper categories (Dimitrov–Haiden–Katzarkov–Kontsevich, arXiv:1307.8418, Theorem 2.6).

From these, Lean proves every assertion of the corollary:

| Assertion | Lean |
|---|---|
| `c e^{-d(σ,τ)} p(W) ≤ m_σ(W𝒪_x) ≤ C e^{d(σ,τ)} p(W)` for every word | `PointMassHypotheses.uniform_estimate` |
| Arbitrary prefixes: point mass and `p(W_n)` have the same rates when `d(σ_n, τ) = o(n)` | `PointMassHypotheses.tendsto_log_mass_div_sub` |
| Comparison for a fixed period: `H(W) ≤ J p(W)` for every `W` commuting with a nonstandard `Φ` | `PointMassHypotheses.exists_H_le_mul_p` |
| `H(Φ^{m+n}) ≤ K H(Φ^m) H(Φ^n)`, `H(W⁻¹) = H(W)`, `h_cat(Φ⁻¹) = h_cat(Φ)` | `PointMassHypotheses.H_pow_add_le`, `H_inv`, `hcat_inv` |
| Certified upper bounds `(K H(Φ^k))^{1/k}` converging to `exp h_cat(Φ)` | `PointMassHypotheses.rate_certified` |
| The limit, uniformly in `x` and in `σ` with `d(σ, τ) ≤ D₀`; for `Φ⁻ⁿ`; along `σ_n` with `d(σ_n, τ) = o(n)` and any `x_n` | `PointMassHypotheses.tendstoUniformly_pointMass`, `tendsto_pointMass`, `tendsto_pointMass_inv`, `tendsto_log_pointMass_of_sublinear` |
| The rate per letter `exp(h_cat(Φ)/ℓ)` along the prefixes of a periodic word | `PointMassHypotheses.tendsto_log_pointMass_prefix` |

`PairingTwoWallHypotheses` packages the extensions at a wall where two spherical objects `A`, `B` of one phase have `dim Ext¹(B, A) = 2`: `A`, `B` simple in the wall category, a nonsplit `0 → A → P → B → 0`, an extension `0 → P → M → A → 0` by a generator of the line `Ext¹(A, P)`, and its nonsplit pushout `0 → B → U → A → 0`, `U = M/A`. That these exist is the `Ext` computation at the wall (Serre duality, `Ext¹(A, A) = 0`); at the wall contracting a `(-2)`-curve `C` they are `P = 𝒪_x`, `M = 𝒪_X/(I_C I_x)` and `U = T_{𝒪_C} 𝒪_x`. `SeesawPhaseHypotheses` is a phase function with the see-saw property, which the charge restricted to the wall category has (Bridgeland, arXiv:math/0212237; Rudakov, J. Algebra 197 (1997); Bayer–Bridgeland, arXiv:1310.8266, Lemma 2.7). From these, in any abelian category:

| Assertion | Lean |
|---|---|
| The subobjects of `M` form the single chain `0 ⊂ A ⊂ P ⊂ M` | `PairingTwoWallHypotheses.subobject_M` |
| Where `φ(A) < φ(B)`: `P` is stable and is the first HN step of `M`, with quotient `A` of smaller phase | `PairingTwoWallHypotheses.hn_of_phase_lt` |
| Where `φ(B) < φ(A)`: `A` is the first HN step of `M`, with stable quotient `U` of smaller phase | `PairingTwoWallHypotheses.hn_of_phase_gt` |
| On the wall `M` is semistable, with Jordan–Hölder factors `A`, `B`, `A` | `PairingTwoWallHypotheses.semistable_of_phase_eq` |

A theorem proved from hypotheses that cannot hold together says nothing. [K3TwistsTest/PointMassModel.lean](K3TwistsTest/PointMassModel.lean) builds a five-object model in which every field holds. [K3TwistsTest/PairingTwoWallModel.lean](K3TwistsTest/PairingTwoWallModel.lean) does the same for `PairingTwoWallHypotheses`, in abelian groups with `A = B = ℤ/2`, `P = U = ℤ/4` and `M = ℤ/8`; since `A = B` there, it exercises the statement on the wall, and a constant phase satisfies `SeesawPhaseHypotheses`. [scripts/AxiomAudit.lean](scripts/AxiomAudit.lean) checks every constant of every `K3Twists` module for `sorry` and for axioms other than `propext`, `Classical.choice` and `Quot.sound`.

### The tower theorem

`TowerHypotheses` lists what the tower theorem of the draft uses: `C` stands for `D^b(X)`, a
slicing for a stability condition, and each field cites its source:

- `𝒪_x` is nonzero and stable at the geometric anchor `η` (Bayer–Bridgeland,
  arXiv:1310.8266, Theorem 2.2 and Lemma 6.7; the draft's "Visibility on the cover");
- each letter is an exact autoequivalence that matches the constituents of `P_s(φ)` with those of
  `P_{Vs}(φ)`, isotropic to isotropic and spherical to spherical (Bridgeland,
  arXiv:math/0212237, §8; Seidel–Thomas, arXiv:math/0001043), and preserves `e(E) = 2`;
- for each letter a finite path of walls from `η` to `V⁻¹η`, and one from `η` to the target; at
  each wall the grouping of the incoming factors and an outgoing flag of each wall group in its
  own phase window (the draft's two-extension lemma and rigid-wall proposition; Bayer–Bridgeland,
  arXiv:1310.8266, Lemmas 2.5–2.7 and Remark 2.8), packaged as `WallCrossing`.

From these, Lean proves the induction on the length of the word:

| Assertion | Lean |
|---|---|
| At `η`, every prefix `W_j 𝒪_x` has exactly one HN factor carrying the point, and every other factor is spherical | `TowerHypotheses.carriesOnce_anchor` |
| The same at the target `σ`, also when `σ` lies on walls | `TowerHypotheses.tower` |
| The same for every HN filtration of `W 𝒪_x` at `σ` with nonzero factors | `TowerHypotheses.tower_forall` |

[K3TwistsTest/HNTowerModel.lean](K3TwistsTest/HNTowerModel.lean) builds an instance from any slicing
with a nonzero semistable object (the empty word, no walls); it shows the fields are consistent
relative to such a slicing, which Mathlib cannot yet construct.

## Layout

The library mirrors Mathlib: a file sits at the Mathlib path of the API it extends, or of its
nearest Mathlib precedent, and its declarations use Mathlib's namespaces. Moving a file into
Mathlib or into derived-alg-geo-lean keeps its path below the library root.

| Module under `K3Twists/` | Job | Namespace |
|---|---|---|
| `Analysis/SpecificLimits/GrowthRate.lean` | exponential growth rates of sequences | `Real` |
| `LinearAlgebra/Lattice/Mukai/PicardRankOne.lean` | the Mukai lattice of a Picard-rank-one K3: pairing, roots, reflections, punctures | `MukaiVector` |
| `Combinatorics/Quiver/Kronecker/RealRoots.lean` | the real roots of the `g`-Kronecker quiver and their determinants | `Quiver.Kronecker` |
| `AlgebraicGeometry/Surface/K3/PicardRankOne/CentralCharge.lean` | central charges, the half-turn of a twist, the opening example | `AlgebraicGeometry.K3.PicardRankOne` |
| `AlgebraicGeometry/Surface/K3/PicardRankOne/WallArithmetic.lean` | the integers of a wall with two spherical simples | same |
| `AlgebraicGeometry/Surface/K3/PairingTwoWall.lean` | the length-three object at a wall of pairing two and its two HN filtrations | `AlgebraicGeometry.K3` |
| `CategoryTheory/Abelian/Uniserial.lean` | the subobjects of nonsplit extensions of simple objects | `CategoryTheory` |
| `RingTheory/Polynomial/Basic.lean` | multiplication by `X` enlarges every nonzero finite-dimensional subspace of `K[X]` | `Polynomial` |
| `AlgebraicGeometry/Surface/K3/PicardRankOne/PointMassEstimates.lean` | the inequalities inside Lemma A.1 and the constant `K` | same |
| `AlgebraicGeometry/Surface/K3/PicardRankOne/PointMass.lean` | the point-mass corollary from its inputs | same |
| `AlgebraicGeometry/Surface/K3/PicardRankOne/TwistWords.lean` | standard words and the words `Θ`, `Ψ` of the mass section | same |
| `AlgebraicGeometry/Surface/K3/PicardRankOne/HNTower.lean` | the tower theorem from its inputs | same |
| `AlgebraicGeometry/Surface/K3/PicardRankOne/RigidWall.lean` | the example of a rigid wall at `g = 3` | same |
| `Order/HarderNarasimhan.lean` | Harder–Narasimhan filtrations and the HN polygon in a lattice with a slope function | `Order.SlopeFunction` |
| `RepresentationTheory/Quiver/Kronecker/HarderNarasimhan.lean` | slope functions on subrepresentations, the two sides of a wall, the HN filtrations of the rigid representation | `Quiver.Kronecker` |
| `RepresentationTheory/Quiver/Kronecker/Preprojective.lean` | representations of the doubled Kronecker quiver: preprojective relations, nilpotence, morphisms, subrepresentations, dimension vectors | `Quiver.Kronecker` |
| `RepresentationTheory/Quiver/Kronecker/RigidRep.lean` | the rigid representation of dimension `(g², g)` with arrows in both directions | `Quiver.Kronecker` |

Quiver representations are not in Mathlib. They sit under `RepresentationTheory/Quiver/`, beside
Mathlib's representations and subrepresentations, and keep the namespace `Quiver.Kronecker` of
the Kronecker real roots. Harder–Narasimhan filtrations in a lattice sit under `Order/`, beside
Mathlib's composition series in a lattice (`Mathlib/Order/JordanHolder.lean`).

### Stability foundations

Copied from derived-alg-geo-lean at the same paths, ported to Mathlib `v4.36.0`, in namespace
`CategoryTheory.Triangulated` unless noted. They are the triangulated layer the tower algorithm
is built on.

| Module under `K3Twists/CategoryTheory/` | Job |
|---|---|
| `Triangulated/PostnikovTower.lean` | finite filtrations by distinguished triangles |
| `Triangulated/StabilityCondition/Weak/Foundation/Slicing.lean` | `HNFiltration` and `Slicing` (Bridgeland's slicings) |
| `Triangulated/StabilityCondition/Weak/Foundation/IntervalCategory.lean` | interval categories `P((a, b))` and admissible subobjects |
| `Triangulated/StabilityCondition/Weak/Foundation/Slicing/{PhaseBounds,FiltrationOperations,BoundaryFactors,IntrinsicPhases}.lean` | phase cuts, Hom vanishing across a phase gap, operations on HN filtrations, the intrinsic phases `φ⁺`, `φ⁻` |
| `Triangulated/StabilityCondition/Symmetry/Autoequivalence/Slicing/Transport.lean` | an exact autoequivalence `Φ` moves HN filtrations and slicings, `(Φ s).P φ = Φ (s.P φ)` |
| `Triangulated/StabilityCondition/Symmetry/Autoequivalence/Slicing/Quotient.lean` | `TriEquiv`, an exact autoequivalence with its instances; its action on slicings, composition, the group `AutQuot` |
| `GrothendieckGroup/Presentation.lean`, `Triangulated/GrothendieckGroup/Basic.lean` | `K₀` of a triangulated category and class maps |
| `Triangulated/StabilityCondition/Weak/Basic/Definitions.lean` | the weak prestability condition (Definition 14.1 of arXiv:1902.08184 only) |
| `Triangulated/StabilityCondition/Foundation/{PreStabilityCondition,StabilityCondition}.lean` | prestability and locally finite stability conditions with a class map |
| `Linear/SerreFunctor/Basic.lean` (with `Algebra/Category/ModuleCat/LinearDual/Basic.lean`) | Serre functors of a `k`-linear category (`CategoryTheory.SerreFunctor`) |
| `Triangulated/SerreFunctor/Objects.lean` | spherical and pseudoprojective objects relative to a Serre functor |

Added here, for the tower algorithm, in the same namespaces:

| Module under `K3Twists/CategoryTheory/` | Job |
|---|---|
| `Triangulated/StabilityCondition/Weak/Foundation/Slicing/Uniqueness.lean` | uniqueness of HN filtrations |
| `Triangulated/StabilityCondition/Weak/Foundation/Slicing/Insertion.lean` | the homotopy pullback, concatenation and refinement of HN filtrations |
| `Triangulated/StabilityCondition/Symmetry/Autoequivalence/Slicing/HarderNarasimhan.lean` | HN filtrations along an exact autoequivalence |
| `Triangulated/StabilityCondition/WallCrossing.lean` | carrying the point once across a wall, a path of walls and a letter |
| `Triangulated/StabilityCondition/Weak/Foundation/Slicing/Evaluation.lean` | the evaluation lemma, as far as it holds in any slicing |

Five of these files began as adaptations of mattrobball/BridgelandStability under Apache-2.0;
their headers say so and [NOTICE](NOTICE), beside this README, carries the attribution and the
license.

Beside the library: `K3Twists.lean`, the umbrella, generated by Mathlib's `mk_all`;
`K3TwistsTest/`, a test library in the style of `MathlibTest` that `lake test` builds; and
`scripts/`, the axiom audit and a style checker copied from derived-alg-geo-lean.

## Conventions

These follow Mathlib and derived-alg-geo-lean, so that files can move to either.

- **Placement.** An extension of a Mathlib API goes at Mathlib's path and in its namespace. A
  new subject follows the nearest Mathlib precedent (`CategoryTheory/Triangulated/<Name>/`,
  `RepresentationTheory/...`); K3-specific material goes under
  `AlgebraicGeometry/Surface/K3/`, in namespace `AlgebraicGeometry.K3`.
- **Files.** Every file starts with the header below and a module docstring that states what it
  proves, its assumptions and its conventions. Lines are at most 100 characters, files at most
  1,500 lines. Plain Lean files, not the module system (`allowNonModules = true`), as in
  derived-alg-geo-lean.

  ```lean
  /-
  Copyright (c) 2026 Chris Dare. All rights reserved.
  Released under the MIT license.
  -/
  ```
- **Names.** Mathlib naming. Sources are cited in docstrings ("Lemma 2.6 of arXiv:1310.8266"),
  never in names; no issue numbers, dates, part numbers or agent names in identifiers or
  comments. Statements of the draft are cited by name, not number.
- **Proofs.** No `sorry`, `admit`, `native_decide` or added axiom. What Mathlib cannot prove yet
  is an explicit hypothesis; a structure that packages such inputs ends in `Hypotheses` (as
  `PointMassHypotheses`), and each field's docstring gives its source.
- **Copied files.** Files copied from derived-alg-geo-lean keep its path below the library root,
  with `DerivedAlgGeo` replaced by `K3Twists`. Files that carry an Apache-2.0 header or an
  attribution to another project keep both, and the attribution is listed in `NOTICE` beside
  this README.
- **Before a pull request.** `make lean` passes. After adding a file, run
  `lake exe mk_all --lib K3Twists` (from `src/lean`) to regenerate the umbrella.

## What this does not cover

Visibility on the cover and the wall lemmas beyond their integer arithmetic and the rigid example are not formalized, nor is the socle step of the evaluation lemma (it needs the abelian length category `P(φ)`); neither is the higher-Picard-rank work. They need derived categories of K3 surfaces and stability conditions in Mathlib first. The tower algorithm is formalized from its inputs (`TowerHypotheses`), which are those statements.
