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
| The projective model `(b, t) = (Re z, \|z\|²)` is a bijection of `ℍ` onto `t > b²` with `cosh d(z, w) = (t_z + t_w - 2b_z b_w)/(2 Im z Im w)`; semicircles on the real axis are its lines, and `d(z, w) + d(w, u) = d(z, u)` exactly when the image of `w` is on the straight segment | `UpperHalfPlane.range_projectiveModel`, `cosh_dist_eq`, `projectiveModel_snd_eq_iff`, `dist_add_dist_eq_iff` |
| The Mukai form has signature `(2, 1)`; in the chart `(c/r, s/(dr))` its negative cone is `t > b²` and its isotropic lines are the parabola and `(0, 0, 1)`; the cone of two positive-rank vectors is the segment between their points | `MukaiVector.pairing_self_pos_of_pairing_structureSheaf_eq_zero`, `pairing_self_neg_iff`, `isIsotropic_iff`, `toModel_mem_segment_iff` |
| Reverse Cauchy–Schwarz; two vectors of the closed negative cone with positive rank pair negatively (Lemma 3.2 of arXiv:1310.8266); distinct roots of positive rank pair to at most `-3` | `mul_pairing_self_le_sq`, `sq_pairing_eq_iff`, `pairing_neg_of_rank_pos`, `pairing_le_neg_three` |
| `Z_p` vanishes exactly on the kernel line `ℝκ`, and `Z_p(v) = λ Z_p(w)` with `λ` real iff `v = λw + tκ`; charges are collinear on the wall line `(c - rb)(dRt - S) - (C - Rb)(drt - s) = 0` | `modelCharge_eq_zero_iff`, `modelCharge_eq_ofReal_mul_iff`, `im_modelCharge_mul_conj` |
| Visibility on the cover, the lattice part: a clear upward ray is Bayer–Bridgeland's condition `Z(δ) ∉ ℝ_{≤0}`; on a clear segment, roots `λ_i δ + t_i κ` with `λ_i > 0`, `Σ λ_i = 1`, `Σ t_i = 0` are the single root `δ`; an obstacle has a positively proportional charge and pairing `≤ -3` with `δ`; an obstructed segment has a first obstacle | `rayClear_iff`, `eq_singleton_of_segmentClear`, `obstacle_charge_pos_mul`, `exists_first_obstacle` |
| The finite search: an obstacle has `r'² ≤ max(r², 1/(dh))` on a segment to a root, `d r' h ≤ e\|b - m\|` on a segment to the cusp `m = c₀/e`, `d r'² h ≤ 1` on the upward ray, so there are finitely many; a verified search decides visibility at rational points | `obstacle_rank_sq_le`, `cusp_obstacle_rank_le`, `ray_obstacle_rank_sq_le`, `finite_obstacles`, `segmentClear_iff_check`, `not_segmentClear_example` |
| Clear sight: `dh > 1` clears the upward ray and the segment to a puncture of rank one; `e\|b - m\| < dh` clears the segment to the cusp `m` (which generalizes the opening check); the rigid wall example | `rayClear_of_one_lt`, `segmentClear_of_one_lt`, `cuspClear_of_lt`, `opening_cuspClear`, `rigid_segmentClear` |
| The sight line to the cusp of an isotropic class `w` (no root with `⟨δ', w⟩ < 0` and `Z_p(δ') ∈ ℝ_{≥0} Z_p(w)`) is the upward ray for rank zero and the segment to `(c/r, (c/r)²)` otherwise; an isometry matching the charges at two points carries one sight line to the other | `cuspRayClear_point_iff`, `cuspRayClear_iff_rayClear`, `cuspRayClear_iff_cuspClear`, `cuspRayClear_iff_of_isometry` |
| For `g ≥ 2` the nonnegative solutions of `a² + b² - gab = 1` are exactly `R_m = (u_{m+1}, u_m)` and `L_m = (u_m, u_{m+1})` | `realRoot_classification` |
| `[R_m, R_j] = u_{j-m}`, and every ray-difference minor `[R_m, R_{j+1} - R_j]` is at least one | `det_R`, `det_R_sub_ge_one` |
| The same bound for any fan `v_{j+1} = g_j v_j - v_{j-1}`, `g_j ≥ 2`, with adjacent minors one, on both sides | `fan_minor_ge_one`, `fan_minor_ge_one_left` |
| For `\|g\| ≥ 3` two spherical classes of pairing `±g` span no isotropic class | `no_null_vector`, `span_roots_anisotropic` |
| The ground-state (Picone) identity `2xᵀAx = 2Σ(Ap)ᵢpᵢyᵢ² - ΣAᵢⱼpᵢpⱼ(yᵢ - yⱼ)²` for `x = py` and symmetric `A` over any commutative ring; for a symmetric Z-matrix, with no hypothesis on the diagonal: positive definite iff some `p > 0` has `Ap > 0` (the M-matrix criterion, Berman–Plemmons, *Nonnegative Matrices in the Mathematical Sciences*, Ch. 6, Thm 2.3), `Ax ≥ 0 ⇒ x ≥ 0`, `A⁻¹ ≥ 0` and `A⁻¹𝟙 > 0`; a positive null vector `δ` gives positive semidefiniteness and, for indecomposable `A`, isotropic vectors `ℚδ`; a nonzero null vector `δ ≥ 0` of any symmetric matrix forbids `Ap > 0`; Mathlib's spectral bound for Z-matrices puts the eigenvalues of a positive definite wall matrix of spheres below `4` | `Matrix.IsSymm.picone`, `Matrix.IsZMatrix.posDef_iff_exists_certificate`, `nonneg_of_mulVec_nonneg`, `inv_nonneg_of_posDef`, `posSemidef_of_null`, `isotropic_eq_smul`, `Matrix.IsSymm.no_certificate_of_null`, `Matrix.IsZMatrix.eigenvalue_lt_two_mul` |
| Over `ℤ`: positive definite iff an integer `p > 0` has `Ap ≥ 1`; the isotropic integer vectors of an indecomposable symmetric Z-matrix with a positive primitive null vector `δ` are `ℤδ` | `Matrix.IsZMatrix.posDef_iff_int_certificate`, `isotropic_int_eq_zsmul` |
| A finite-type Cartan matrix from an integer certificate, and positive weights `Mp > 0` for every finite-type Cartan matrix; `E₆`, `E₇`, `E₈` by `p = 2ρ^∨` with `Ap = 2·𝟙`; `E 9 = Ẽ₈` has the null vector `(2, 3, 4, 6, 5, 4, 3, 2, 1)`, no certificate, affine type and isotropic vectors `ℤδ` | `Matrix.isFiniteCartan_of_certificate`, `Matrix.IsFiniteCartan.exists_certificate`, `CartanMatrix.isFiniteCartan_E_six`, `isFiniteCartan_E_seven`, `isFiniteCartan_E_eight`, `E_nine_no_certificate`, `E_nine_posSemidef_and_not_posDef`, `E_nine_isotropic_eq_zsmul` |
| The wall matrix `Aᵢⱼ = χ(Sᵢ, Sⱼ) = -⟨v(Sᵢ), v(Sⱼ)⟩` and the Tits identity `v(Σ aᵢSᵢ)² = -aᵀAa`; no nonzero `ℕ`-sum of spherical vertices is isotropic (`NoIsotropicSphereSum`); for three spheres pairwise pairings `≥ 3` do not give it (pairings `4, 5, 6`, isotropic sum `(4, 35, 3)`); the density statement that would relate it to `ℚ`-anisotropy is stated as a `Prop`, not proved | `LinearMap.BilinForm.wallMatrix`, `LinearMap.BilinForm.apply_sum_smul_self`, `Matrix.NoIsotropicSphereSum`, `Matrix.pairwise_three_not_sufficient`, `Matrix.ExistsPosIsotropicOfIsotropic` |
| Two spheres, `[[2, -g], [-g, 2]]`: positive definite iff `\|g\| < 2`, isotropic iff `g² - 4` is a square; for `g ∈ ℕ` finite iff `g ≤ 1`, affine iff `g = 2` (isotropic vectors `ℤ(1, 1)`), indefinite iff `g ≥ 3` and then anisotropic over `ℚ`; an isotropic sum only at `g = 2`, so for two spheres no isotropic `ℕ`-sum means `ℚ`-anisotropy; the two reflections multiply to trace `g² - 2` | `Quiver.Kronecker.cartanMatrix_posDef_iff`, `cartanMatrix_isotropic_iff`, `rank_two_trichotomy`, `cartanMatrix_two_isotropic_eq_zsmul`, `cartanMatrix_anisotropic`, `noIsotropicSphereSum_cartanMatrix_iff_anisotropic`, `trace_reflection_mul_reflection` |
| In Picard rank one, two roots of pairing `g ∈ ℕ` span a wall of finite, affine or indefinite type as `g ≤ 1`, `g = 2`, `g ≥ 3`; `v(𝒪_X)` and `v(𝒪_X(-H)[1])` pair to `d + 2`: an indefinite wall with no isotropic sum | `wallMatrix_trichotomy`, `span_roots_anisotropic_of_wallMatrix`, `noIsotropicSphereSum_wallMatrix`, `structureSheaf_shift_wall` |
| The wall group carrying the point: `v(N)² = 2q(g - q)`, and `e(N) ≤ 2` leaves `N = U` or a universal extension | `square_roots_plus_isotropic`, `twoExtensions_numerics` |
| The rigid wall example at `g = 3`: `dim End = 9`, the boundary roots `(8, 3) = R₂` and `(1, 3) = L₁` | `rigid_example` |
| The preprojective model of a wall with two spherical simples: representations `A_i : V₀ → V₁`, `B_i : V₁ → V₀` with `∑ B_i A_i = 0 = ∑ A_i B_i`, nilpotence, morphisms, the complete lattice of subrepresentations, on which the dimension vector is a valuation | `DoubledRep.IsPreprojective`, `DoubledRep.IsNilpotent`, `DoubledRep.Hom`, `DoubledRep.subreps`, `DoubledRep.dimVec_sup_add_inf` |
| The example *Arrows in both directions at a rigid wall*, for every `g`: `V₀ = H' ⊕ k·u`, `V₁ = W`, the relations, every path of length three vanishes, `dim End = g²`, and a subrepresentation is everything or lies in `H'` and contains the `g·dim U₁`-dimensional image of `W ⊗ U₁` | `rigidRep_isPreprojective`, `rigidRep_isNilpotent`, `finrank_rigidRep_End`, `RigidRep.eq_endOf`, `RigidRep.eq_top_or`, `RigidRep.dimVec_mem` |
| At `g = 3`: dimension `(9, 3)`, `dim End = 9`; plotting `(i, j)` at `(i + j, j)`, the upper boundary `(0, 0) → (11, 3) → (12, 3)` through `(H', W)` and the lower boundary `(0, 0) → (8, 0) → (12, 3)` through `(H', 0)`; `(H', W)` and `M/(H', 0)` are stable, of the real-root dimensions `(8, 3) = R₂` and `(1, 3) = L₁` | `rigidWall_finrank_End`, `rigidWall_dimVec_mem`, `rigidWall_upper`, `rigidWall_lower`, `rigidWall_upperCorner_stable`, `rigidWall_quotient_stable`, `rigidWall_stable_roots` |
| Harder–Narasimhan filtrations in a lattice with a slope function (valuations `rk`, `deg`, `rk` strictly monotone): the prefix `c_k` with factor slopes `≥ θ` below and `≤ θ` above maximizes `deg - θ rk`, uniquely if the inequalities are strict; hence the HN filtration is unique, it reads the upper boundary of the convex hull of the points `(rk, deg)` and the opposite one reads the lower boundary (Baumann–Kamnitzer–Tingley, arXiv:1110.3661, §3.2), and it only depends on the order of slopes | `HNFiltration.weight_le`, `HNFiltration.eq_of_weight_eq`, `HNFiltration.mem_range_chain_iff`, `HNFiltration.instSubsingleton`, `HNFiltration.convexHull_subset`, `HNFiltration.weight_ge_edge_of_neg`, `HNFiltration.ofSlopeOrder` |
| At a wall with two simples, a charge `i Z₀ + j Z₁` orders the subquotients by `j/(i + j)` on one side and by `i/(i + j)` on the other | `DoubledRep.slopeFunction`, `DoubledRep.slope_le_slope_iff`, `DoubledRep.slope_le_slope_iff_neg` |
| The HN filtrations of the rigid wall example, for every `g` and every charge on either side, are `0 ⊂ (H', W) ⊂ M` and `0 ⊂ (H', 0) ⊂ M`; at `g = 3` their polygons are `(0, 0) → (11, 3) → (12, 3)` and `(0, 0) → (8, 0) → (12, 3)` | `RigidRep.hnUpper`, `RigidRep.hnLower`, `RigidRep.hnUpperOf`, `RigidRep.hnLowerOf`, `rigidWall_hnUpper`, `rigidWall_hnLower` |
| The lemma on the wall group that carries the point, in the quiver model (`U` once at vertex one, `S` `p` times at vertex zero, `e(M) = 2` read as `dim End M + p(g - p) = 1`): `p ≥ g`, and `M = S^k ⊕ T_S U` (every `B_i = 0`, the `A_i` independent) or `M = S^k ⊕ T_S⁻¹ U` (every `A_i = 0`, the `B_i` independent), `k = p - g` | `IsNilpotent.A_comp_B_eq_zero`, `finrank_End_ge`, `twoExtensions_rank`, `twoExtensions` |
| Its table of HN quotients on both sides of the wall: where `U` is higher, `U, S^p` or `T_S⁻¹ U, S^k`; where `S` is higher, `S^k, T_S U` or `S^p, U`; for any wall object with `U` once, the HN filtrations are `0 ⊂ (⟨B_i⟩, U) ⊂ M` and `0 ⊂ (⋂ ker A_i, 0) ⊂ M` | `hnUHigher`, `hnSHigher`, `isStable_bot_subSpan`, `isStable_subKer_top`, `twoExtensions_table` |
| From the proposition on rigid wall groups: the outgoing HN flag determines subobjects of the retained wall object independently of the representative. An isomorphism `M ≅ N` carries the HN filtration of `M` to that of `N` on either side, and every automorphism fixes the HN prefixes (in a lattice: any map preserving rank and degree fixes them) | `DoubledRep.Iso.mapSubrep`, `Iso.map_hnFiltration`, `Iso.map_hnFiltration_neg`, `Iso.mapSubrep_chain`, `HNFiltration.apply_chain_eq`, `HNFiltration.map` |
| `Ext¹` of representations with the preprojective relations, by the standard complex `⊕ Hom(X_v, Y_v) → ⊕ Hom(X_{t(a)}, Y_{h(a)}) → ⊕ Hom(X_v, Y_v)`: `H⁰ = Hom`; an extension `0 → A → N → B → 0` is a cocycle placed in the off-diagonal block, every subrepresentation presents its representation as such an extension, and classes related by isomorphisms of the ends (cohomologous classes in particular) give isomorphic extensions | `DoubledRep.Ext1`, `ker_d₀₁`, `isPreprojective_extension_iff`, `offDiag_mem_cocycles₁`, `exists_iso_extension`, `extensionIso` |
| From the proposition on rigid wall groups: for an extension `ξ` with middle term `N` and `Hom(A, B) = 0`, `v ↦ i v p` induces an injection `Ext¹(B, A)/(End(A)ξ + ξ End(B)) ↪ Ext¹(N, N)`; so `Ext¹(N, N) = 0` gives `Ext¹(B, A) = End(A)ξ + ξ End(B)` | `extQuotPushPull_injective`, `orbitSpan_eq_top`, `cocycles₁_le_orbitTangent` |
| From the same proposition: a prefix `M_j` of an HN filtration has no maps to the next factor `M_{j+1}/M_j` (a nonzero map would give subobjects `K < M_j ≤ I` with `w(K) + w(I) = 2w(M_j)`, while `M_j` is the only maximizer of a weight `w`), and along such a flag the prefixes of a rigid representation are rigid | `Hom_restrict_subquotient_eq_bot`, `exists_subreps_of_mem_Hom`, `subsingleton_Ext1_restrict_of_chain` |
| `dim Ext¹(X, Y) = dim Hom(X, Y) + dim Hom(Y, X) - (x, y)`, `(x, y) = 2x₀y₀ + 2x₁y₁ - g(x₀y₁ + x₁y₀)` (Crawley-Boevey, Amer. J. Math. 122 (2000), Lemma 1), from the duality of the two differentials under the trace pairing; Mukai's inequality with its defect, `e(N) = e(A) + e(B) + 2 dim Ext¹(B, A)/(End(A)ξ + ξ End(B))` when `Hom(A, B) = 0` (Bayer–Bridgeland, arXiv:1310.8266, Lemma 2.5), so both ends of a rigid extension are rigid; the rigid example has `Ext¹ = 0` | `finrank_Ext1`, `dualMap_d₀₁_comp_tracePairing₁`, `finrank_Ext1_extension`, `finrank_Ext1_add_le`, `rigid_of_rigid_extension`, `subsingleton_Ext1_rigidRep` |
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
| For a class map additive on short exact sequences, `[P] = [U] = [A] + [B]` and `[M] = 2[A] + [B]`; if `[A]`, `[B]` are spherical of pairing two, the wall matrix is `[[2, -2], [-2, 2]]`, `P` and `U` are isotropic and `M` is spherical | `PairingTwoWallHypotheses.cl_P`, `cl_M`, `cl_U`, `selfPairing_cl` |

A theorem proved from hypotheses that cannot hold together says nothing. [K3TwistsTest/PointMassModel.lean](K3TwistsTest/PointMassModel.lean) builds a five-object model in which every field holds. [K3TwistsTest/PairingTwoWallModel.lean](K3TwistsTest/PairingTwoWallModel.lean) does the same for `PairingTwoWallHypotheses`, in abelian groups with `A = B = ℤ/2`, `P = U = ℤ/4` and `M = ℤ/8`; since `A = B` there, it exercises the statement on the wall, and a constant phase satisfies `SeesawPhaseHypotheses`. [scripts/AxiomAudit.lean](scripts/AxiomAudit.lean) checks every constant of every `K3Twists` module for `sorry` and for axioms other than `propext`, `Classical.choice` and `Quot.sound`.

### Visibility on the cover

`VisibilityHypotheses` lists what the lemma "Visibility on the cover" uses about `D^b(X)` and `Stab†(X)`, with sources ([BB] is Bayer–Bridgeland, arXiv:1310.8266):

- the shift (`v(E[1]) = -v(E)`, `φ(E[n]) = φ(E) + n`), Riemann–Roch for spheres (`v(E)² = -2`), `Z_σ(E) ∈ ℝ_{>0} e^{iπφ(E)}` for semistable `E`, and Jordan–Hölder factors of semistable objects;
- `Z_σ` is the geometric charge at a point of the punctured half-plane followed by a real-linear automorphism of `ℂ`, and vanishes on no root (Bridgeland, arXiv:math/0307164, Theorem 1.1; [BB], equations (2) and (3));
- the rigid-factor lemma ([BB], Lemma 2.6), `⟨v(E), v(F)⟩ ≥ 0` for non-isomorphic stable objects of one phase (the proof of [BB], Lemma 3.1), openness of stability ([BB], Proposition 2.10) and closedness of semistability (arXiv:math/0212237, §8);
- the cover: a clear segment lifts to a marked puncture, and the points that see a marked puncture form a connected set (arXiv:math/0307164, Theorem 1.1; [BB], Theorem 1.3);
- the marked spheres, deck translates of the spherical bundles, stable near their punctures and determined up to shift by them ([BB], Lemma 5.3, Proposition 2.3, Theorem 1.4); every sphere is stable somewhere ([BB], Corollary 6.9);
- the geometric chamber: one skyscraper sheaf is stable exactly there ([BB], Lemma 6.7), and it is the part of the geometric sheet over the slit region `V(X)` ([BB], Theorem 2.2);
- autoequivalences act on the Mukai lattice by isometries `G_*`, with `v(GE) = G_* v(E)`, and on `Stab†(X)` by `Z_{Gσ} = Z_σ ∘ G_*⁻¹` ([BB], §1 and §2).

From these, Lean proves the lemma:

| Assertion | Lean |
|---|---|
| A semistable sphere seen along a clear segment is stable; the sphere of a marked puncture is stable wherever that puncture is seen | `VisibilityHypotheses.stable_of_semistable_of_segmentClear`, `stable_sphere_of_sees` |
| Where a sphere is stable, the segment to its puncture is clear; a stable sphere is determined by its class and phase | `VisibilityHypotheses.segmentClear_of_stable`, `eq_of_stable_of_cl_eq` |
| Every sphere is a shifted marked sphere, and it is stable exactly where its marked puncture is seen: where the segment to its puncture is clear and lifts to its marking | `VisibilityHypotheses.exists_eq_vadd_sphere`, `stable_vadd_sphere_iff`, `stable_iff_sees_marking`, `stable_iff_segmentClear_and_sees` |
| A point image `G𝒪_x` is stable exactly when `G⁻¹σ` is geometric: on the geometric sheet, with a clear upward ray | `VisibilityHypotheses.stable_smul_point_iff`, `stable_smul_point_iff_rayClear` |
| `G_*` carries that upward ray to the ray from the point of `σ` to the cusp of `G𝒪_x`; so `G𝒪_x` is stable exactly where the ray to its cusp is unobstructed and has the prescribed marking: the segment to `(c/r, (c/r)²)` if `v(G𝒪_x) = (r, c, s)` has `r ≠ 0`, the upward ray if `r = 0` | `VisibilityHypotheses.rayClear_inv_smul_iff`, `stable_smul_point_iff_cuspRayClear`, `stable_smul_point_iff_cuspClear`, `stable_smul_point_iff_rayClear_of_r_eq_zero` |

[K3TwistsTest/VisibilityModel.lean](K3TwistsTest/VisibilityModel.lean) meets the field list of `VisibilityHypotheses`, vacuously on the stability side: a model with stability conditions needs Bridgeland stability in Mathlib.

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

### Rigid wall objects from their incoming flag

`OpenOrbitHypotheses` is the one step of the uniqueness in the draft's proposition on rigid wall
groups that Mathlib cannot prove: over an algebraically closed field of characteristic zero, two
classes of `Ext¹(B, A)` whose `Aut(A) × Aut(B)`-orbits have full tangent space
`End(A)ξ + ξ End(B) = Ext¹(B, A)` lie in one orbit. Its source is the closed-orbit lemma (Borel,
*Linear Algebraic Groups*, Proposition I.1.8; Humphreys, *Linear Algebraic Groups*, §8.3): a full
tangent space makes the orbit full-dimensional, hence open and dense in the irreducible space
`Ext¹(B, A)`, and two such orbits meet. From it, in the quiver model:

| Assertion | Lean |
|---|---|
| Two extensions `0 → A → N → B → 0` and `0 → A' → N' → B' → 0` with `A ≅ A'`, `B ≅ B'`, `Hom(A, B) = 0` and rigid middle terms are isomorphic | `DoubledRep.nonempty_iso_extension` |
| A rigid wall object is determined by its incoming flag: two rigid representations with the relations whose HN filtrations for one charge have isomorphic factors, in order, are isomorphic; the same holds along any flags whose prefixes have no maps to the next factor | `DoubledRep.nonempty_iso_of_hnFiltration`, `nonempty_iso_of_chain` |

[K3TwistsTest/OpenOrbitModel.lean](K3TwistsTest/OpenOrbitModel.lean) proves the field for a quiver
without arrows, where `Ext¹ = 0`; with arrows it is the open-orbit theorem itself, which needs
algebraic groups acting on varieties in Mathlib.

## Walls in the quiver model

The wall statements are proved for representations of the doubled Kronecker quiver with the
preprojective relations, from Mathlib alone, except that the uniqueness of a rigid wall object
given its incoming flag also uses `OpenOrbitHypotheses`. Two inputs connect them to the K3 surface
and are not formalized:

- the iterated extensions of the stable wall constituents are the nilpotent representations of
  this quiver with these relations, so that wall subobjects are subrepresentations with their
  multiplicities as dimension vectors (formality of the `Ext`-algebra of the constituents,
  Davison, arXiv:2106.07692, Proposition 7.8);
- near the wall, the HN filtration of a wall object is the slope filtration for the perturbed
  charge in the Serre subcategory of its constituents (Bayer–Bridgeland, arXiv:1310.8266,
  Lemma 2.7 and Remark 2.8).

For the wall group that carries the point, `e(M) = 2` enters through Riemann–Roch,
`e(M) = 2 dim End M + v(M)²` with `v(M)² = 2p(g - p)` (`square_roots_plus_isotropic`). For the
rigid wall groups, between two spherical simples, `e(M) = dim Ext¹(M, M)` is computed in the model
itself, by the standard complex of the preprojective algebra: `finrank_Ext1` gives
`e(M) = 2 dim End M - 2(p² + q² - gpq)`, the same identity with `v(M)² = -2(p² + q² - gpq)`.

## Higher Picard rank: an elliptic K3 surface with a section

On an elliptic K3 surface with a section `C`, fibre class `F` and `NS = ℤC ⊕ ℤF`, the curve `C` is contracted on a wall whose spherical simples `A = 𝒪_C` and `B = 𝒪_C(-1)[1]` pair to two. The curve with an embedded point `𝒪_X/(I_C I_x)` and its family `M_{d,x}` appear there as HN quotients of twisted points, at the stability condition of Tramel and Xia (arXiv:1702.06252) with `H = C + 2F`, `β = -C/4`, `z = 2 - i`. The lattice, charge and phase numbers of these towers are proved from Mathlib alone; the geometry (the stability condition, the stability of `A`, `B` and the tails, the exact sequences and towers themselves) is cited, not formalized.

| Statement | Lean |
|---|---|
| The Mukai extension `ℤ ⊕ N ⊕ ℤ` of a symmetric bilinear lattice, its roots and reflections (copied from derived-alg-geo-lean) | `Mukai.pairing`, `Mukai.reflect_reflect`, `Mukai.pairing_reflect_reflect` |
| `C² = -2`, `C·F = 1`, `F² = 0`; `H = C + 2F` has `H² = 2` and contracts `C` and only `C` | `intersection_curve_fibre`, `intersection_polarization`, `intersection_polarization_pos` |
| The wall: `⟨v(A), v(B)⟩ = 2`, `v(A) + v(B) = v(𝒪_x)`, `v(aA + bB)² = -2(a - b)² = -2 q₂(a, b)` with `q₂` the Kronecker form | `pairing_wallA_wallB`, `wallA_add_wallB`, `selfPairing_wallClass_eq_kroneckerForm` |
| The wall matrix of `A`, `B` is `[[2, -2], [-2, 2]]`: the curve wall is of affine type, its null vector is `v(𝒪_x)`, its isotropic classes are the multiples of `v(𝒪_x)`, and the Tits identity gives `v(aA + bB)² = -(a, b)ᵀA(a, b)`; `𝒪_x`, `T_A 𝒪_x` and `𝒪_X/(I_C I_x)` have multiplicities `(1, 1)`, `(1, 1)`, `(2, 1)` | `wallMatrix_curveWall`, `curveWall_posSemidef_and_not_posDef`, `isIsotropic_wallClass_iff`, `selfPairing_wallClass_eq_neg_dotProduct`, `curveWall_pairingTwoWall_classes` |
| Riemann–Roch on the wall: an `(m, 1)` object `D₀ ⊕ A^r` has `dim Ext¹ = 2(1 + pq) - 2(p + q - 1)² + 2r(2 - p - q)`, which is `2` only at `p = q = 1`; the class `(2, 2)` is isotropic | `ext_one_count`, `ext_one_count_eq_two_iff`, `selfPairing_wallClass_two_two` |
| `v(𝒪_C(j)) = (j + 1)v(A) + j v(B)`; `M_{d,x}` has multiplicities `(d + 2, d + 1)` and square `-2`; `D(jC)/(I_x ⊗ D(-C))` grows by layers `𝒪_C(d - 2j)`; the thickening `K_ε ⊗ 𝒪_X/(I_x I_C^{r+1})` has class `(0, (r + 1)C, (r + 1)(r + 1 + ε) + 1)` and square `-2(r + 1)²`, so `dim Ext¹ = 2` | `curveSheaf_eq_wallClass`, `embeddedPoint_eq_wallClass`, `idealQuotient_succ`, `thickening_eq`, `selfPairing_thickening` |
| The quotients of each tower add up to the class of the twisted point: the two towers of the thickening, `T_{K_ε(-(r+1)C)} 𝒪_x`, the two-letter word `T_{D(nF)}⁻¹ T_{D(-C)} 𝒪_x` in every degree, the rank-two example | `point_add_sum_curveSheaf`, `sum_A_side_odd`, `sum_A_side_even`, `reflect_lineBundle_point`, `reflect_reflect_point`, `reflect_rankTwo_point` |
| The charge at the wall: `Z(aA + bB) = -(a + b)/2` (phase one), `Z(M_{d,x}) = -(2d + 3)/2`, `Z(𝒪_X[1]) = -2 + i`, `Z(𝒪_X(-C - F)[1]) = -7/4 + 2i`, `Z(𝒪_X(-C + 2F)) = 4 + i`, `Z(𝒪_X(-C + 3F)) = 19/4 + 2i`, `Z(𝒪_X(-2C + 2F)) = 17/2 + i`, `Z(I_x(-2C + 2F)) = 19/2 + i`, and the order of their phases | `charge_wallClass`, `charge_embeddedPoint`, `charge_structureSheaf_shift`, `charge_tailOdd_shift`, `charge_twoLetter`, `charge_rankTwo`, `arg_charge_wallClass`, `arg_charge_structureSheaf_shift` |
| The parity argument: a root of odd rank and imaginary charge `2` is not the sum of two roots of imaginary charge `1`; so `𝒪_X(-C - F)[1]` and every line bundle of `H`-slope `3` are stable | `not_isSpherical_sub_of_odd_rank`, `not_split_tail_odd`, `not_split_slope_three` |
| The words `T_{𝒪_X(-2C)}`, then `T_{𝒪_X(-C + 2F)}⁻¹`, then `T_{𝒪_X(-C + 3F)}⁻¹` applied to `𝒪_x`: the two-letter tower has charges `-4 - i`, `-7/2`, `19/2 + 4i` adding up to `2 + 3i`; the wall masses are `4 + √5`, `(7/2)(1 + √17)` and `3/2 + √41/4`; the third word has the class `(0, C + F, 3)` of `𝒪_{C+Γ}(C + 4F)` and of `𝒪_C(1) ⊕ 𝒪_Γ(x)` | `charge_twoLetter_tower`, `mass_oneLetter`, `mass_twoLetter`, `mass_threeLetter`, `reflect_threeLetter_point` |
| Stable classes in charge coordinates: with `p = 4 Re Z`, `q = Im Z`, `v² ≥ -2` iff `(43r - 2(p + 2q))² + 43(4a - r - 2q)² ≤ 4(p + 2q)² + 172q² + 688` | `neg_two_le_selfPairing_iff` |
| Near the wall phases follow `B`-fractions: `j/(2j + 1)` (for `𝒪_C(j)`) increases below `1/2`, `j/(2j - 1)` (for `T_A 𝒪_C(j)`) decreases above it, and a subobject in the section-evaluation argument has fraction at most `j/(2j + 1)` | `cross_restrictedCharge`, `curveSheaf_fraction_strictMono`, `twistCurveSheaf_fraction`, `subobject_fraction_le` |
| `exp h_cat(T_{𝒪_C} T_{𝒪_C(2)}) = (4² - 2 + √(4⁴ - 4·4²))/2 = 7 + 4√3` (Barbacovi–Kim, arXiv:2107.06079), while points off `C` are fixed | `barbacoviKim_four`, `barbacoviKim_four_root` |

## Layout

The library mirrors Mathlib: a file sits at the Mathlib path of the API it extends, or of its
nearest Mathlib precedent, and its declarations use Mathlib's namespaces. Moving a file into
Mathlib or into derived-alg-geo-lean keeps its path below the library root.

| Module under `K3Twists/` | Job | Namespace |
|---|---|---|
| `Analysis/SpecificLimits/GrowthRate.lean` | exponential growth rates of sequences | `Real` |
| `LinearAlgebra/Lattice/Mukai/PicardRankOne.lean` | the Mukai lattice of a Picard-rank-one K3: pairing, roots, reflections, punctures | `MukaiVector` |
| `LinearAlgebra/Lattice/Mukai/Basic.lean`, `Mukai/Reflection.lean`, `BilinearForm/Hyperbolic.lean`, `BilinearForm/Reflection.lean`, `Lattice/Arithmetic/TorsionFree.lean` | the Mukai extension `ℤ ⊕ N ⊕ ℤ` of a bilinear lattice and its reflections, copied from derived-alg-geo-lean | `Mukai`, `BilinearForm`, `IntegralLattice` |
| `Combinatorics/Quiver/Kronecker/RealRoots.lean` | the real roots of the `g`-Kronecker quiver and their determinants | `Quiver.Kronecker` |
| `LinearAlgebra/Matrix/ZMatrix.lean`, `Matrix/ZMatrix/Integer.lean`, `Matrix/ZMatrix/Isotropic.lean` | symmetric Z-matrices: the ground-state identity, the M-matrix criterion, the affine kernel, integer certificates, isotropic sums of spheres, the wall matrix of a family and the Tits identity | `Matrix`, `LinearMap.BilinForm` |
| `LinearAlgebra/Matrix/Cartan/Basic.lean` | finite-type Cartan matrices from certificates; `E₆`, `E₇`, `E₈`, `Ẽ₈` | `Matrix`, `CartanMatrix` |
| `Combinatorics/Quiver/Kronecker/CartanMatrix.lean` | the wall matrix `[[2, -g], [-g, 2]]` of two spheres and its trichotomy | `Quiver.Kronecker` |
| `AlgebraicGeometry/Surface/K3/PicardRankOne/WallMatrix.lean` | the wall matrix of two spherical simples in Picard rank one | `AlgebraicGeometry.K3.PicardRankOne` |
| `AlgebraicGeometry/Surface/K3/EllipticWithSection/WallMatrix.lean` | the wall matrix of the curve wall and of a wall of pairing two | `AlgebraicGeometry.K3` |
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
| `RepresentationTheory/Quiver/Kronecker/Preprojective.lean` | representations of the doubled Kronecker quiver: preprojective relations, nilpotence, morphisms, isomorphisms, subrepresentations, dimension vectors, restrictions, quotients, subquotients, kernels and images | `Quiver.Kronecker` |
| `RepresentationTheory/Quiver/Kronecker/Ext.lean` | `Ext¹` by the standard complex, extensions as cocycles, the injection into `Ext¹(N, N)`, the dimension of `Ext¹` and Mukai's inequality | `Quiver.Kronecker` |
| `RepresentationTheory/Quiver/Kronecker/IncomingFlag.lean` | a rigid wall object is determined by its incoming flag, from the open-orbit input | `Quiver.Kronecker` |
| `RepresentationTheory/Quiver/Kronecker/TwoExtensions.lean` | the wall group that carries the point: classification and table of HN quotients | `Quiver.Kronecker` |
| `RepresentationTheory/Quiver/Kronecker/RigidRep.lean` | the rigid representation of dimension `(g², g)` with arrows in both directions | `Quiver.Kronecker` |
| `AlgebraicGeometry/Surface/K3/PicardRankOne/Visibility.lean` | punctures, clear sight lines, the lattice arguments of visibility on the cover, the finite search | same |
| `AlgebraicGeometry/Surface/K3/PicardRankOne/VisibilityOnCover.lean` | the lemma "Visibility on the cover" from its inputs | same |
| `Analysis/Complex/UpperHalfPlane/ProjectiveModel.lean` | the projective model `(Re z, \|z\|²)` of the half-plane, whose geodesics are straight | `UpperHalfPlane` |
| `LinearAlgebra/Lattice/Mukai/ProjectiveModel.lean` | the signature, negative cone and projective model of the Mukai lattice; reverse Cauchy–Schwarz | `MukaiVector` |
| `AlgebraicGeometry/Surface/K3/EllipticWithSection/Lattice.lean` | the Mukai lattice of an elliptic K3 with a section and the classes of its curve wall | `AlgebraicGeometry.K3.EllipticWithSection` |
| `AlgebraicGeometry/Surface/K3/EllipticWithSection/CurveWall.lean` | the charge of the curve wall, its phases, and the parity argument for the tails | same |

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

The wall lemmas beyond the quiver model are not formalized, nor is the socle step of the evaluation lemma (it needs the abelian length category `P(φ)`); neither is the higher-Picard-rank work. They need derived categories of K3 surfaces and stability conditions in Mathlib first. The tower algorithm is formalized from its inputs (`TowerHypotheses`), which are those statements. In the quiver model, the uniqueness of a rigid wall object given its incoming flag is proved from one input, `OpenOrbitHypotheses`: the open-orbit argument for `Aut(A) × Aut(B)` acting on `Ext¹(B, A)` needs algebraic groups acting on varieties, which Mathlib cannot use yet.
