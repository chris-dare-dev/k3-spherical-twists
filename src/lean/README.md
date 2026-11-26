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
| One Mukai lattice `MukaiLattice R N = R × N × R` over any commutative ring, with the form `⟨(r, c, s), (r', c', s')⟩ = b(c, c') - rs' - r's`; the Picard-rank-one lattice is the Mukai lattice of `(R, 2dxy)`, and the slice `(r, c, s) ↦ (r, cℓ, s)` of a class with `ℓ² = 2d` is isometric over every ring | `Mukai.mukaiForm`, `MukaiVector.isometryEquivMukaiLattice`, `Mukai.slice`, `Mukai.mukaiForm_slice`, `Mukai.slice_reflect` |
| A twist acts on Mukai vectors by the reflection in its root, which is Mathlib's `Module.preReflection` (`Module.reflection` at a root): an isometric involution with `T_Y Y = Y[-1]` on classes | `BilinearForm.reflectHom_eq_preReflection`, `BilinearForm.reflectEquiv_eq_reflection`, `BilinearForm.reflect_reflect`, `BilinearForm.apply_reflect_reflect`, `BilinearForm.reflect_self` |
| The half-turn for any isometry: if `ρ` preserves the Mukai form, `Ω` is isotropic and `ρΩ` has rank `r ≠ 0`, then `ρΩ = r · e` with `e` an exponential point and `r · Z_e(ρv) = Z_Ω(v)`, for `Z_Ω = ⟨Ω, -⟩`; no inverse, involution or symmetry | `Mukai.mul_charge_of_apply_eq_smul`, `Mukai.isIsotropic_expChart`, `Mukai.charge_halfTurn_of_isometry` |
| The slice lemma over any field: for `ℓ² = 2d` and `δ = (r, μℓ, s)` with `rs = dμ² + 1`, `ρ_δ(e^{zℓ}) = -dr²(z - μ/r)² e^{z'ℓ}` with `z' = μ/r - 1/(dr²(z - μ/r))`; `⟨δ, δ⟩ = -2` does not suffice in characteristic two | `Mukai.reflect_expSlice` |
| Eichler transvections `E(e, x, q)(v) = v + ⟨v, e⟩x - ⟨v, x⟩e - q⟨v, e⟩e` at an isotropic `e`: the group law `E(e, x, q)E(e, y, q') = E(e, x + y, q + q' + ⟨x, y⟩)`, isometry for `2q = ⟨x, x⟩`, `Eⁿ = E(e, nx, n²q)` (in general `E(e, nx, nq + C(n, 2)⟨x, x⟩)`), `(E - 1)³ = 0`, conjugation `gE(e, x, q)g⁻¹ = E(ge, gx, q)`; with a quadratic form, the Eichler homomorphism `e^⊥ → Aut(M)` into isometries, descending to `e^⊥/Re` when `Q(e) = 0` (Eichler, *Quadratische Formen und orthogonale Gruppen*, 1952) | `BilinearForm.eichler_mul`, `eichler_isometry`, `eichler_pow`, `eichler_pow_eq`, `eichler_sub_one_pow_three`, `conj_eichler`, `eichlerHom`, `eichlerQ_isometry`, `map_eichlerQ`, `eichlerQ_add_smul` |
| Two reflections: `ρ_b ρ_a = E(a + b, b, -1)` from `⟨a, b⟩ = 2` alone; the pair law `ρ_{a + kδ} ρ_a = E(δ, ka, -k²)` from `a² = -2`, `⟨a, δ⟩ = 0` (Kac, *Infinite dimensional Lie algebras*, §6.5, at `k = -1`); for spherical `a`, `b` with `⟨a, b⟩ = g`, `T = ρ_b ρ_a` satisfies `(T - 1)(T² - (g² - 2)T + 1) = 0`, and at `g = ±2` its powers are quadratic in `n` | `BilinearForm.reflectHom_mul_reflectHom_of_apply_eq_two`, `reflectHom_add_smul_mul_reflectHom`, `reflectHom_sub_mul_reflectHom`, `reflectHom_mul_reflectHom_cubic`, `reflectHom_mul_reflectHom_pow` |
| Two reflections at pairing `\|g\| > 2`: on the plane of `a`, `b` the product `ρ_b ρ_a` acts by `s₁ s₀ = [[-1, g], [-g, g² - 1]]`, the two simple reflections of the rank-two wall; the pairings along the orbit are `⟨a, (ρ_b ρ_a)ⁿ a⟩ = -(λⁿ + λ⁻ⁿ)` with `λ = (g² - 2 + √((g² - 2)² - 4))/2 > 1`, so `\|⟨a, (ρ_b ρ_a)ⁿ a⟩\|^{1/n} → λ`, and `‖(ρ_b ρ_a)ⁿ a‖^{1/n} → λ` for any norm on a finite-dimensional real space; `s₁ s₀` has Gelfand radius `λ` | `BilinearForm.reflectHom_mul_reflectHom_pow_smul_add_smul`, `abs_map_apply_reflectHom_mul_reflectHom_pow`, `tendsto_abs_map_apply_reflectHom_mul_reflectHom_pow`, `tendsto_norm_reflectHom_mul_reflectHom_pow`, `gelfandRadius_reflectionProductMatrix` |
| `⊗𝒪(D)` is the Eichler transvection `E(pt, (0, -D, 0), D²/2)` at the class of a point, with `D²/2` forced by the Mukai quadratic form `Q(r, c, s) = q(c) - rs`; line bundles compose by the group law; `ρ_{(0, C, 0)} ρ_{(0, C, 1)} = ⊗𝒪(C)` from `C² = -2`; `v(𝒪(mH)) = ⊗𝒪(mH) v(𝒪_X)` | `Mukai.tensorLine_eq_eichler`, `tensorLine_eq_eichlerQ`, `tensorLine_mul`, `reflectHom_mul_reflectHom_curve`, `slice_lineBundle` |
| The Tits identity: `B(Σ aᵢsᵢ, Σ aᵢsᵢ) = aᵀ G a` for the Gram matrix `G` of any finite family, and `-aᵀ A a` when `⟨sᵢ, sⱼ⟩ = -Aᵢⱼ` | `BilinearForm.apply_sum_smul_sum_smul`, `apply_sum_smul_sum_smul_of_apply_eq_neg`, `apply_smul_add_smul_self` |
| Affine simple roots of a connected exceptional fibre `Cᵢ` with fundamental cycle `Θ = Σ zᵢCᵢ` (`zᵢ ≥ 0`, `Θ² = -2`, `Θ·Cᵢ ≤ 0`; Artin, *On isolated rational singularities of surfaces*, Amer. J. Math. 88 (1966)): `α₀ = (0, Θ, 1)`, `αᵢ = (0, -Cᵢ, 0)`, `α₀ + Σ zᵢαᵢ = (0, 0, 1)`; full support `zᵢ > 0`; the extended Dynkin matrix `-⟨αₖ, αₗ⟩` with null vector `(1, z)`, positive semidefinite with isotropic vectors `ℤ(1, z)`; `⊗𝒪(L)αᵢ = αᵢ - (Cᵢ·L)δ`, `⊗𝒪(L)α₀ = α₀ + (Θ·L)δ`, trivial on the affine roots exactly when `L ⊥ Cᵢ` | `Mukai.FundamentalCycle`, `FundamentalCycle.mult_pos`, `affineRoot`, `sum_nullMult_smul_affineRoot`, `affineCartan_mulVec_nullMult`, `dotProduct_affineCartan_nonneg`, `eq_smul_nullMult_of_isotropic`, `tensorLine_affineRoot_some`, `tensorLine_fixes_affineRoot_iff` |
| The affine Weyl group `W_aff = ⟨ρ_{(0, c, s)} : c ∈ ⊕ℤCᵢ, c² = -2, s ∈ ℤ⟩` inside `O(Λ)` is `E(Q) ⋊ W(R)`: `ρ_{(0, c, s)} = ⊗𝒪(-sc) ρ_{(0, c, 0)}` by the pair law, a reflection conjugates `⊗𝒪(D)` to `⊗𝒪(ρ_c D)`, and `W(R) ∩ E(Q) = 1` by evaluating at `(1, 0, 0)` (Kac, *Infinite dimensional Lie algebras*, §6.5); `⊗𝒪(L) ρ_{(0, c, s)} ⊗𝒪(-L) = ρ_{(0, c, s + c·L)}`, so `W_aff` is normal in `W(R) ⋉ E(N)` | `FundamentalCycle.affineWeyl_eq_sup`, `reflect_eq_tensorLine_reflect`, `reflect_tensorLine_reflect`, `translations_normal`, `disjoint_finiteWeyl_translations`, `isComplement'`, `affineWeylEquiv`, `lineTwists_le_normalizer`, `affineWeyl_normal` |
| The fundamental-alcove theorem, by sign coherence with no highest-root theory: a rank-zero root `(0, Σ dᵢCᵢ, s)` has coordinates `(s, szᵢ - dᵢ)` in the affine simple roots, all `≥ 0` or all `≤ 0`, so every root of the fibre has `-z ≤ d ≤ z`; for `Z(0, c, s) = β·c - s`, `β·Cᵢ > 0`, `β·Θ < 1` iff `Z < 0` on every positive root, and then `Z ≠ 0` on every rank-zero root of the fibre; on the boundary of the closed alcove an affine simple root lies in `ker Z`. With the field that every `(-2)`-class orthogonal to `H` lies in `⊕ℤCᵢ` (Riemann–Roch on a K3 surface: a class with `D² = -2` or its negative is effective), `Z ≠ 0` on every rank-zero root orthogonal to `H`. The converse fails (`A₂`, `β·Cᵢ = 3/4`: a test) | `FundamentalCycle.signCoherent_affineCoord`, `le_mult_of_root`, `neg_mult_le_of_root`, `isInFundamentalAlcove_iff`, `fibreCharge_ne_zero`, `exists_fibreCharge_affineRoot_eq_zero`, `RiemannRochMembership`, `fibreCharge_ne_zero_of_riemannRochMembership` |
| Length-zero elements on classes: the automorphisms permuting the affine simple roots form a group with a homomorphism to the permutations of the nodes, whose range is a group; an isometry among them preserves the extended Dynkin matrix and the marks and fixes `δ`, so it sends `α₀` to a node of mark one (Bourbaki, *Groupes et algèbres de Lie*, Ch. VI, §2.3) | `FundamentalCycle.affineRootStabilizer`, `affineRootPerm`, `affineRootPermGroup`, `affineCartan_perm`, `nullMult_perm`, `nullMult_perm_none`, `apply_corankUnit_of_perm` |
| Simple reflections of a fibre: the affine simple roots are linearly independent; `sₖ = ρ_{αₖ}` maps the positive roots other than `αₖ` to positive roots; every positive root is `ω(αₖ)` for a word `ω` of simple reflections (descent on the height), so the simple reflections generate `W_aff` and those of the finite nodes generate `W(R)`; an element of `W_aff` keeping every affine simple root positive is the identity, so `W_aff` meets the stabilizer of the affine simple roots only in `1`; an automorphism preserving the roots that maps every affine simple root to a positive root permutes them | `FundamentalCycle.sum_smul_affineRoot_injective`, `IsPositiveRoot.reflect_affineRoot`, `exists_reflectWord_affineRoot`, `affineWeyl_eq_closure`, `finiteWeyl_eq_closure`, `eq_one_of_mem_affineWeyl`, `affineWeyl_inf_affineRootStabilizer`, `eq_one_of_mem_finiteWeyl`, `mem_affineRootStabilizer_of_forall` |
| Length-zero elements by descent, with no longest element: the inversion set of an automorphism preserving the roots is finite and drops by one under `g ↦ g sₖ` when `g αₖ < 0`, so every coset `g W_aff` contains exactly one element permuting the affine simple roots; at a minuscule node `j` (`zⱼ = 1`) and `M` with `M·Cᵢ = δᵢⱼ`, `⊗𝒪(M) ∘ w` permutes the affine simple roots and sends `α₀` to `αⱼ` for some `w ∈ W(R)` (Bourbaki, *Groupes et algèbres de Lie*, Ch. VI, §2.3, Proposition 6) | `FundamentalCycle.inversionSet_finite`, `ncard_inversionSet_mul_simpleReflection`, `exists_forall_isPositiveRoot`, `exists_mul_mem_affineRootStabilizer`, `eq_of_mul_mem_affineRootStabilizer`, `exists_lengthZero_of_minuscule` |
| The extended affine Weyl group is `E(N) ⋊ W(R)`: every element is `⊗𝒪(L) ∘ w`, `W(R)` conjugating `⊗𝒪(L)` to `⊗𝒪(wL)`; an element fixes every affine simple root iff it is `⊗𝒪(L)` with `L ⊥ Cᵢ`, so the group acts on the affine roots through `W(R) ⋉ Λ`; the degree of `L` modulo `Q^∨ = Aℤ^l` is a homomorphism on the length-zero elements with the same kernel as their permutation of the nodes; so the length-zero permutations form a group isomorphic to `Λ/Q^∨`, and for an even lattice with every degree realized to `P^∨/Q^∨ = ℤ^l/Aℤ^l`, of order `\|det A\|` (Iwahori–Matsumoto, Publ. Math. IHÉS 25 (1965)) | `FundamentalCycle.exists_tensorLine_mul_of_mem_extendedAffineWeyl`, `finiteWeyl_conj_tensorLine`, `translationPart`, `lengthZeroGroup`, `lengthZeroClass`, `ker_lengthZeroPerm`, `lengthZeroPermEquiv`, `exists_lengthZeroClass_eq`, `lengthZeroPermEquivOfDegreeLattice`, `card_lengthZeroPerm_range`, `fixes_affineRoot_iff` |
| The Weyl groups of a fibre as Coxeter groups: the affine simple roots pair to natural numbers, so their Gram matrix is `rootMatrix affineExt` and the reflections give the reflection representations of `W(ofExt affineExt)` and `W(ofExt finiteExt)` on the Mukai lattice, with images `W_aff` and `W(R)`; the classes are linearly independent. The sign of the class at the stratum: in the fundamental alcove a word is root-positive iff `Z = β·c - s < 0` on each prefix root, and in the fundamental Weyl chamber the same for words in the finite nodes; root-positivity for the finite nodes is the finite check on `ℤ^l`, and on a chain of curves the longest word of `A_n` is root-positive with `w₀(αᵢ) = -α_{n-1-i}` (`n ≤ 6`) | `FundamentalCycle.affineExt`, `mukaiForm_affineRoot_eq_rootMatrix`, `affineWeylRep`, `range_affineWeylRep`, `finiteWeylRep`, `range_finiteWeylRep`, `linearIndependent_affineRoot`, `chargeCone`, `isRootPositive_affineRoot_iff`, `isRootPositive_finiteRoot_iff`, `isRootPositive_finiteRoot_iff_rootForm`, `FundamentalCycle.isRootPositive_longestWordA`, `FundamentalCycle.reflectWord_longestWordA` |
| Roots of an orthogonal sum lie in one summand: for mutually orthogonal `x a` with `B(x a, x a) ≤ -2` unless `x a = 0`, a root `Σ x a` has all but one `x a` zero. So a `(-2)`-class on several orthogonal fibres lies on one of them, and the fundamental-alcove theorem holds for several fibres, with the Riemann–Roch membership field for their sum | `LinearMap.BilinForm.exists_forall_ne_eq_zero`, `FundamentalCycle.exists_forall_ne_eq_zero_of_root`, `FundamentalCycle.fibreCharge_ne_zero_of_sum`, `FundamentalCycle.fibreCharge_ne_zero_of_mem_sum` |
| The puncture of a root `(r, c, s)` is at height `1/(dr²)` above the parabola: `s/(dr) = (c/r)² + 1/(dr²)` | `MukaiVector.puncture_height` |
| `Z_{b+ia}` vanishes on the kernel line `(1, b, d(b² + a²))` | `charge_kernel` |
| The half-turn: `Z_{f(z)}(T_δ v) = -k Z_z(v)/(z - m)²` for `f(z) = m - k/(z - m)`, `m = c/r`, `k = 1/(dr²)`; `f` is an involution preserving the upper half-plane; `Z_z = ⟨e^{zH}, -⟩` and `f(z)` is the slice coordinate of the image point `ρ_δ(e^{zH})` | `charge_halfTurn`, `halfTurn_halfTurn`, `im_halfTurn_pos`, `charge_eq_mukaiCharge`, `reflect_expSlice_halfTurn` |
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
| A symmetric `2 × 2` matrix over a field has a nonzero isotropic vector iff minus its determinant is a square, from `a xᵀAx = (a x₀ + b x₁)² - (b² - ac) x₁²`; `no_null_vector` is the case `[[2, g], [g, 2]]` | `Matrix.exists_isotropic_iff_isSquare_neg_det`, `isSquare_neg_det_of_isotropic` |
| The ground-state (Picone) identity `2xᵀAx = 2Σ(Ap)ᵢpᵢyᵢ² - ΣAᵢⱼpᵢpⱼ(yᵢ - yⱼ)²` for `x = py` and symmetric `A` over any commutative ring; for a symmetric Z-matrix, with no hypothesis on the diagonal: positive definite iff some `p > 0` has `Ap > 0` (the M-matrix criterion, Berman–Plemmons, *Nonnegative Matrices in the Mathematical Sciences*, Ch. 6, Thm 2.3), `Ax ≥ 0 ⇒ x ≥ 0`, `A⁻¹ ≥ 0` and `A⁻¹𝟙 > 0`; a positive null vector `δ` gives positive semidefiniteness and, for indecomposable `A`, isotropic vectors `ℚδ`; a nonzero null vector `δ ≥ 0` of any symmetric matrix forbids `Ap > 0`; Mathlib's spectral bound for Z-matrices puts the eigenvalues of a positive definite wall matrix of spheres below `4` | `Matrix.IsSymm.picone`, `Matrix.IsZMatrix.posDef_iff_exists_certificate`, `nonneg_of_mulVec_nonneg`, `inv_nonneg_of_posDef`, `posSemidef_of_null`, `isotropic_eq_smul`, `Matrix.IsSymm.no_certificate_of_null`, `Matrix.IsZMatrix.eigenvalue_lt_two_mul` |
| Over `ℤ`: positive definite iff an integer `p > 0` has `Ap ≥ 1`; the isotropic integer vectors of an indecomposable symmetric Z-matrix with a positive primitive null vector `δ` are `ℤδ` | `Matrix.IsZMatrix.posDef_iff_int_certificate`, `isotropic_int_eq_zsmul` |
| Sign coherence: for a symmetric integer Z-matrix with even diagonal, nonnegative form, and every isotropic vector zero or of full support, every root `xᵀAx = 2` has all coordinates of one sign; from `q(x) ≥ q(x⁺) + q(x⁻)` and evenness of `q` | `Matrix.IsZMatrix.signCoherent`, `Matrix.IsZMatrix.dotProduct_mulVec_posPart_negPart`, `Matrix.IsSymm.even_dotProduct_mulVec` |
| A finite-type Cartan matrix from an integer certificate, and positive weights `Mp > 0` for every finite-type Cartan matrix; `E₆`, `E₇`, `E₈` by `p = 2ρ^∨` with `Ap = 2·𝟙`; `E 9 = Ẽ₈` has the null vector `(2, 3, 4, 6, 5, 4, 3, 2, 1)`, no certificate, affine type and isotropic vectors `ℤδ` | `Matrix.isFiniteCartan_of_certificate`, `Matrix.IsFiniteCartan.exists_certificate`, `CartanMatrix.isFiniteCartan_E_six`, `isFiniteCartan_E_seven`, `isFiniteCartan_E_eight`, `E_nine_no_certificate`, `E_nine_posSemidef_and_not_posDef`, `E_nine_isotropic_eq_zsmul` |
| `det Aₙ = n + 1` and `det Dₙ = 4` (`n ≥ 2`), from the expansion at a leaf `det M = 2 det M' - det M''`; for a fibre with Cartan matrix `A = -Gram(Cᵢ)`, the degrees `L ↦ (L·Cᵢ)` give `Aℤ^l ⊆ Λ_H ⊆ Λ ⊆ ℤ^l` with `[ℤ^l : Aℤ^l] = \|det A\|`, so `[ℤ^l : Λ]`, `[ℤ^l : Λ_H]` and `[Λ : Aℤ^l]` divide `\|det A\|` | `CartanMatrix.A_det`, `CartanMatrix.D_det`, `Matrix.det_eq_of_leaf`, `Mukai.FundamentalCycle.index_corootLattice`, `index_degreeLattice_dvd`, `index_polarizedDegreeLattice_dvd`, `relIndex_corootLattice_dvd` |
| The wall matrix `Aᵢⱼ = χ(Sᵢ, Sⱼ) = -⟨v(Sᵢ), v(Sⱼ)⟩` and the Tits identity `v(Σ aᵢSᵢ)² = -aᵀAa`; no nonzero `ℕ`-sum of spherical vertices is isotropic (`NoIsotropicSphereSum`); for three spheres pairwise pairings `≥ 3` do not give it (pairings `4, 5, 6`, isotropic sum `(4, 35, 3)`); the density statement that would relate it to `ℚ`-anisotropy is stated as a `Prop`, not proved | `LinearMap.BilinForm.wallMatrix`, `LinearMap.BilinForm.apply_sum_smul_self`, `Matrix.NoIsotropicSphereSum`, `Matrix.pairwise_three_not_sufficient`, `Matrix.ExistsPosIsotropicOfIsotropic` |
| Two spheres, `[[2, -g], [-g, 2]]`: positive definite iff `\|g\| < 2`, isotropic iff `g² - 4` is a square; for `g ∈ ℕ` finite iff `g ≤ 1`, affine iff `g = 2` (isotropic vectors `ℤ(1, 1)`), indefinite iff `g ≥ 3` and then anisotropic over `ℚ`; an isotropic sum only at `g = 2`, so for two spheres no isotropic `ℕ`-sum means `ℚ`-anisotropy; the two reflections multiply to trace `g² - 2` | `Quiver.Kronecker.cartanMatrix_posDef_iff`, `cartanMatrix_isotropic_iff`, `rank_two_trichotomy`, `cartanMatrix_two_isotropic_eq_zsmul`, `cartanMatrix_anisotropic`, `noIsotropicSphereSum_cartanMatrix_iff_anisotropic`, `trace_reflection_mul_reflection` |
| In Picard rank one, two roots of pairing `g ∈ ℕ` span a wall of finite, affine or indefinite type as `g ≤ 1`, `g = 2`, `g ≥ 3`; `v(𝒪_X)` and `v(𝒪_X(-H)[1])` pair to `d + 2`: an indefinite wall with no isotropic sum | `wallMatrix_trichotomy`, `span_roots_anisotropic_of_wallMatrix`, `noIsotropicSphereSum_wallMatrix`, `structureSheaf_shift_wall` |
| The wall group carrying the point: `v(N)² = 2q(g - q)`, and `e(N) ≤ 2` leaves `N = U` or a universal extension | `square_roots_plus_isotropic`, `twoExtensions_numerics` |
| The rigid wall example at `g = 3`: `dim End = 9`, the boundary roots `(8, 3) = R₂` and `(1, 3) = L₁` | `rigid_example` |
| The preprojective model of a wall with two spherical simples: representations `A_i : V₀ → V₁`, `B_i : V₁ → V₀` with `∑ B_i A_i = 0 = ∑ A_i B_i`, nilpotence, morphisms, the complete lattice of subrepresentations, on which the dimension vector is a valuation | `DoubledRep.IsPreprojective`, `DoubledRep.IsNilpotent`, `DoubledRep.Hom`, `DoubledRep.subreps`, `DoubledRep.dimVec_sup_add_inf` |
| The example *Arrows in both directions at a rigid wall*, for every `g`: `V₀ = H' ⊕ k·u`, `V₁ = W`, the relations, every path of length three vanishes, `dim End = g²`, and a subrepresentation is everything or lies in `H'` and contains the `g·dim U₁`-dimensional image of `W ⊗ U₁` | `rigidRep_isPreprojective`, `rigidRep_isNilpotent`, `finrank_rigidRep_End`, `RigidRep.eq_endOf`, `RigidRep.eq_top_or`, `RigidRep.dimVec_mem` |
| At `g = 3`: dimension `(9, 3)`, `dim End = 9`; plotting `(i, j)` at `(i + j, j)`, the upper boundary `(0, 0) → (11, 3) → (12, 3)` through `(H', W)` and the lower boundary `(0, 0) → (8, 0) → (12, 3)` through `(H', 0)`; `(H', W)` and `M/(H', 0)` are stable, of the real-root dimensions `(8, 3) = R₂` and `(1, 3) = L₁` | `rigidWall_finrank_End`, `rigidWall_dimVec_mem`, `rigidWall_upper`, `rigidWall_lower`, `rigidWall_upperCorner_stable`, `rigidWall_quotient_stable`, `rigidWall_stable_roots` |
| Valuations on a lattice (`f (x ⊔ y) + f (x ⊓ y) = f x + f y`): one injective on comparable pairs forces modularity (Birkhoff's argument for metric lattices, *Lattice theory*, Chapter X); the maximizers of a valuation form a sublattice, and for `deg - θ rk` with `rk` monotone the greatest maximizer is antitone in `θ` (Topkis's monotonicity theorem); along a chain from `⊥` to `⊤`, local maximizers give the global one | `isModularLattice_of_valuation`, `isMax_sup_inf_of_valuation`, `topkis`, `greatest_maximizer_antitone`, `val_le_of_chain`, `eq_of_val_eq_of_chain` |
| Harder–Narasimhan filtrations in a lattice with a charge function (valuations `rk`, `deg` with `(rk, deg)` lexicographically strictly monotone, so vertical steps of phase `⊤` are allowed; the lattice is then modular): the prefix with factor phases `≥ θ` below and `≤ θ` above maximizes `deg - θ rk`, uniquely if the inequalities are strict; the prefixes are `⊥` and the unique maximizers of these weights, the `⊥` case being needed when the first factor is vertical; the HN filtration is unique with no finiteness hypothesis, maps preserving the charge fix it, and it only depends on the order of phases | `ChargeFunction`, `ChargeFunction.isModularLattice`, `HNChain.weight_le`, `HNChain.eq_of_weight_eq`, `HNChain.mem_range_chain_iff`, `HNChain.instSubsingleton`, `HNChain.factorPhase_zero_eq_top_iff`, `HNChain.apply_chain_eq`, `HNChain.ofPhaseOrder` |
| Existence of HN filtrations for a charge function from the ascending chain condition and a maximal phase attained on every `[a, ⊤]` (the induction of Bridgeland, arXiv:math/0212237, Proposition 2.4); finitely many charge values give both, and bound the length of chains, so the main theorem is the one that reaches lattices of infinite length such as `O(D) ⊃ I_Z(D) ⊃ ⋯`. Neither hypothesis is necessary (models in `K3TwistsTest/ChargeFunctionModel.lean`) | `ChargeFunction.nonempty_hnChain`, `ChargeFunction.nonempty_hnFiltration`, `ChargeFunction.MaxPhaseAttained`, `nonempty_hnFiltration_of_finite_range`, `card_le_of_finite_range` |
| The HN polytope with a vertical edge (Baumann–Kamnitzer–Tingley, arXiv:1110.3661, §3.2): the hull of the points `(rk, deg)` lies right of the vertical line through `⊥`, which carries a vertical edge, and below every edge line of finite phase; the point of each nonzero prefix is exposed and the point of `⊥` is the lexicographic minimum | `HNChain.convexHull_subset`, `HNChain.weight_le_edge`, `HNChain.rk_chain_succ_eq_of_factorPhase_eq_top`, `HNChain.exists_exposed_succ`, `ChargeFunction.lex_le_of_mem_convexHull` |
| Slope functions (no vertical steps) as charge functions: their HN filtrations are those of the charge function, and the extremality, uniqueness and existence statements are corollaries; the filtration reads the upper boundary of the convex hull and the opposite one the lower boundary | `SlopeFunction.toChargeFunction`, `HNFiltration.toCharge`, `HNFiltration.ofCharge`, `HNFiltration.weight_le`, `HNFiltration.eq_of_weight_eq`, `HNFiltration.mem_range_chain_iff`, `HNFiltration.instSubsingleton`, `SlopeFunction.nonempty_hnFiltration`, `HNFiltration.convexHull_subset`, `HNFiltration.weight_ge_edge_of_neg`, `HNFiltration.ofSlopeOrder` |
| In an abelian category, a function additive on short exact sequences is a valuation on subobjects, `Z(A ⊔ B) + Z(A ⊓ B) = Z A + Z B`, through the short exact sequence `0 → A ⊓ B → A ⊞ B → A ⊔ B → 0`; if it vanishes only on zero objects the subobject lattices are modular; a stability function (Bridgeland, arXiv:math/0212237, Definition 2.1) gives a charge function on the subobjects of every object, with an HN filtration on a Noetherian object of attained maximal phase | `Subobject.infSupShortComplex_shortExact`, `Subobject.additive_sup_add_inf`, `Subobject.isModularLattice_of_additive`, `Subobject.chargeFunction`, `Subobject.nonempty_hnFiltration` |
| At a wall with two simples, a charge `i Z₀ + j Z₁` orders the subquotients by `j/(i + j)` on one side and by `i/(i + j)` on the other | `DoubledRep.slopeFunction`, `DoubledRep.slope_le_slope_iff`, `DoubledRep.slope_le_slope_iff_neg` |
| Every charge `i Z₀ + j Z₁` with `Z₀`, `Z₁` in the upper half-plane or on the negative real axis is a charge function on the subrepresentations of a finite-dimensional representation and has a unique HN filtration there, by the existence theorem; its phase order, vertical steps included, depends only on the side of the wall. For the rigid representation the filtration from the existence theorem is `0 ⊂ (H', W) ⊂ M` or `0 ⊂ (H', 0) ⊂ M`; for `Z₀ = -1` its first factor is vertical and `⊥` maximizes no weight | `DoubledRep.chargeFunction`, `DoubledRep.nonempty_hnFiltration`, `DoubledRep.chargeFunction_phase_le_phase_iff`, `RigidRep.range_hnFiltration_chain_upper`, `RigidRep.range_hnFiltration_chain_lower`, `RigidRep.verticalCharge_factorPhase_zero`, `RigidRep.verticalCharge_weight_bot_lt` |
| The HN filtrations of the rigid wall example, for every `g` and every charge on either side, are `0 ⊂ (H', W) ⊂ M` and `0 ⊂ (H', 0) ⊂ M`; at `g = 3` their polygons are `(0, 0) → (11, 3) → (12, 3)` and `(0, 0) → (8, 0) → (12, 3)` | `RigidRep.hnUpper`, `RigidRep.hnLower`, `RigidRep.hnUpperOf`, `RigidRep.hnLowerOf`, `rigidWall_hnUpper`, `rigidWall_hnLower` |
| The lemma on the wall group that carries the point, in the quiver model (`U` once at vertex one, `S` `p` times at vertex zero, `e(M) = 2` read as `dim End M + p(g - p) = 1`): `p ≥ g`, and `M = S^k ⊕ T_S U` (every `B_i = 0`, the `A_i` independent) or `M = S^k ⊕ T_S⁻¹ U` (every `A_i = 0`, the `B_i` independent), `k = p - g`; the rank dichotomy needs only the preprojective relation, nilpotence enters only for `p ≥ g` | `IsNilpotent.A_comp_B_eq_zero`, `finrank_End_ge`, `twoExtensions_rank`, `twoExtensions`, `twoExtensions_rank'`, `twoExtensions'` |
| The one-copy lemma: for any representation of the doubled Kronecker quiver with a line at vertex one and no relation, every endomorphism is a scalar plus a map `V/⟨B_i 1⟩ → ⋂ ker A_i`, so `dim End M = 1 + (p - b)(p - a)` with `a = rk A`, `b = rk B`, and `dim End M + p(g - p) = 1 + ab + p(g - a - b)`; with the preprojective relation `e(M) = 2` splits as `ab + p(g - a - b) = c - 1`, `c = 1 - v(U)²/2`, both terms nonnegative; `c = 1`: `ab = 0`, `a + b = g`; `c = 2`, `p ≥ 2` (one copy of a spherical simple): `a = b = 1`, `g = 2`, the classes `A_i = α_i φ` and `B_i 1 = β_i w` of rank one with `∑ α_i β_i = 0` and `φ(w) = 0`, and conversely every such rank-one datum is semirigid; Riemann–Roch for `U` and `M` gives `e(M) - e(U) = 2(ab + p(g - a - b))`, which is the HN defect only when `a = 0` or `b = 0` | `endOf_surjective'`, `finrank_End_eq`, `oneCopy_identity`, `oneCopy`, `oneCopy_one`, `oneCopy_two`, `oneCopy_two_rankOne`, `oneCopy_of_rankOne`, `oneCopy_two_range_evalA`, `oneCopy_riemannRoch` |
| Its table of HN quotients on both sides of the wall: where `U` is higher, `U, S^p` or `T_S⁻¹ U, S^k`; where `S` is higher, `S^k, T_S U` or `S^p, U`; for any wall object with `U` once, the HN filtrations are `0 ⊂ (⟨B_i⟩, U) ⊂ M` and `0 ⊂ (⋂ ker A_i, 0) ⊂ M` | `hnUHigher`, `hnSHigher`, `isStable_bot_subSpan`, `isStable_subKer_top`, `twoExtensions_table` |
| Interval classes on a lattice (`Q a b`, "`b / a` is in the class": reflexive, closed under extensions and under `s/a ↠ (a' ⊔ s)/a'`): under ACC the saturation `sat a`, the greatest `b ≥ a` with `Q a b`, is a closure operator and `rad = sat ⊥`; the nested formula `c ⊓ sat a` holds for all `a ≤ c` exactly when the class is hereditary, and its case `a = ⊥`, `t(A) = A ⊓ t(R)`, does not imply heredity; an order isomorphism matching two classes matches their saturations; the socle iteration of a generating layer reaches `sat a` in at most `ℓ(sat a) - ℓ(a)` steps for a length `ℓ` (the order core of torsion theory, Stenström, *Rings of Quotients*, Ch. VI) | `IntervalClass.satClosure`, `IntervalClass.isClosed_iff`, `IntervalClass.hereditary_iff_nested`, `IntervalClass.isGreatest_inf_rad`, `IntervalClass.sat_map`, `IntervalClass.Layer.socleSeq_eq_sat_of_le` |
| In an abelian category, "`b / a` lies in `P`" is an interval class on the subobjects of `R` when `P` contains zero and is closed under quotients and extensions (`0 → b/a → c/a → c/b → 0` is exact), hereditary when `P` is closed under subobjects; on a Noetherian `R` its radical is the largest subobject in `P`, and `t(A) = A ⊓ t(R)` | `ObjectProperty.intervalClass`, `ObjectProperty.subQ_trans`, `ObjectProperty.subQ_push`, `ObjectProperty.isGreatest_intervalClass_rad`, `ObjectProperty.isGreatest_inf_intervalClass_rad` |
| For a representation of the doubled Kronecker quiver, the subquotients supported at vertex zero form a hereditary interval class with saturation `(⋂ Aᵢ⁻¹ N₁, N₁)` and radical `(⋂ ker Aᵢ, 0)`; where `U` occurs once, that radical is the first step of the HN filtration on the side where `S` is higher | `DoubledRep.sat_vertexZeroClass`, `DoubledRep.rad_vertexZeroClass`, `DoubledRep.hnSHigher_chain_one` |
| From the proposition on rigid wall groups: the outgoing HN flag determines subobjects of the retained wall object independently of the representative. An isomorphism `M ≅ N` carries the HN filtration of `M` to that of `N` on either side, and every automorphism fixes the HN prefixes (in a lattice: any map preserving rank and degree fixes them) | `DoubledRep.Iso.mapSubrep`, `Iso.map_hnFiltration`, `Iso.map_hnFiltration_neg`, `Iso.mapSubrep_chain`, `HNFiltration.apply_chain_eq`, `HNFiltration.map` |
| `Ext¹` of representations with the preprojective relations, by the standard complex `⊕ Hom(X_v, Y_v) → ⊕ Hom(X_{t(a)}, Y_{h(a)}) → ⊕ Hom(X_v, Y_v)`: `H⁰ = Hom`; an extension `0 → A → N → B → 0` is a cocycle placed in the off-diagonal block, every subrepresentation presents its representation as such an extension, and classes related by isomorphisms of the ends (cohomologous classes in particular) give isomorphic extensions | `DoubledRep.Ext1`, `ker_d₀₁`, `isPreprojective_extension_iff`, `offDiag_mem_cocycles₁`, `exists_iso_extension`, `extensionIso` |
| From the proposition on rigid wall groups: for an extension `ξ` with middle term `N` and `Hom(A, B) = 0`, `v ↦ i v p` induces an injection `Ext¹(B, A)/(End(A)ξ + ξ End(B)) ↪ Ext¹(N, N)`; so `Ext¹(N, N) = 0` gives `Ext¹(B, A) = End(A)ξ + ξ End(B)` | `extQuotPushPull_injective`, `orbitSpan_eq_top`, `cocycles₁_le_orbitTangent` |
| From the same proposition: a prefix `M_j` of an HN filtration has no maps to the next factor `M_{j+1}/M_j` (a nonzero map would give subobjects `K < M_j ≤ I` with `w(K) + w(I) = 2w(M_j)`, while `M_j` is the only maximizer of a weight `w`), and along such a flag the prefixes of a rigid representation are rigid | `Hom_restrict_subquotient_eq_bot`, `exists_subreps_of_mem_Hom`, `subsingleton_Ext1_restrict_of_chain` |
| `dim Ext¹(X, Y) = dim Hom(X, Y) + dim Hom(Y, X) - (x, y)`, `(x, y) = 2x₀y₀ + 2x₁y₁ - g(x₀y₁ + x₁y₀)` (Crawley-Boevey, Amer. J. Math. 122 (2000), Lemma 1), from the duality of the two differentials under the trace pairing; Mukai's inequality with its defect, `e(N) = e(A) + e(B) + 2 dim Ext¹(B, A)/(End(A)ξ + ξ End(B))` when `Hom(A, B) = 0` (Bayer–Bridgeland, arXiv:1310.8266, Lemma 2.5), so both ends of a rigid extension are rigid; the rigid example has `Ext¹ = 0` | `finrank_Ext1`, `dualMap_d₀₁_comp_tracePairing₁`, `finrank_Ext1_extension`, `finrank_Ext1_add_le`, `rigid_of_rigid_extension`, `subsingleton_Ext1_rigidRep` |
| The Mukai budget lemma in the quiver model: `e(X) = dim Ext¹(X, X)` is invariant under isomorphism and even, `e = 2 dim End + v²` (Riemann–Roch, `e = 2 + v²` only when `End = k`), and along a flag whose prefixes have no maps to the next subquotient, so along the HN filtration of every charge on either side of the wall, `∑ e(M_{j+1}/M_j) ≤ e(M)` | `DoubledRep.Iso.selfExtDim_eq`, `even_selfExtDim`, `selfExtDim_eq`, `selfExtDim_add_le`, `sum_selfExtDim_subquotient_le`, `sum_selfExtDim_le_of_hnFiltration` |
| Representations of the double of any finite quiver `Q` with loops (vertex type `I`, arrow sets `Q i j`), with the preprojective relation `∑_{a : j → i} A_a B_a - ∑_{a : i → j} B_a A_a = 0` at each vertex (the commutator `[A_a, B_a]` for a loop): morphisms, isomorphisms, the complete lattice of subrepresentations with the dimension vector as a valuation, restrictions, quotients, and the charge function `(∑ r_i dim U_i, ∑ d_i dim U_i)` of weights with `0 < r_i` or `r_i = 0 < d_i`, with a unique HN filtration on every finite-dimensional representation | `Quiver.Preprojective.DoubledRep.relation`, `DoubledRep.subreps`, `DoubledRep.dimVec_sup_add_inf`, `DoubledRep.Iso.mapSubrep`, `DoubledRep.chargeFunction`, `DoubledRep.nonempty_hnFiltration` |
| Crawley-Boevey's formula for any quiver with loops: `dim Ext¹(X, Y) = dim Hom(X, Y) + dim Hom(Y, X) - (x, y)`, `(x, y) = ∑_i 2x_iy_i - ∑_{a : i → j}(x_iy_j + x_jy_i)` (Crawley-Boevey, Amer. J. Math. 122 (2000), Lemma 1), from the standard complex and the duality of its differentials under the trace pairing; `e = 2 dim End - 2q(x)`, even, so a brick has `q ≤ 1`, is rigid iff `q = 1` and has `e = 2` iff `q = 0` | `DoubledRep.finrank_Ext1_eq`, `DoubledRep.dualMap_d₀_comp_tracePairing₁`, `DoubledRep.selfExtDim_eq`, `DoubledRep.even_selfExtDim`, `DoubledRep.titsForm_le_one_of_brick`, `DoubledRep.titsForm_eq_one_or_eq_zero_of_brick` |
| Mukai's inequality for any quiver with loops, `e(A) + e(B) ≤ e(N) + 2 dim Hom(A, B)` for an extension `N` of `B` by `A` (a dimension count of block upper triangular endomorphisms), so `e(A) + e(B) ≤ e(N)` when `Hom(A, B) = 0` (Bayer–Bridgeland, arXiv:1310.8266, Lemma 2.5); a subrepresentation presents a representation as an extension; along a Hom-orthogonal flag `∑ e(M_{j+1}/M_j) ≤ e(M)` | `DoubledRep.selfExtDim_add_le_add`, `DoubledRep.selfExtDim_add_le`, `DoubledRep.exists_iso_extension`, `DoubledRep.sum_selfExtDim_subquotient_le` |
| The Kronecker files are the two-vertex case: a doubled Kronecker representation is a representation of the double of the wall quiver with no loops, with the same relations, morphisms, subrepresentations and `e`, so the rigid representation is rigid for the general complex; with one loop at the isotropic vertex and a line there, `e(M) = 2 dim End M - 2(p² - gp)`, so `e(M) = 2` for the general complex is the hypothesis of the lemma on the wall group that carries the point, which then holds | `DoubledRep.ofKronecker`, `DoubledRep.isPreprojective_ofKronecker_iff`, `DoubledRep.ofKroneckerSubrepsIso`, `DoubledRep.selfExtDim_ofKronecker`, `DoubledRep.selfExtDim_ofKronecker_rigidRep`, `DoubledRep.selfExtDim_pointWall`, `DoubledRep.twoExtensions_of_selfExtDim_eq_two` |
| A fully faithful functor preserving monomorphisms reflects the order of subobjects, and is an order isomorphism of subobject lattices when every subobject of `G X` comes from `X`; so for an equivalence of abelian categories carrying a class `P` to `P'`, `b/a ∈ P` iff `Gb/Ga ∈ P'`, and `G` carries saturations and the radical of the interval class of `P` to those of `P'` | `Functor.subobjectOrderIso`, `Functor.mapSubobject_le_mapSubobject_iff`, `Functor.subobjectOrderIsoOfIsEquivalence`, `ObjectProperty.subQ_mapSubobject_iff`, `ObjectProperty.mapSubobject_intervalClass_sat`, `ObjectProperty.mapSubobject_intervalClass_rad` |
| Relabelling the arrows of the doubled Kronecker quiver (`Equiv.Perm ι`) preserves the preprojective relations and the morphism spaces, `Hom(σM, σN) = Hom(M, N)`, so it carries the profile `dim Hom(A, -)` to `dim Hom(σA, -)`; with two arrows it moves the profile of `k ⇉ k` with arrows `(1, 0)` to a different profile | `DoubledRep.Hom_smul`, `DoubledRep.smul_homDimProfile` |
| `RHom(A, -)` on preprojective representations as a fibre-functor profile: `Ext² = C²/im d₁₂` of the standard complex has `dim Ext²(X, Y) = dim Hom(Y, X)`, so `dim Hom(A, E) - dim Ext¹(A, E) + dim Ext²(A, E) = (a, e)` and `dim Hom + dim Ext¹ + dim Ext² ≥ \|(a, e)\|` with the same parity | `DoubledRep.finrank_Ext2`, `homFibreFunctorProfile`, `abs_cartanForm_le` |
| Fekete with a constant: the rate exists, each block certifies `ρ ≤ (K H_k)^{1/k}`, and the bounds converge | `exists_rate_of_submul`, `pow_rate_le` |
| Transfer of rates between comparable sequences, uniformly in parameters; `o(n)` errors; polynomial growth has rate one; the rate per letter of a periodic word | `tendsto_rpow_inv_of_bounds`, `tendstoUniformly_rpow_inv_of_bounds`, `tendsto_log_div_of_bound`, `tendsto_log_div_zero_of_poly`, `tendsto_log_div_of_period` |
| Fekete's lemma with a gap and no monotonicity: `ℓ(m) + ℓ(n) ≤ ℓ(m + n + D)` with bounded certificates gives `ℓ(N)/N → sup_{q ≥ 1} ℓ(q)/(q + D)` (the supremum must start at `q = 1`); lower certificates for every `q + D > 0`, upper certificates from a block bound; for positive `P` with `c P_m · c P_n ≤ c P_{m+n+D}` and `P_{n+q} ≤ K(q) P_n`, `log(c P_q)/(q + D) ≤ lim log P_N / N ≤ log K(q)/q`; `⌊N/p⌋/N → 1/p` | `tendsto_div_of_superadd_gap`, `le_of_superadd_gap`, `le_div_of_block`, `fekete_sandwich`, `tendsto_natDiv_div` |
| Padding with a one-sided step bound: `x_n ≥ c > 0` and `x_n ≤ L x_{n+1}` give `x` the rate of an attained running maximum; with `x_n ≤ K A_n` and `A_n ≤ K(n + 1) B_n` the exact-length rate is the rate of `A` | `tendsto_log_div_of_runningMax`, `tendsto_log_exact_of_coupled` |
| `m^n 2^{⌈√n⌉}` is submultiplicative with rate `m`, loses at least `2^{(2 - √2)√k - 1}` under doubling, and has no polynomial envelope `B(1 + n)^s m^n` | `sqrtWitness_add_le`, `tendsto_sqrtWitness`, `sqrtWitness_doubling`, `not_exists_poly_envelope_sqrtWitness` |
| Fork words `W_0 = H`, `W_i = ⁅W_{i-1}, L_i⁆` with commuting `L_i` and `H L_i H = L_i H L_i` are conjugate to `H L_i⁻¹` by `L_1⁻¹ ⋯ L_i⁻¹` | `forkWord_succ_eq_conj` |
| A nonnegative matrix applied to a seed `c ≥ m > 0` grows at its Gelfand radius, `‖Aⁿc‖^{1/n} → gelfandRadius A`, with no irreducibility, primitivity or Perron vector; the Gelfand radius of a real matrix is the spectral radius of its complexification; `\|E\| ≤ P` entrywise gives `gelfandRadius E ≤ gelfandRadius P` | `Matrix.tendsto_rate_of_pos`, `tendsto_rate_of_pos_spectralRadius`, `spectralRadius_map_ofReal`, `gelfandRadius_le_of_abs_le` |
| Certificates without Perron–Frobenius: for `L ≥ 0`, a vector `v ≥ m > 0` with `Lv ≤ ρv` gives `‖Lᵏ‖ ≤ (‖v‖/m)ρᵏ` and `gelfandRadius L ≤ ρ`; a vector `0 ≤ v ≠ 0` with `tv ≤ Lv` gives `t ≤ gelfandRadius L` (Collatz, Math. Z. 48 (1942); Wielandt, Math. Z. 52 (1950)) | `Matrix.norm_pow_le_of_mulVec_le`, `gelfandRadius_le_of_mulVec_le`, `le_gelfandRadius_of_smul_le_mulVec` |
| Block-triangular certificates: for `L ≥ 0` block upper triangular with `c` blocks whose diagonal blocks share a subinvariant vector `v ≥ m > 0` of ratio `ρ > 0`, and `Lv ≤ Kv`, `‖Lᵏ‖ ≤ 3(‖v‖/m)(1 + K/ρ)^{c-1}(1 + k)^{c-1}ρᵏ`, so `gelfandRadius L ≤ ρ`; a domination `X_{n+q} ≤ X_n L` by such a tower matrix with `ρ = λ^q`, `λ ≥ 1`, gives `‖X_n‖ ≤ B(1 + n)^{c-1}λⁿ` | `Matrix.norm_pow_le_of_blockTriangular`, `gelfandRadius_le_of_blockTriangular`, `norm_le_of_le_mul_of_blockTriangular` |
| Variational upper bounds: `X_{n+q} ≤ X_n L` entrywise for nonnegative matrices, `q ≥ 1`, gives `limsup ‖X_n‖^{1/n} ≤ gelfandRadius(L)^{1/q}`; `b_n^{1/n} → λ ≥ 1` and `‖L_q‖ ≤ 1 + A Σ_{k<q} b_k` give `limsup gelfandRadius(L_q)^{1/q} ≤ λ` | `Matrix.limsup_rpow_inv_le_of_le_mul`, `exists_norm_le_mul_pow_of_le_mul`, `limsup_gelfandRadius_rpow_inv_le` |
| The infimum over periods is a limit: if `‖X_n‖^{1/n} → λ ≥ 1` and every period `q ≥ 1` has `L_q ≥ 0` with `X_{n+q} ≤ X_n L_q` and `‖L_q‖ ≤ 1 + A Σ_{k<q} ‖X_k‖`, then `gelfandRadius(L_q)^{1/q} → λ` and `λ = inf_{q ≥ 1} gelfandRadius(L_q)^{1/q}` | `Matrix.tendsto_gelfandRadius_rpow_inv_of_le_mul`, `iInf_gelfandRadius_rpow_inv_eq` |
| `x² = tx - 1` in an algebra gives `xⁿ = S_{n-1}(t)x - S_{n-2}(t)` with Mathlib's rescaled Chebyshev polynomials, and `S_n(l + l⁻¹)(l - l⁻¹) = l^{n+1} - l^{-(n+1)}`; Cayley–Hamilton for `2 × 2` matrices and the powers of one of determinant one | `Polynomial.Chebyshev.pow_eq_S_eval_smul_sub`, `S_eval_add_inv_mul_sub_inv`, `Matrix.sq_eq_trace_smul_sub_det_smul`, `pow_eq_S_eval_trace_smul_sub` |
| The matrix Chebyshev series `S_m(C) = aeval C (Chebyshev.S m)` (`S_{m+2}(C) = C S_{m+1}(C) - S_m(C)`, the coefficients of `(1 - Ct + t²)⁻¹`); `S_m = Xᵐ + (lower terms)`; reachability at the graph distance: if `(Cʲ)_{ab} = 0` for `j < d` then `S_j(C)_{ab} = 0` for `j < d` and `S_d(C)_{ab} = (C^d)_{ab}`, so for a simple graph `S_m(A)_{uv}` vanishes below the distance, counts the shortest walks at it and vanishes in all degrees without a walk; the Euler characteristic of the normalized bar complex of a graded algebra with Hilbert matrix `1 + Ct + t²`, each term signed by its cohomological degree, is `S_m(C)`; for two spheres with `g` arrows each way the off-diagonal odd entries are the Kronecker numbers `u_{m+1}`. From two fields (the routed complex is that bar complex, by formality of the `Ext` algebra, Davison, arXiv:2106.07692, Proposition 7.8; exact dimensions off Dynkin components, by Koszulity of the preprojective algebra, Etingof–Eu, arXiv:math/0606403): the routed Euler characteristic and `Tor` vanish below the graph distance and are nonzero at it | `Polynomial.Chebyshev.coeff_S_self`, `Matrix.chebyshevS`, `Matrix.chebyshevS_apply_eq_pow_apply`, `Matrix.chebyshevS_apply_eq_zero`, `SimpleGraph.chebyshevS_adjMatrix_apply_dist`, `SimpleGraph.chebyshevS_adjMatrix_apply_dist_pos`, `Matrix.barEuler_eq_chebyshevS`, `Matrix.chebyshevS_kronecker_apply_zero_one`, `SimpleGraph.routedEuler_eq_zero_of_lt_dist`, `SimpleGraph.routedTor_dist_pos` |
| A real `2 × 2` matrix of determinant one and trace `l + l⁻¹`, `l > 1`, has Gelfand radius `l` (no eigenvector); the Thurston product `[[1, aμ], [0, 1]][[1, 0], [bμ, 1]]` has rate `λ` with `λ + λ⁻¹ = 2 + abμ²` (Thurston, Bull. Amer. Math. Soc. 19 (1988)), and `λ = 1 + 2g² + 2g√(g² + 1)` at `a = b = 2`, `μ = g` | `Matrix.gelfandRadius_eq_of_det_eq_one`, `gelfandRadius_thurston`, `gelfandRadius_thurston_two_two` |
| With the root supplied: a real `2 × 2` matrix of determinant one and trace `t > 2` has Gelfand radius `(t + √(t² - 4))/2 > 1`, a root of `x² - tx + 1` | `Matrix.gelfandRadius_eq_sl2Rate`, `one_lt_gelfandRadius_of_det_eq_one`, `gelfandRadius_sq_sub_trace_mul_add_one`, `sl2Rate_eq_of_add_inv` |
| Thurston's compression `(x, y) ↦ (uᵀx, vᵀy)` carries the letters of two bipartite multitwists to the Thurston matrices, using only `uᵀG = μvᵀ` and `Gv = μu`; for `G ≥ 0`, letters with nonnegative exponents and a seed with positive compression, the total mass of `Wⁿz` grows at the Gelfand radius of the Thurston product | `Matrix.BipartiteCompression.compress_act`, `compress_word`, `compress_iterate`, `tendsto_rate_of_compress_pos` |
| The star word `H ∏ L_i⁻¹` with `d ≥ 1` leaves grows at `(d + 2 + √(d² + 4d))/2`, the larger root of `t² - (d + 2)t + 1`: the compression to hub and leaf sum gives the Thurston product of trace `d + 2` | `Matrix.BipartiteCompression.tendsto_star_rate`, `starRate_root` |
| The joint spectral radius of a finite family (Rota–Strang, Indag. Math. 22 (1960)) exists; each length certifies an upper bound and each word `w` the lower bound `gelfandRadius(A_w)^{1/\|w\|}`; for `s ≥ 1`, `JSR([[1, s], [0, 1]], [[1, 0], [s, 1]]) = (s + √(s² + 4))/2`; the triangle letters `1 + e_i G_{i*}` have joint spectral radius at least the tribonacci constant `τ ∈ (1.8, 1.9)` | `Matrix.tendsto_jointSpectralRadius`, `jointSpectralRadius_le`, `gelfandRadius_rpow_le_jointSpectralRadius`, `jointSpectralRadius_unipotent_pair`, `exists_tribonacci_le_jointSpectralRadius_triangle` |
| The single twists `1 + e_k G_{k*}` of a bipartite graph `G ≥ 0` with weights at most `s ≥ 1` have joint spectral radius at most `(s + √(s² + 4))/2` at every valence, with equality when an edge has weight `s` both ways; the proof compresses to the two colour sums, dominated by the unipotent pair | `Matrix.jointSpectralRadius_graphTransvection_le`, `jointSpectralRadius_graphTransvection_bipartite`, `partSums_graphTransvection_mulVec_le`, `exists_sphereMax_le_mul_pow` |
| The Thompson pseudometric `sup_s \|log x - log y\|` and the Hilbert projective pseudometric, the oscillation of `log x - log y` on `s`, with values in `[0, ∞]` (Thompson, Proc. Amer. Math. Soc. 14 (1963); Birkhoff, Trans. Amer. Math. Soc. 85 (1957)): extended pseudometrics, zero exactly on equal (Thompson) or proportional (Hilbert) positive functions, `d_H ≤ 2 d_T`, `d_H` invariant under positive rescaling, isometric reindexing | `thompsonEDist_triangle`, `thompsonEDist_eq_zero_iff`, `hilbertEDist_triangle`, `hilbertEDist_eq_zero_iff`, `hilbertEDist_le_two_mul_thompsonEDist`, `hilbertEDist_smul_left`, `thompsonEDist_comp`, `hilbertEDist_comp` |
| Birkhoff's contraction for a positive `2 × 2` matrix `[[a, b], [c, d]]` (Birkhoff, Trans. Amer. Math. Soc. 85 (1957); Hopf, J. Math. Mech. 12 (1963)): its ratio map `x ↦ (ax + b)/(cx + d)` is Lipschitz in `log x` with constant `\|√(ad) - √(bc)\|/(√(ad) + √(bc)) = tanh(\|log(ad/bc)\|/4) < 1`, with no condition on the determinant; equivalently `d_H(Mx, My) ≤ tanh(Δ/4) d_H(x, y)` on the positive cone of `ℝ²` | `Matrix.abs_log_ratioMap_sub_le`, `Matrix.birkhoffCoeff_eq_tanh`, `Matrix.birkhoffCoeff_lt_one`, `Matrix.hilbertEDist_mulVec_le` |
| The coding map of finitely many uniform contractions of a complete metric space (Hutchinson, Indiana Univ. Math. J. 30 (1981)): limits of `f_{ω 0} ∘ ⋯ ∘ f_{ω (n-1)}` from any start, the shift equation, uniform convergence and continuity, the unique fixed point for a periodic word, and a closed embedding of `β^ℕ` (a Cantor set) for injective letters with disjoint images | `IFS.tendsto_comp_codingMap`, `IFS.codingMap_eq`, `IFS.continuous_codingMap`, `IFS.eq_codingMap_of_periodic`, `IFS.isClosedEmbedding_codingMap` |
| The two-block alphabet: the count matrices `M_b = [[1 + 2bg², 2g], [bg, 1]]` of the blocks `T₁²T₂^{-b}` have Birkhoff coefficient `(√(1 + 2bg²) - √(2bg²))/(√(1 + 2bg²) + √(2bg²))` and transposed ratio map `bg + 1/(2g + 1/x)`; for `b ∈ {2, 4}` every infinite word has a centre ratio `[b₀g; 2g, b₁g, 2g, …]`, the limit of its finite continued fractions, and for `g ≥ 1/2` the centre ratio embeds `{2, 4}^ℕ` as a Cantor set (the count matrices are an input; mass profiles are not formalized) | `Matrix.birkhoffCoeff_twoTwistBlock`, `Matrix.ratioMap_transpose_twoTwistBlock_eq_cf`, `IFS.centreRatio_eq`, `IFS.tendsto_centreRatio`, `IFS.isClosedEmbedding_centreRatio` |
| Polynomial envelope of powers: `∏_{μ ∈ s}(a - μ) = 0` with `‖μ‖ ≤ ρ`, `ρ > 0`, in a normed algebra gives `‖aᵏ‖ ≤ C(1 + k)^{\|s\| - 1}ρᵏ`; a complex `r × r` matrix with eigenvalues of modulus at most `ρ` has `‖Mᵏ‖ ≤ C(1 + k)^{r - 1}ρᵏ` (the bound of a Schur form, proved from Cayley–Hamilton); it fails at `ρ = 0` | `exists_norm_pow_le_of_aeval_eq_zero`, `Matrix.exists_norm_pow_le_of_forall_mem_spectrum`, `Matrix.exists_norm_pow_le_of_forall_mem_spectrum_of_one_le`, `Matrix.not_exists_norm_pow_le_of_spectrum_zero` |
| Profiles `Obj → ℝ≥0` with `(g • μ)(E) = μ(g⁻¹E)` (Mathlib's `arrowAction` on a type synonym): `g • h(A, -) = h(gA, -)` for an invariant count; `g` carries limits and cluster points of normalized profiles to `g • (limit)` for any filter and normalizer, so `m_{gσ} = g • m_σ` passes to limits; the Thompson and half-Hilbert pseudometrics over a set of objects are `Γ`-isometric, invariant over a `Γ`-invariant set, and `d_S ≤ d_T` | `Profile.homProfile_smul`, `Profile.tendsto_normalized_smul`, `Profile.tendsto_normalized_of_equivariant`, `Profile.mapClusterPt_smul_iff`, `Profile.thompsonEDist_smul`, `Profile.halfHilbertEDist_smul`, `Profile.halfHilbertEDist_le_thompsonEDist` |
| The defect identity: a long exact sequence `⋯ → K_j → E_j → Q_j → K_{j+1} → ⋯` of finite-dimensional spaces has `P_E = P_K + P_Q - (1 + t)R` with `R = Σ rk(δ_j)tʲ`, and `R` is unique; at `t = -1` Euler characteristics add, at `t = 1` totals add up to the defect `2R(1)` | `LinearMap.finrank_add_finrank_range_connecting`, `LinearMap.poincare_eq_of_exact`, `LaurentPolynomial.poincare_eq_sub_mul`, `LaurentPolynomial.defect_unique`, `LaurentPolynomial.poincareNegOne_eq_add`, `LaurentPolynomial.poincareOne_add_two_mul` |
| Parity: `\|P(-1)\| ≤ P(1)` and `P(-1) ≡ P(1) mod 2` for `f : ℤ →₀ ℕ`; a fibre-functor profile (`μ = P(1)`, `χ = P(-1) = -⟨w, v⟩`) has `μ ≥ \|⟨w, v(-)⟩\|` with the same parity | `Finsupp.abs_poincareNegOne_le`, `Finsupp.poincareNegOne_modEq`, `FibreFunctorProfile.abs_le_mass`, `FibreFunctorProfile.modEq_mass` |
| The Crofton constant `∫₀^{2π} \|cos(θ - α)\| dθ = 4` and the barycentre `Σ\|z_j\| = (1/4)∫₀^{2π} Σ\|Re(e^{-iθ}z_j)\| dθ`; the directional ratio `Σ\|Re(e^{-iθ}z_j)\|/Σ\|z_j\|` lies in `[0, 1]`, is `1`-Lipschitz in angular distance and has average `2/π` | `Complex.integral_abs_cos_sub`, `Complex.sum_norm_eq_integral`, `Complex.directionalRatio_mem_Icc`, `Complex.abs_directionalRatio_sub_le_norm`, `Complex.average_directionalRatio` |
| The algebra of Lemma A.1: the slope estimate `V(E) ≤ aR + d^{-1/2}√(Rm)` and the absorption of the square root | `piece_bound`, `slope_bound_of_le`, `fixedTest_of_generic` |
| The Koszul bound `7^s` and the constant `K = 5(2 + 36ν)(2 + 25ν)⁸7⁴⁶` | `koszul_bound`, `diag_constant` |
| A standard word has `H_n = 18 + 12ν + 9du²n²` | `standard_H_formula` |
| `Θ = T_S T_B` with `v(B) = v(S)` acts trivially on classes while `h(B, Θⁿ S) ≥ M(M - 1)^{2n}` | `theta_acts_trivially`, `theta_lower_bound` |
| `Ψ = T_𝒪 T_L` on the plane of `v(𝒪), v(L)`: trace `(d + 2)² - 2`, determinant one, an eigenvalue `ρ > 1`, irrational eigenlines; on the whole lattice `(Ψ - 1)(Ψ² - ((d + 2)² - 2)Ψ + 1) = 0` | `psi_action`, `psi_eigenvalue`, `psi_discriminant_not_square`, `psi_cubic` |
| In an abelian category, a nonsplit extension of two simple objects has exactly three subobjects, and an object `M` with `A ⊂ P ⊂ M` glued from two such extensions (`P` and `M/A` nonsplit) has exactly the chain `0 ⊂ A ⊂ P ⊂ M` | `ShortComplex.ShortExact.subobject_eq_of_nonsplit`, `subobject_eq_of_nonsplit_of_nonsplit` |
| `dim(J + XJ) ≥ dim J + 1` for a nonzero finite-dimensional `J ⊆ K[X]`, the dehomogenized `dim(sJ + tJ) ≥ dim J + 1` behind the stability of the section-evaluation objects `Q_d` | `Polynomial.finrank_lt_finrank_sup_map_mulLeft_X` |
| Two HN filtrations of one object with nonzero factors have the same length, phases and factors (Bridgeland, arXiv:math/0212237, §3) | `HNFiltration.exists_iso_of_nonzero` |
| Two distinguished triangles on one object, each first vertex orthogonal to both third vertices, are isomorphic | `Pretriangulated.exists_iso_of_hom_eq_zero` |
| An exact autoequivalence `Φ` carries HN filtrations for `s` to HN filtrations for `Φ s` with the same phases, and by uniqueness to all of them; `Φ(Φ⁻¹ s) = s` | `TriEquiv.mapHN`, `TriEquiv.exists_iso_of_hnFiltration`, `TriEquiv.act_symm_act` |
| The homotopy pullback `B_i = B ×_M M_i` of the tower algorithm, from the octahedral axiom: `A → B_i → M_i`, `B_{i-1} → B_i → M_i/M_{i-1}` and the induced connecting map | `Pretriangulated.exists_pullback_triangles` |
| HN filtrations concatenate along a triangle when their phases are separated; an HN filtration whose factors carry HN filtrations with separated phases refines to one with their factors, counted additively | `HNFiltration.exists_concat`, `HNFiltration.exists_refinement` |
| Exactly one factor carrying the point survives a wall crossing from its local inputs, a finite path of walls, and a letter | `WallCrossing.carriesOnce`, `Leg.carriesOnce`, `TriEquiv.carriesOnce_map` |
| Carrying the point once is "at most once" (at most one factor with `Pt`, each factor `Pt` or `Rg`) plus existence of a carrier | `HNFiltration.carriesOnce_iff`, `Slicing.carriesOnce_of_hasCarrier` |
| `dim Hom(E, E⟦n⟧)` is invariant under isomorphism in any `k`-linear category, with no linearity of the shift; a `2`-spherical object has `Hom(E, E⟦1⟧) = 0` | `finrank_shiftHom_congr`, `selfExtDim_congr`, `selfExtDim_eq_zero_of_isSphericalObject` |
| Evaluation of one phase, in any slicing: `Hom(S, M) ≅ Hom(S, D)` for the top quotient `M → D → C` and `S` of phases at least `φ` (and dually at the bottom); a residual of phases at most `φ` with no maps from `P(φ)` has phases below `φ`; the fibre of `D → D_final` is `M → D`; one evaluation step keeps the lower tail `C` | `Slicing.comp_bijective_of_top`, `Slicing.comp_bijective_of_bottom`, `Slicing.ltProp_of_leProp_of_hom_eq_zero`, `Slicing.exists_iso_top`, `Slicing.exists_evaluation_step` |
| A coreflection `ε : D ⟶ R` into a class `P` (`D` in `P`, and every map from an object of `P` to `R` factors uniquely through `ε`) is the partial right adjoint of the inclusion at `R`, unique up to isomorphism over `R`. In an abelian category it is a monomorphism if `P` is closed under subobjects or under quotients, and then the largest subobject in `P`; it exists if `P` contains zero, is closed under quotients and extensions and `R` is Noetherian, or if `C` is well-powered with coproducts and `P` is closed under quotients and coproducts. `t(R)` is the supremum of the images of the maps from a generator; `Ext¹(-, K₀)` is left exact on `P` when `t(K₀) = 0`; a test class and a potential that drops on kernels give a torsion pair `(⊥F, F)` (Dickson, Trans. Amer. Math. Soc. 121 (1966)) | `ObjectProperty.IsCoreflection`, `rightAdjointObjIsDefined_ι_iff`, `isLeftAdjoint_ι_iff`, `IsCoreflection.isoOfIsCoreflection`, `IsCoreflection.mono_of_subobjects`, `IsCoreflection.mono_of_quotients`, `IsCoreflection.isGreatest`, `exists_isGreatest_subobject`, `isLeftAdjoint_ι_of_isNoetherianObject`, `isGreatest_sSup`, `isLUB_imageSubobject_of_generator`, `mk₀_comp_injective_of_rightOrthogonal`, `torsionTheory_of_potential` |
| In a slicing, the top quotient `M → D` of the evaluation lemma is the coreflection of `D` into the objects of phases at least `t`, so it is unique over `D`; every object has a coreflection into the objects of phases above `t`, so their inclusion is a left adjoint | `Slicing.isCoreflection_geProp_of_top`, `Slicing.isoOfTop`, `Slicing.exists_isCoreflection_gtProp`, `Slicing.isLeftAdjoint_ι_gtProp` |
| A slicing and `a ∈ ℝ` give a bounded t-structure in Mathlib's sense: aisle `P(> a)`, coaisle `P(≤ a + 1)`, heart the half-open interval `P((a, a+1])` (Bridgeland, arXiv:math/0212237, §3), from the HN filtration cut at `a`; the thin interval category `P((a, a+1))` lies in the heart but is not it | `Slicing.toTStructure`, `Slicing.toTStructure_heart`, `Slicing.instHeartHeartCat`, `Slicing.toTStructure_bounded`, `Slicing.exists_distTriang_gtProp_leProp`, `Slicing.intervalProp_le_heartProp` |
| The heart of any t-structure is abelian (Beilinson–Bernstein–Deligne, *Faisceaux pervers*, Théorème 1.3.6; a TODO in Mathlib's `TStructure/Heart.lean`), through Mathlib's criterion `AbelianSubcategory.abelian`: Homs from the heart to negative shifts of the heart vanish, every morphism of the heart is admissible, and the heart has finite biproducts; its short exact sequences are the distinguished triangles on heart objects. So the heart `P((a, a+1])` of a slicing is abelian, and so is the heart of the canonical t-structure on `D(A)` | `TStructure.heartAbelian`, `TStructure.heartFullSubcategoryAbelian`, `TStructure.ιHeart_hom_shift_eq_zero`, `TStructure.admissibleMorphism_ιHeart`, `TStructure.hasFiniteProducts_heart`, `TStructure.shortExact_of_distTriang`, `TStructure.exists_distTriang_of_shortExact`, `Slicing.instAbelianHeartCat` |
| In the heart `P((a, a+1])` of any slicing, `(P(a+1), P((a, a+1)))` is a torsion pair, and so is `(P((θ, a+1]), P((a, θ]))` for `θ ∈ [a, a+1]`; the torsion sequence of an object is its HN filtration cut at a phase. Given a charge `w : K₀ → ℝ` positive on nonzero semistable objects of phase in `(a, a+1)` and zero on `P(a+1)` (for a prestability condition `w = Im(e^{-iπa} Z)`), `w` is nonnegative on the heart with kernel `P(a+1)`, so `P(a+1)` is a Serre class of the heart and the torsion pair is hereditary; for a bare slicing `P(a+1)` need not be closed under subobjects. In an abelian category, the kernel of a nonnegative function additive on short exact sequences is a Serre class, and two classes with no maps from the first to the second and a torsion sequence for every object form a torsion pair | `Slicing.torsionTheory_heartTop`, `Slicing.torsionTheory_heartAbove`, `Slicing.weight_eq_zero_iff_of_heartProp`, `Slicing.isSerreClass_heartTop`, `Slicing.heartTop_hereditary`, `PreStabilityCondition.WithClassMap.heartWeight`, `PreStabilityCondition.WithClassMap.isSerreClass_heartTop`, `ObjectProperty.isSerreClass_of_additive_nonneg`, `Abelian.TorsionTheory.of_shortExact` |
| The converse of tilting at a torsion pair (Happel–Reiten–Smalø, Mem. Amer. Math. Soc. 120 (1996), Chapter I, §2; in the form of Polishchuk, arXiv:math/0606013, Lemma 1.1.2), with the inclusion of aisles `D_t^{≤-1} ⊆ D_{t'}^{≤0} ⊆ D_t^{≤0}` as hypothesis: every object of the heart `A` of `t` has a torsion triangle (its `t'`-truncation), `(A ∩ D_{t'}^{≤0}, A ∩ D_{t'}^{≥1})` is a torsion pair in `A`, and the heart of `t'` is its tilt (`E` lies in `t`-degrees `[-1, 0]` with `τ_{≥0} E` torsion and `τ_{<0} E` torsion-free). For a prestability condition, `Z` is a stability function on `P((0, 1])`, and a heart in degrees `[0, 1]` of `P((0, 1])` on which `Z` is a stability function is `P((0, 1])`; so two prestability conditions with the same `Im Z`, hearts so related and `Re Z < 0` on the phase-one objects of the second have the same heart and the same phase-one objects in it | `TStructure.exists_distTriang_heart_of_le`, `TStructure.torsionTheory_of_le`, `TStructure.mem_heart_iff_of_le`, `PreStabilityCondition.WithClassMap.charge_mem_of_heartProp`, `PreStabilityCondition.WithClassMap.heart_eq_of_le`, `PreStabilityCondition.WithClassMap.heartProp_eq_of_im_eq`, `PreStabilityCondition.WithClassMap.phase_one_iff_of_im_eq` |
| The radical, interval-class and charge-function layers at the heart `P((a, a+1])`. For any slicing, every object `R` of the heart has a largest subobject of phase `a + 1` (the first term of its torsion sequence, a coreflection), with no chain condition on `R`, and the inclusion of `P(a+1)` is a left adjoint; so too for `P((θ, a+1])`; `P(a+1)` is a torsion class, so its interval class on `Subobject R` is defined. For a prestability condition that interval class is hereditary and the restriction formula `t(A) = A ⊓ t(R)` holds for every subobject, again with no chain condition; on `P((0, 1])`, `rk = Im Z` and `deg = -Re Z` form a charge function on subobjects, the subobject lattices are modular, and HN filtrations of subobjects exist on Noetherian objects whose maximal phase is attained | `Slicing.isCoreflection_heartTop`, `Slicing.exists_isGreatest_heartTop`, `Slicing.isLeftAdjoint_ι_heartTop`, `Slicing.isCoreflection_heartAbove`, `Slicing.isGreatest_intervalClass_rad_heartTop`, `PreStabilityCondition.WithClassMap.intervalClass_heartTop_hereditary`, `PreStabilityCondition.WithClassMap.isGreatest_inf_heartTop`, `PreStabilityCondition.WithClassMap.heartChargeFunction`, `PreStabilityCondition.WithClassMap.isModularLattice_subobject_heart`, `PreStabilityCondition.WithClassMap.nonempty_hnFiltration_heart`, `ObjectProperty.isCoreflection_of_shortExact` |
| In a slicing, every object splits as `E_{≥t} → E → E_{<t}` (as well as `E_{>t} → E → E_{≤t}`), and `E_{≥t} → E` is its coreflection into the objects of phases at least `t`; in each pair `(P(≥ t), P(< t))`, `(P(> t), P(≤ t))` each class is the orthogonal of the other, so all four are closed under extensions; an object of phases at least `t` and at most `t` is semistable of phase `t` (Bridgeland, arXiv:math/0212237, §3) | `Slicing.exists_split_geProp_ltProp`, `Slicing.exists_split_gtProp_leProp`, `Slicing.exists_isCoreflection_geProp`, `Slicing.geProp_iff_hom_eq_zero`, `Slicing.ltProp_iff_hom_eq_zero`, `Slicing.gtProp_iff_hom_eq_zero`, `Slicing.leProp_iff_hom_eq_zero`, `Slicing.geProp_ext₂`, `Slicing.ltProp_ext₂`, `Slicing.gtProp_ext₂`, `Slicing.leProp_ext₂`, `Slicing.semistable_of_geProp_of_leProp` |
| The cut criterion for cones, in any slicing: for a triangle `U → E → Q →δ U⟦1⟧`, the cut composite `d_t : Q_{≥t} → U_{<t}⟦1⟧` and `E' = cofib(U_{≥t} → E)`, (A) `E_{≥t} = E ×ʰ_{E'} E'_{≥t}` and `E'_{≥t} → Q_{≥t}` represents `ker(d_t ∘ −)` on `P(≥ t)`; (B) a compatible truncation triangle `U_{≥t} → E_{≥t} → Q_{≥t}` exists iff that map is an isomorphism iff `d_t = 0`, with a unique lift of `Q_{≥t} → U⟦1⟧` (always, if `U` has no phase below `t`); (C) if `Q` has no phase above `θ`, `E'_{≥θ} → Q_{≥θ}` is the largest monomorphism in `P(θ)` killed by `d_θ` (Bapat–Deopurkar–Licata, arXiv:2011.07908, Appendix A, for one triangle) | `Pretriangulated.exists_cofib_triangles`, `Slicing.exists_geProp_pullback`, `Slicing.cutMap_injective`, `Slicing.exists_comp_cutMap_iff`, `Slicing.isIso_cutMap_iff`, `Slicing.cut_criterion`, `Slicing.existsUnique_cut_lift_iff`, `Slicing.exists_truncation_triangle_of_geProp`, `Slicing.cutMap_top_phase` |
| Flag reassembly gives additive mass: if the cut composite `d_t` of a triangle `U → E → Q` vanishes for every `t`, then `m(E) = m(U) + m(Q)`. The charge of the part of `X` of phases at least `t` is `∑_{φ_i ≥ t} Z(A_i)` for any HN filtration and any truncation; its jumps are the charges of the factors of each phase, which lie on one ray, and the mass is the sum of their norms (Bridgeland, arXiv:math/0212237, §8). The converse needs the heart cohomology `H⁰` as a homological functor, not in the library | `PreStabilityCondition.WithClassMap.mass_eq_add_of_forall_cutVanishes`, `PreStabilityCondition.WithClassMap.charge_coreflection_eq_chargeGe`, `PreStabilityCondition.WithClassMap.mass_eq_sum_norm_jump`, `Slicing.CutVanishes` |
| Every HN filtration can be replaced by one with nonzero factors and phases among its own; so in the tower algorithm the outgoing clause for a wall group that does not carry the point is a theorem from the slice fields: its outgoing HN filtration can be chosen with nonzero factors, all spherical and not carriers, in the same phase windows, and a wall crossing needs only the grouping, the ordered flags and the carrier clause. On the rank-free form each of these inputs is an existence statement, and the carrier clause follows from the anisotropy of a named wall step from the wall slicing (through `WallStep.lost_isotropic`); the grouping and a named wall then give a transport step with the Gram matrices of the wall's stable spheres, with no flags and no octahedral insertion, and the flags name the factors after the wall: one carrier factor, an outgoing factor of the carrier group, the others spherical outgoing factors of the other groups | `HNFiltration.exists_nonzero_factors`, `SliceFields.exists_outgoing_noncarrier`, `WallCrossing.ofSliceFields`, `WallCrossing.ofHasCarrier`, `WallStep.hasCarrier_of_semistable`, `WallCrossing.ofWallStep`, `CarrierStep.ofGrouping`, `SliceFields.exists_named_refinement` |
| The divisibility obstruction: for `P` semistable of phase `φ` with scalar endomorphisms and a triangle `P → E → Q →c P⟦1⟧` (a rotated twist triangle, `E = T_S P`, `Q = S⟦1⟧^{⊕ r}`), `P` is a direct summand of the phase-`φ` HN factor `G` of `E` if `c` vanishes on `Q_{≥φ}`, and otherwise `Hom(Q_{≥φ}, P) ≅ Hom(G, P)`, so `dim Hom(G, P) = r · dim Hom(S⟦1⟧_{≥φ}, P)`; dually `Hom(P, Q_{≤φ}) ≅ Hom(P, G)` for `Q → E → P` (Seidel–Thomas, arXiv:math/0001043, §2, for the twist triangles); truncations of finite biproducts; retracts are direct summands | `Slicing.divisibility_obstruction_top`, `Slicing.divisibility_obstruction_bottom`, `Slicing.divisibility_obstruction_top_finrank`, `Slicing.divisibility_obstruction_bottom_finrank`, `Slicing.isCoreflection_biproduct_map`, `Slicing.exists_iso_biproduct_of_leProp`, `Pretriangulated.exists_iso_biprod_of_retraction` |
| One unit of weight: for a pre-stability condition and `w = Im(e^{-iπa} Z)` (additive, zero on `P(a)` and `P(a + 1)`, positive on `P((a, a + 1))`), if every nonzero semistable object of phase in `(a, a + 1)` has `w ≥ δ` (for instance if `w(Λ) ⊆ δℤ`) and `E` has phases in `[a, a + 1]` with `0 < w(E) < 2δ`, the HN tower of `E` is `0 → T → E' → E` with `T = E_{≥ a+1}` of phase `a + 1`, `E' = fib(E → B) = E_{>a}`, `B` of phase `a`, and `S = cofib(T → E')` stable of a phase in `(a, a + 1)` with `w(S) = w(E)` | `PreStabilityCondition.WithClassMap.imChargeAt`, `imChargeAt_triangle`, `exists_imChargeAt_eq_of_semistable`, `le_imChargeAt_of_mem_zmultiples`, `one_unit_of_weight`, `one_unit_of_weight_of_triangle` |
| **Window dévissage**: if a triangulated functor `F` is surjective on `Hom(S, T⟦n⟧)` for `a - 1 ≤ n ≤ b` and injective for `a ≤ n ≤ b + 1`, for all `S`, `T` in a family, the same holds on the (inductive) extension closure of the family; for `a ≤ 0 ≤ b`, `F` is fully faithful there, and for `a ≤ 2`, `1 ≤ b` its essential image there is the extension closure of the images (the model is Bondal–Orlov, arXiv:alg-geom/9506012, Theorem 1.1, and Bridgeland, arXiv:math/9809114, Theorems 1.1 and 2.3); a functor commuting with shifts preserves the composition of shifted morphisms with no sign; in an abelian category the extension closure of simple objects is a Serre class | `Functor.isExtWindow_of_extensionClosure`, `Functor.IsExtWindow.of_vanishing`, `Functor.fullyFaithfulOfIsExtWindow`, `Functor.map_extensionClosure_eq`, `Functor.map_shiftedHom_comp`, `ObjectProperty.extensionProductIter_le_extensionClosure`, `ObjectProperty.isSerreClass_abelianExtensionClosure` |
| The isotropic-family lemmas. The degree-two lemma: if `φ₂(μ(v, w)) = μ'(φ₁ v, φ₁' w)`, `dim X ≤ 1`, `φ₁` is nonzero somewhere, `φ₁'` onto and `μ'` separates its left argument, then `φ₂` is injective. The Serre pairing is composition followed by the Serre trace, and at an object with `S X ≅ X⟦2⟧` the composition–trace pairing on `Hom(X, Y⟦1⟧) × Hom(Y, X⟦1⟧)` separates both arguments, so a functor commuting with shifts that is nonzero on `Ext¹(S, U)` and onto `Ext¹(F U, F S)` is injective on `Ext²(S, S)` when `dim Ext²(S, S) ≤ 1`. Orthogonality: for `P`, `Q` with no negative extensions either way, `Hom(P, Q) = 0 = Hom(Q, P)` and `S P ≅ P⟦2⟧`, `Hom(P, Q⟦i⟧) = 0` for `i ≠ 1` and `dim Ext¹(P, Q) = -χ(P, Q)`, so `P`, `Q` are orthogonal iff `χ(P, Q) = 0`. Poincaré duality: if `A_i × A_{d-i} → A_d` separates its left argument and `dim A_d ≤ 1`, an algebra map nonzero on `A_d` is injective in every degree `i ≤ d`; with target duality, equal dimensions and `B_{⌈d/2⌉} ≠ 0`, it is nonzero on `A_d` iff it is injective in degrees `≤ ⌈d/2⌉`. In a spectral space a directed cover by constructible sets has a member equal to the space, and every constructible cover has a finite subcover | `LinearMap.injective_of_pairing_of_finrank_le_one`, `SerreFunctorData.pairing_eq_trace_comp`, `SerreFunctorData.compTrace_separating_left`, `Functor.injective_map_shiftedHom_two`, `TwoCYHypotheses.injective_map_shiftedHom_two`, `SerreFunctorData.finrank_ext_one_eq_neg_euler`, `SerreFunctorData.ext_eq_zero_iff`, `AlgHom.injOn_of_top`, `AlgHom.exists_top_ne_zero_iff`, `Topology.exists_eq_univ_of_directed_of_isConstructible`, `Topology.exists_finite_subcover_of_isConstructible` |
| The short-step stability test, (A): in any slicing, `E ∈ P([l, r])` if and only if `Hom(P(> r), E) = 0` and `Hom(E, P(< l)) = 0`; the phase cuts of a nonzero object through its intrinsic phases `φ^±` | `Slicing.mem_closedInterval_iff`, `Slicing.leProp_iff_phiPlus_le`, `Slicing.geProp_iff_le_phiMinus`, `Slicing.semistable_of_phiPlus_le_of_le_phiMinus` |
| The short-step stability test, (B), the Im-form test: let `τ`, `ν` be slicings with `\|φ^±_ν - φ^±_τ\| < ε ≤ 1/4` on nonzero objects and `Z` compatible with `ν`. Then `Y` with `Z(Y) ∈ ℝ_{>0} e^{iπφ}` is `ν`-semistable of phase `φ` if and only if `Y ∈ P_τ([φ - ε, φ + ε])` and no triangle `N → Y → Q` with `N, Q ≠ 0` in `P_τ([φ - 3ε, φ + 3ε])` has `Im(e^{-iπφ} Z(N)) > 0`; it is stable if and only if none has `Im(e^{-iπφ} Z(N)) ≥ 0` | `Slicing.semistable_iff_imPhase`, `Slicing.isStable_iff_imPhase`, `Slicing.PhaseClose` |
| The mass `m_σ(E) = Σ \|Z(A_i)\|` over the HN factors is well defined, because HN filtrations agree up to zero factors on every isomorphism-invariant sum; it is invariant under isomorphisms and shifts, `\|Z(E)\| ≤ m_σ(E)` with equality for semistable `E`, positive on nonzero objects, and splits at every phase: `m(E) = m(E_{> t}) + m(E_{≤ t})` | `HNFiltration.sum_factor_eq`, `PreStabilityCondition.WithClassMap.mass_eq_sum`, `mass_iso`, `mass_shift`, `norm_charge_le_mass`, `mass_eq_norm_charge_of_semistable`, `mass_pos`, `mass_eq_add_of_triangle`, `exists_mass_split` |
| The `2m(D)` lemma: for `m` invariant under shifts and subadditive on triangles, if `f, f' : A → B` differ by a map through `D`, their cones satisfy `\|m(cone f) - m(cone f')\| ≤ 2m(D)`; for the mass under Ikeda subadditivity | `abs_sub_mass_cone_le`, `PreStabilityCondition.WithClassMap.abs_sub_mass_cone_le` |
| The Artin group of a Coxeter matrix (Mathlib has none) and its surjection onto the Coxeter group; the pure Artin group is the normal closure of the squares `σ_i²`; a representation whose generators are involutions factors through the Coxeter group and kills the pure Artin group | `CoxeterMatrix.ArtinGroup`, `toCoxeterGroup_surjective`, `pureArtinGroup_eq_normalClosure`, `exists_factor_of_sq`, `pure_mem_ker_of_sq` |
| A braid relation of length `m` is one conjugation identity `u f(i') u⁻¹ = f(c)`, `u` the alternating word of length `m - 1`; a conjugation-equivariant `τ : X → G` turns one object identity per edge into the braid relations, for every Coxeter matrix; braid relations are closed under reversal, which gives the anti-automorphism `σ_i ↦ σ_i` | `CoxeterMatrix.braid_iff_conj`, `isBraidLiftable_of_equivariant`, `isBraidLiftable_op_iff`, `ArtinGroup.reverse` |
| An Artin group acts on slicings through any family of exact autoequivalences whose classes satisfy its braid relations (from pairwise braid isomorphisms, or in the Seidel–Thomas form, arXiv:math/0001043, §2); two signed words with the same image in the Artin group are naturally isomorphic and carry HN filtrations to each other, with the same phases and isomorphic factors; the pure Artin group lands in the normal closure of the squared twists | `AutQuot.artinHom`, `AutQuot.isBraidLiftable_of_iso`, `AutQuot.isBraidLiftable_ofExt`, `AutQuot.nonempty_iso_of_ofSignedWord_eq`, `AutQuot.hn_of_ofSignedWord_eq`, `AutQuot.map_pureArtinGroup_le` |
| For a homological `F : C ⥤ A` and a Serre class `P` of `A`, the objects with `F(X[n]) ∈ P` for every `n` form a thick subcategory (triangulated, closed under isomorphisms and retracts; for `P = 0` Verdier's homological kernel); the Verdier form: a composite of letters, each joined to the identity by a natural transformation with cones in a triangulated `K`, preserves `K` and is isomorphic to the identity after any functor inverting the cones in `K`; the Serre-preimage theorem for twist words: if `F(E[j])` and `F(S[j])` lie in `P` for every centre `S`, so does `F(Y[i])` for every object `Y` reached from `E` by evaluation or coevaluation triangles at the centres (Seidel–Thomas, arXiv:math/0001043, §2); in `D(A)`, the complexes with cohomology in `P` | `Functor.serrePreimage`, `ObjectProperty.IsWordModulo.prop_iff`, `IsWordModulo.nonempty_iso`, `IsWordModulo.nonempty_iso_obj_shift`, `ObjectProperty.prop_iff_of_reflTransGen`, `Functor.prop_obj_shift_of_reflTransGen`, `DerivedCategory.mem_serrePreimage_homologyFunctor_iff`, `DerivedCategory.singleFunctor_mem_serrePreimage_iff` |
| A central element `z` (Mathlib's `CatCenter`) commuting with a letter: a faithful letter preserves annihilators, `Ann(ΦX) = Ann(X)`, and inverses of autoequivalences inherit `z`-linearity; `z` kills retracts of objects it kills; along a distinguished triangle `X → E → Y` with `Hom(X, Y[-1]) = 0`, `z_E = 0` gives `z_X = z_Y = 0`, so `z` kills every prefix and every factor of every HN filtration of `E` and both pieces of a truncation at a phase cut; `Ann(X)·Ann(Y) ⊆ Ann(E)` along any triangle. | `Functor.CommutesWithCenter`, `CatCenter.annihilator_map_eq`, `CatCenter.app_eq_zero_of_retract`, `CatCenter.app_obj₁_eq_zero`, `app_obj₃_eq_zero`, `HNFiltration.app_factor_eq_zero`, `Slicing.app_eq_zero_of_cut`, `CatCenter.annihilator_mul_le` |
| The polynomial modulus lemma: if `\|P(n)\| ∈ cℤ` for all large integers `n`, for a complex polynomial `P` and `c > 0`, then `P P̄ = q²` for a real polynomial `q`; a monic quadratic with this property is real or `(X + b)²`, and `(X + i)²` shows that `b` need not be real | `Polynomial.exists_mul_map_conj_eq_sq`, `Polynomial.exists_eq_sq_of_eventually_mem_zmultiples`, `Polynomial.im_eq_zero_or_eq_sq_of_mul_map_conj_eq_sq` |
| The sector budget: for a closed cone `K` in an open half-space of a finite-dimensional space, `κ_K Σ ‖z_j‖ ≤ ℓ(Σ z_j)`; for the Euclidean sector of half-width `b ≤ 1/2`, `cos(πb) Σ \|z_j\| ≤ p_φ(Σ z_j) ≤ \|Σ z_j\|` | `Complex.exists_pos_mul_norm_le_of_isClosed`, `Complex.sum_norm_mul_le`, `Complex.sum_norm_mul_cos_le_phaseProj`, `Complex.sum_norm_le_norm_sum_div_cos` |
| The selection lemma in increment form: a continuous function equal at every point to one of finitely many functions with `g_j(t) - g_j(u) ≥ -L(t - u)` satisfies the same bound; a continuous selection from finitely many monotone functions is monotone | `sub_le_of_continuousOn_of_selection`, `monotoneOn_of_continuousOn_of_selection` |
| The support property `‖v‖ ≤ D \|Z(v)\|` on a finite-rank real Mukai lattice: only finitely many classes of bounded charge; Finsler's lemma; the support property on classes of square at least `-2` when `ker Z` is negative definite and holds no such class, a condition necessary for any `D`; in signature `(2, n)` the kernel of a positive period is negative definite; `k` stable constituents of norm at least `μ` in a sector of half-width `b ≤ 1/2` have `k μ cos(πb) ≤ D p_φ(v)` | `Mukai.SupportProperty.finite_norm_le`, `Mukai.exists_finsler`, `Mukai.exists_supportProperty`, `Mukai.not_supportProperty_of_mem_ker`, `Mukai.negDef_orthogonal_of_posPlane`, `Mukai.exists_supportProperty_realCharge`, `Mukai.card_mul_cos_le_of_sector` |
| The completed square `Re Z/r = δ/2 - b(u - β, u - β)/2 - 1/r²` for a root with `Im Z = 0` of the normalized charge `Z = xr - s + b(β, c) + i(b(H, c) - ar)`, and the root test: a violating root of positive rank has `r² ≤ 2/δ` and `u` in an ellipsoid, the violating roots are finitely many, and there are none once `δ > 2`. In Picard rank one it is the height `1/(dr²)` of a puncture, and `finite_obstacles` is its shadow | `Mukai.re_normalizedCharge_div_rank`, `Mukai.rank_sq_le_of_re_nonpos`, `Mukai.neg_le_of_re_nonpos`, `Mukai.finite_violations`, `Mukai.re_normalizedCharge_pos`, `AlgebraicGeometry.K3.PicardRankOne.re_div_rank_eq_height` |
| On the K3 surfaces of the library: in Picard rank one the central charge `Z_p` has the support property where `d·height(p) > 1`; at the curve wall of the elliptic K3 with a section (Tramel–Xia, arXiv:1702.06252) `δ = 43/8`, every root of positive rank with `Im Z = 0` has `Re Z > 0`, and the charge has the support property | `AlgebraicGeometry.K3.PicardRankOne.exists_supportProperty_modelCharge`, `AlgebraicGeometry.K3.EllipticWithSection.normalizedDelta_curveWall`, `AlgebraicGeometry.K3.EllipticWithSection.re_charge_pos`, `AlgebraicGeometry.K3.EllipticWithSection.exists_supportProperty_charge` |
| The kernel root system: a reflection-closed set of `(-2)`-vectors of a symmetric form is a root pairing over any commutative ring (no finiteness, so the Mukai lattice is an instance), reduced over `ℤ`; on a negative-definite lattice it is finite and simply laced, and the Cartan matrix of a base is `Matrix.IsSimplyLaced` and positive definite; over `ℚ` it is a root system on the span of the roots; at a period `Z` with `B` negative on the lattice points of `ker Z` the roots `R_*` are finite and form the kernel root system of `ker Z ∩ N` | `RootPairing.pairingOfClosed`, `RootPairing.sphericalPairing`, `RootPairing.pairingOfClosed_isReduced`, `RootPairing.sphericalPairing_finite_isReduced_simplyLaced`, `RootPairing.cartanMatrix_isSimplyLaced`, `RootPairing.cartanMatrix_pos`, `RootPairing.latticeRootSystem_isRootSystem`, `RootPairing.finite_kernelRoots`, `RootPairing.kernelRootPairing_finite_isReduced_simplyLaced` |
| The stratum trichotomy in signature `(2, n)`: a positive period vanishes on a subspace iff it is negative definite, of dimension at most `n`; two independent roots meet in `P⁺` iff `\|⟨δ₁, δ₂⟩\| < 2`, at pairing `±2` the sum `δ₁ ± δ₂` is an isotropic radical and above it the span is indefinite | `Mukai.exists_posPlane_orthogonal_iff_negDef`, `Mukai.finrank_le_of_negDef`, `Mukai.negDef_span_pair_iff`, `Mukai.exists_posPlane_orthogonal_pair_iff`, `Mukai.isotropic_add_of_eq_two`, `Mukai.pos_add_of_two_lt` |
| The punctured support bound: at a charge `Z₀` with negative-definite kernel, `‖v‖ ≤ K \|Z(v)\|` on a ball of charges for every class of square at least `-2` off the roots of the kernel, and only those root hyperplanes meet the ball; the support property is its case with no kernel roots | `Mukai.exists_finsler_ball`, `Mukai.exists_punctured_supportBound`, `Mukai.exists_ball_ker_subset`, `Mukai.exists_supportProperty` |
| On the K3 surfaces of the library: the real Mukai form of the elliptic K3 has signature `(2, 2)`; its spherical pairing has infinitely many roots and is reduced; at the normalized charge with `β = -C/2` the roots of the kernel are `±v(𝒪_C)`, an `A₁` kernel root system, with the punctured support bound around it; the roots `𝒪_C`, `𝒪_C(-1)[1]` of the curve wall (pairing `2`) never meet in `P⁺`, the `A₂` pair `𝒪_X[1]`, `𝒪_C` does; in Picard rank one every stratum is `A₁` | `AlgebraicGeometry.K3.EllipticWithSection.sigPos_mukaiForm`, `AlgebraicGeometry.K3.EllipticWithSection.kernelRoots_stratumCharge`, `AlgebraicGeometry.K3.EllipticWithSection.exists_punctured_supportBound_stratumCharge`, `AlgebraicGeometry.K3.EllipticWithSection.not_exists_posPlane_wallA_wallB`, `AlgebraicGeometry.K3.EllipticWithSection.exists_posPlane_a2`, `AlgebraicGeometry.K3.PicardRankOne.eq_or_eq_neg_of_modelCharge_eq_zero` |
| Vectors of norm `-2` with pairings `e i j ∈ ℕ` under a symmetric form give the reflection representation `W(ofExt e) →* GL(Λ)` (for `Λ = ℤ^B` the geometric representation of the Weyl group of the generalized Cartan matrix `2 - e`), with `ρ_s ρ_t ρ_s = ρ_{ρ_s t}`; root-positive words (every prefix root a nonempty sum of simple roots); root-positivity transfers along any map matching the Gram matrices, and on `ℤ^B` it is a finite check. Tits' positivity theorem (reduced iff root-positive) is stated, not proved | `CoxeterMatrix.reflectionRep`, `BilinearForm.reflect_reflect_reflect`, `BilinearForm.IsRootPositive`, `BilinearForm.IsRootPositive.of_rootForm`, `CoxeterMatrix.isRootPositive_rootForm_iff`, `CoxeterMatrix.CoxeterPositivity` |
| A finite set mapped into itself by each `ρ(s_i)` except at one point bounds lengths from below: the number of its elements `ρ(w)` moves out is at most `ℓ(w)`. The word `[0] ++ [1, 0] ++ ⋯ ++ [n-1, …, 0]` has length `n(n+1)/2`; for `n ≤ 6` it is a reduced, root-positive word of `w₀` in `W(A_n)` with `w₀(α_i) = -α_{n-1-i}` (by computation) | `CoxeterSystem.inversionCount_le_length`, `CoxeterSystem.isReduced_of_length_le_inversionCount`, `CoxeterMatrix.longestWordA`, `CoxeterMatrix.isReduced_longestWordA`, `CoxeterMatrix.isRootPositive_longestWordA`, `CoxeterMatrix.stdWord_longestWordA` |
| The deletion argument for words of reflections: if each `ρ_i` maps `P ∖ {α_i}` into a set `P ∋ α_i`, a word whose last prefix root leaves `P` acts as a word two letters shorter; so a word with no shorter word of the same action keeps every prefix root in `P`, and if `P` has no pair `v, -v` a word keeping every `α_i` in `P` acts trivially. A statement about the action, not the abstract Coxeter group | `BilinearForm.exists_split_of_reflectWord_notMem`, `BilinearForm.exists_reflectWord_eq_of_notMem`, `BilinearForm.prefixRoots_mem_of_minimal`, `BilinearForm.reflectWord_eq_one_of_forall_mem`, `BilinearForm.exists_reflectWord_of_mem_closure` |
| Real roots of a loopless quiver on its root form `rootForm e`: the images of the simple roots under words of simple reflections, among them the prefix roots of every word, have norm `-2` (`q = 1`); the form is sign coherent (every vector of norm `-2` has coordinates of one sign) when the Tits form is positive semidefinite with isotropic vectors zero or of full support, as in finite and connected affine type; then, by descent on the height, every positive vector of norm `-2` is a real root, and a function invariant under the simple reflections between positive vectors takes there its value at a simple root | `CoxeterMatrix.IsRealRoot`, `CoxeterMatrix.IsRealRoot.rootForm_self`, `CoxeterMatrix.isRealRoot_of_mem_stdPrefixRoots`, `CoxeterMatrix.IsSignCoherent`, `CoxeterMatrix.isSignCoherent_of_posSemidef`, `CoxeterMatrix.exists_eq_stdRoot_of_reflect_invariant` |
| Integrality over `ℤ[1/N]`: the elements with `N ^ j x` an algebraic integer form a subalgebra, integrally closed in the ring and preserved by ring maps; a root of a monic polynomial with algebraic-integer coefficients is an algebraic integer; if `α ≠ 0` is a root of a monic `P ∈ ℤ[X]` irreducible over `ℚ` and `α⁻¹` is integral over `ℤ[1/N]`, then `P(0)` divides a power of `N`, with no number field; elements with the same minimal polynomial over `ℚ` have the same integral integer multiples | `integralClosureAway`, `mem_integralClosureAway_of_isIntegral`, `map_mem_integralClosureAway`, `Polynomial.Monic.isIntegral_of_isIntegral_coeff`, `coeff_zero_dvd_pow`, `isIntegral_mul_of_minpoly_eq` |
| Specialization: a finitely generated subring `R` of a field of characteristic zero has one `N > 0` such that every element algebraic over `ℚ` and integral over `R` is integral over `ℤ[1/N]`, from Zariski's lemma and lying over (no transcendence basis); for generators algebraic over `ℚ`, `N` is a common denominator | `exists_specialization`, `exists_specialization_of_isAlgebraic`, `adjoin_le_integralClosureAway` |
| Eigenvalues of a matrix are integral over the ring of its entries; with the entries of `M⁻¹` and `(M̄)⁻¹` in `R`, the inverse modulus `\|z\|⁻¹` of every eigenvalue is integral over `R`. The unit test: with the entries of `M` and `M⁻¹` algebraic integers, every eigenvalue modulus is an algebraic unit, so a real number whose inverse is not an algebraic integer is not the modulus of an eigenvalue of an integer matrix of determinant `±1` | `Matrix.isIntegral_of_mem_spectrum`, `Matrix.isIntegral_norm_inv_of_mem_spectrum`, `Matrix.isIntegral_norm_of_mem_spectrum_of_isIntegral`, `Matrix.isIntegral_norm_inv_of_mem_spectrum_of_isIntegral`, `Matrix.norm_ne_of_not_isIntegral_inv` |
| The S-unit theorem for spectral moduli: for finitely many invertible complex matrices there is `N > 0` such that whenever the modulus of an eigenvalue of a product is a root of a monic `P ∈ ℤ[X]` irreducible over `ℚ`, `P(0)` divides a power of `N`; only the inverse letters enter, and `N` may be any common denominator of their entries when these are integral over `ℤ[1/N]`; the family form | `Matrix.spectral_moduli_norms_divide_pow`, `Matrix.spectral_moduli_norms_divide_pow_of_mem`, `Matrix.no_invertible_family` |
| The singular reduction: if letters map to a group with an inverse-closed alphabet and `λ` on the group gives the spectral radius of every product, invertible letter matrices (on the image of a least-rank product representing the identity) give the same spectral radii; an endomorphism with range in `U` has the spectral radius of its restriction to `U`; a positive spectral radius is the modulus of an eigenvalue | `Matrix.singular_reduction`, `Module.End.spectralRadius_restrict`, `Matrix.exists_mem_spectrum_norm_eq` |
| The cubics `P_s = t³ - (65s - 8)t² - (9s - 8)t - (16s - 1)` of the double-plane block family: `P_s` is the characteristic polynomial of the integer pencil `M_s = M₁ + (s - 1) u vᵀ`, `det M_s = 16s - 1`, `tr M_s = 65s - 8`; for `s ≥ 1` it has exactly one real root, which is positive; it is irreducible over `ℚ` for every `s ≥ 1` (rational roots) and modulo `19` for `s ≡ 1 (mod 19)`; every prime `p ∉ {2, 19}` divides some `16s - 1` with `s ≡ 1 (mod 19)`; its roots are algebraic integers and not units | `Polynomial.DoublePlane.charpoly_blockMatrix`, `blockMatrix_eq`, `det_blockMatrix`, `trace_blockMatrix`, `pos_of_aeval_cubic`, `eq_of_aeval_cubic`, `exists_aeval_cubic_eq_zero`, `irreducible_cubic`, `irreducible_map_zmod_nineteen`, `irreducible_cubic_of_mod_nineteen`, `exists_dvd_of_prime`, `exists_prime_dvd_not_dvd`, `not_isIntegral_inv_of_aeval_cubic` |
| Monotone homogeneous maps of the orthant (Gaubert–Gunawardena, Trans. Amer. Math. Soc. 356 (2004)): closed under composition, maxima and minima, with nonnegative matrices as examples; `‖f^{m+n} 𝟙‖ ≤ ‖fᵐ 𝟙‖ ‖fⁿ 𝟙‖`, so the cycle time `R(f) = lim ‖fⁿ 𝟙‖^{1/n} = inf ‖fⁿ 𝟙‖^{1/n}` exists; starts with `c 𝟙 ≤ u ≤ C 𝟙` have rate `R(f)` and every `v ≥ 0` at most `R(f)`; a nonnegative sub-solution `c_{n+1} ≤ f(c_n)` satisfies `c_n ≤ fⁿ c_0`, also along a sequence of dominated maps | `MonotoneHomogeneous`, `cycleTime`, `MonotoneHomogeneous.norm_iterate_add_le`, `tendsto_cycleTime`, `cycleTime_le`, `tendsto_cycleTime_of_bounds`, `limsup_le_cycleTime`, `le_iterate_of_le`, `limsup_le_cycleTime_of_le`, `le_iterate_of_dominated` |
| Collatz–Wielandt for monotone homogeneous maps, both directions and no Brouwer: `x ≥ m > 0` with `f x ≤ s x` gives `‖fⁿ 𝟙‖ ≤ (‖x‖/m) sⁿ` and `R(f) ≤ s`; `0 ≤ v ≠ 0` with `t v ≤ f v` gives `t ≤ R(f)`; a positive eigenvector gives `R(f)`; the ratio test `min (f v)_i/v_i ≤ R(f) ≤ max (f v)_i/v_i`; for a nonnegative matrix `R = gelfandRadius` | `MonotoneHomogeneous.norm_iterate_one_le_of_le_smul`, `cycleTime_le_of_le_smul`, `le_cycleTime_of_smul_le`, `cycleTime_eq_of_eigenvector`, `cycleTime_mem_Icc_of_ratio`, `cycleTime_mem_Icc_inf_sup`, `cycleTime_mulVec` |
| Maximum operators: for finitely many self-maps of any type, `(Fμ)(x) = max_a μ(f_a x)` has `Fⁿμ(x) = max_{\|w\| = n} μ(f_w x)`; for nonnegative matrices `Φ(x) = max_a A_a x` is monotone homogeneous with `JSR ≤ R(Φ)`; for the letters `[[1, 2], [0, 1]]`, `[[1, 0], [2, 1]]` of a wall of two spheres pairing to two, `Φ = I + G` on the orthant with `R(Φ) = 3`, while `JSR = 1 + √2` | `iterate_maxOperator_apply`, `monotoneHomogeneous_maxMulVec`, `jointSpectralRadius_le_cycleTime_maxMulVec`, `maxMulVec_affine`, `cycleTime_maxMulVec_affine`, `jointSpectralRadius_affine`, `jointSpectralRadius_lt_cycleTime_affine` |
| Monotone homogeneous maps preserve parts of the orthant (vectors with one support) and do not increase the Thompson and Hilbert pseudometrics on them, nor on the open orthant (Bushell, Arch. Rational Mech. Anal. 52 (1973)) | `MonotoneHomogeneous.pos_iff_of_le_smul`, `thompsonEDist_map_le`, `hilbertEDist_map_le`, `thompsonEDist_map_le_of_pos`, `hilbertEDist_map_le_of_pos` |

## What is proved from stated inputs

`PointMassHypotheses` lists what the corollary uses about `D^b(X)`. Mathlib does not yet have derived categories of coherent sheaves on a K3 surface, Bridgeland stability or categorical entropy, so these are hypotheses (fields), each with its source in its docstring. It extends `MassComparisonHypotheses` (below) by the rank-one point fields:

- Serre duality `h(U, V) = h(V, U)`, invariance of total Hom under autoequivalences, additivity on `G = S₀ ⊕ S₁ ⊕ S₂`;
- the diagonal estimate `h(U, V) ≤ K h(U, G) h(G, V)` (Orlov, arXiv:0804.1163, Theorem 4, with regularity for `K`);
- the point test `h(E, 𝒪_x) = R(E)` and `ν R(E) ≤ h(E, G)` for spherical `E` (the article's point-measurement lemma);
- Lemma A.1 (for spherical `E`) and Lemma A.2 of the article;
- standard words: their powers are standard, they move points to shifted points, their `H_n` grows quadratically;
- a distance bound `m_σ ≤ e^{δ(σ, σ')} m_{σ'}` with `δ` at most Bridgeland's metric (arXiv:math/0212237, Proposition 8.1), the action on stability conditions, positive masses;
- the twist triangles of the summands `S_i` read through the mass (from Ikeda subadditivity, arXiv:1612.00995, Proposition 3.3), and the upper comparison `C₁ m_σ(U) ≤ m_σ(G) h(G, U)` (Ikeda, Proposition 3.4, with Dimitrov–Haiden–Katzarkov–Kontsevich, arXiv:1307.8418, eq. (9)).

The two-sided comparison `c h(G, V) ≤ m_τ(V) ≤ C h(G, V)` and the entropy `h_cat(Φ) = lim log h(G, Φⁿ G)/n` are not inputs: `C = m_τ(G)/C₁`, `c` comes from the twist triangles of the `S_i` (`PointMassHypotheses.hom_le_mass`), and the limit exists by Fekete's lemma (`PointMassHypotheses.hcat_spec`; by DHKK's Theorem 2.6 it is categorical entropy at `t = 0`).

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
| Where `φ(B) < φ(A)`: the HN filtration of `P` is `0 ⊂ A ⊂ P`, with the two simple factors `A`, `B`; at a curve wall, `𝒪_x` with `x ∈ C` has the two rigid factors `𝒪_C`, `𝒪_C(-1)[1]` | `PairingTwoWallHypotheses.hn_P_of_phase_gt` |
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

### The Mukai budget

`MukaiBudget` is a function `e` on the objects of a pretriangulated category with values in `ℕ`
(nonnegativity is part of the interface: an integer-valued `e` with the other fields can be the
constant `-1`), invariant under isomorphism, with Mukai's lemma `e(A) + e(B) ≤ e(D)` for every
distinguished triangle `A → D → B → A⟦1⟧` with `Hom(A, B) = 0` (Bayer–Bridgeland,
arXiv:1310.8266, Lemma 2.5). On a `k`-linear category, `e = dim Hom(E, E⟦1⟧)` is invariant under
isomorphism by a theorem, so `MukaiBudget.ofSelfExtDim` asks only for Mukai's lemma.
`TwoCYHypotheses` lists the 2-Calabi–Yau inputs for that `e`, with a class map `v : K₀ → Λ` and a
bilinear form `q` in Mukai's sign (`χ = -q ∘ v`, spherical classes of square `-2`):
Hom-finiteness, a Serre functor naturally isomorphic to `⟦2⟧` (Bondal–Kapranov; Huybrechts,
*Fourier–Mukai transforms in algebraic geometry*, Ch. 3), Mukai's lemma, evenness of `e` (Serre
duality and the even Mukai lattice), and Riemann–Roch `e = 2 + q(v, v)` for objects with `End = k`
and no negative self-extensions only (Mukai; Huybrechts, *op. cit.*, Ch. 10). From these:

| Assertion | Lean |
|---|---|
| **The Mukai budget lemma**: along every Postnikov tower whose triangles have no maps from sub to quotient, `∑ e(M_i) ≤ e(E)`; pairwise orthogonality of the factors gives that step condition, so the budget holds along every HN filtration of a phase predicate with Hom vanishing, at every slicing | `MukaiBudget.tower_sum_le`, `PostnikovTower.triangle_hom_eq_zero`, `MukaiBudget.hn_sum_le`, `MukaiBudget.slicing_sum_le` |
| At most `⌊e(E)/2⌋` factors have `e ≠ 0` if none has `e = 1`; for `e(E) = 2` every factor has `e ∈ {0, 2}` and at most one has `e = 2`; a rigid object has rigid factors; `e(0) = 0` | `MukaiBudget.card_nonrigid_le`, `e_factor_eq_zero_or_two`, `eq_of_e_factor_ne_zero`, `rigid_factors`, `e_zero` |
| For `e(E) = 2`, every HN filtration at every slicing has `e = 2` at most once and the other factors rigid, with no path, word, evenness or Picard rank; existence of the factor with `e = 2` is the vanishing of the defect `e(E) - ∑ e(M_i)`, which does not depend on the HN filtration with nonzero factors | `MukaiBudget.atMostOnce_e`, `exists_e_eq_two_iff`, `carriesOnce_e_iff`, `sum_e_eq_of_nonzero` |
| On a 2-Calabi–Yau category: `dim Hom(E, E⟦2⟧) = dim End(E)`; a simple isotropic object has `e = 2`; a spherical object has `v² = -2`; the at-most-once and zero-defect statements with no hypothesis on the factors | `TwoCYHypotheses.finrank_shift_two`, `selfExtDim_eq_two_of_isotropic`, `sq_classOf_eq_neg_two`, `atMostOnce_e`, `carriesOnce_e_iff` |

[K3TwistsTest/BudgetModel.lean](K3TwistsTest/BudgetModel.lean) checks consistency (`e = 0` on any
pretriangulated category; `TwoCYHypotheses` on a category of zero objects) and keeps two refuted
formulations as tests: an integer-valued budget without `e ≥ 0` (the constant `-1` breaks the
budget on the empty tower of `0`), and Riemann–Roch on all objects (false at `0`, where `e = 0` and
`v = 0`). Neither structure has an instance built from real objects: the library has no
2-Calabi–Yau triangulated category, so Mukai's lemma for triangles (and the Serre functor) cannot be
supplied. The real objects on which the budget is checked are the representations of the quiver
model, where Mukai's inequality, evenness and Riemann–Roch are theorems for extensions in the heart
of the wall (row "The Mukai budget lemma in the quiver model" above).
[K3TwistsTest/PairingTwoWallTowerModel.lean](K3TwistsTest/PairingTwoWallTowerModel.lean) shows that
existence is independent of the budget: a point with the two rigid HN factors of the curve wall
has `e = 2` at most once and no carrier.

### The tower theorem

`TowerHypotheses` (in `CategoryTheory.Triangulated`; the name under
`AlgebraicGeometry.K3.PicardRankOne` is a deprecated alias) lists what the tower theorem of the draft uses: `C` stands for `D^b(X)`, a
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
| With a Mukai budget for which point-like objects have `e = 2`: at every slicing, every HN filtration of every prefix has `e = 2` at most once, with no wall input; the tower theorem gives zero defect at `σ`; and given the pointwise links between carriers, spheres and `e` (Bayer–Bridgeland, arXiv:1310.8266, Lemma 2.6 for rigid objects), the conclusion at `σ` is equivalent to the existence of a carrier | `TowerHypotheses.atMostOnce_word`, `sum_e_eq_two`, `carriesOnce_target_iff` |

[K3TwistsTest/HNTowerModel.lean](K3TwistsTest/HNTowerModel.lean) builds an instance from any slicing
with a nonzero semistable object (the empty word, no walls); it shows the fields are consistent
relative to such a slicing, which Mathlib cannot yet construct.

### The split tower theorem

`SplitTowerHypotheses` states the tower theorem as the Mukai budget plus transport of a carrier,
step by step. The objects and letters are those of `TowerHypotheses`; the wall inputs are replaced
by a Mukai budget, four slice fields linking the carrier predicates to `e` for semistable objects
(no budget `1`; rigid implies spherical, Bayer–Bridgeland, arXiv:1310.8266, Lemma 2.6; a carrier is
not spherical; a semistable object with `e = 2` is a carrier or spherical), and paths of transport
steps (`CarrierStep`, `CarrierPath`). A step carries, for each phase, a matrix standing for the Gram
matrix of the stable spheres of that phase, and the field that a lost carrier forces an isotropic
sum with natural coefficients in one phase; the anisotropy of every step is a field. **Transport is
assumed per step**: with free Gram matrices an anisotropic step exists exactly when carriers are
transported. What drops out is the octahedral proof of transport: `IsTriangulated`, wall slicings,
outgoing flags, the sphericity of letters and uniqueness of HN filtrations. The slice fields are
used, not needed: they hold for the budget predicates `e = 2`, `e = 0`. `TowerHypotheses` and its
theorem are kept as they are.

| Assertion | Lean |
|---|---|
| For `e(E) = 2`, at every slicing every HN filtration of `E` has at most one carrier factor and its other factors spherical; then carrying the point once is existence of a carrier | `SliceFields.atMostOnce`, `SliceFields.carriesOnce_iff_hasCarrier` |
| An anisotropic step or path keeps a carrier; an anisotropic step exists iff carriers are transported | `CarrierStep.keep`, `CarrierPath.keep`, `CarrierStep.exists_anisotropic_iff` |
| **The split tower theorem**: at the target exactly one HN factor of `W 𝒪_x` carries the point, once, and every other factor is spherical; with uniqueness of HN filtrations, the same for every HN filtration with nonzero factors | `SplitTowerHypotheses.tower`, `SplitTowerHypotheses.tower_forall` |
| At a slicing where `E` carries the point once, the outgoing factors of a non-carrier factor are rigid, spherical and not carriers (not their nonzero-ness, nor the existence and ordering of outgoing flags); at most once holds at a wall with no incoming hypothesis | `outgoing_noncarrier`, `wall_atMostOnce` |
| `TowerHypotheses`, with a budget, the slice fields, `e(𝒪_x) = 2` and `e` invariant under the letters, give `SplitTowerHypotheses` with empty Gram matrices (the old `final_target` becomes the last step), and the two theorems agree | `SplitTowerHypotheses.ofTowerHypotheses`, `SplitTowerHypotheses.tower_ofTowerHypotheses` |

[K3TwistsTest/SplitTowerModel.lean](K3TwistsTest/SplitTowerModel.lean) builds an instance with
`e(𝒪_x) = 2` from a slicing with a nonzero semistable object and a budget of value `2` on it with no
semistable object of budget `1` (on a 2-Calabi–Yau category, from Riemann–Roch for a simple object
of isotropic class), and keeps the vacuity statements as tests: a step with free Gram matrices
exists between any two slicings.

### A lost carrier forces an isotropic sphere sum

`WallStep` ties a transport step to a named wall: a pre-stability condition with class map `v` to a
lattice with the Mukai pairing `q`. For each phase `φ` the **sphere types** are the isomorphism
classes of objects stable of phase `φ` at the wall and rigid (spherical, Bayer–Bridgeland,
arXiv:1310.8266, Lemma 2.6), and the Gram matrix is `q(v(Sᵢ), v(Sⱼ))`: both are definitions. The
inputs are fields, each with its source: stable objects of each phase (Bridgeland,
arXiv:math/0212237, Lemma 5.2); Jordan–Hölder constituents whose classes add up (ibid., Lemma 4.5);
semicontinuity of constituents, which gives the isotropic stable constituent of a carrier as a
semistable object of the wall (ibid., §9; Bayer–Bridgeland, Lemma 2.7, Remark 2.8); and the draft's
two-extension lemma (a non-rigid constituent keeps the carrier on the outgoing side). None has an
instance from real objects: the library has no 2-Calabi–Yau triangulated category of a K3 surface.

| Assertion | Lean |
|---|---|
| A nonzero semistable object has nonzero class, and two of one phase do not have opposite classes | `PreStabilityCondition.WithClassMap.classOf_ne_zero`, `classOf_ne_neg` |
| **A lost carrier forces an isotropic sphere sum at one phase**: if `e(E) = 2`, `E` has a carrier at `t₁` and none at `t₂`, the isotropic constituent of its carrier is semistable of some phase `ψ` of the wall with only spherical constituents there, and a nonzero `a ∈ ℕ^{types}` has `aᵀ·gram ψ·a = 0`; per phase, with natural coefficients, and with no assumption on the number of spheres of a phase | `WallStep.exists_isotropic_of_lost`, `WallStep.lost_isotropic`, `WallStep.exists_nonrigid_constituent` |
| So a wall is a transport step with these Gram matrices, an anisotropic wall keeps a carrier, and the split tower theorem holds over paths of anisotropic named walls | `WallStep.toCarrierStep`, `WallStep.keep`, `WallTowerHypotheses.tower` |
| The lattice core: one sphere has no isotropic sum; two spheres of pairing `g` have one iff `g = 2`; an isotropic nonzero class that is a sum of constituent classes, with anisotropic spherical part, has a non-spherical constituent | `Matrix.noIsotropic_one`, `Matrix.isotropicSphereSum_two_iff`, `Matrix.noIsotropic_two`, `Matrix.isotropic_two`, `BilinearForm.exists_nonspherical_constituent`, `BilinearForm.isotropicSphereSum_gram_of_list` |
| **Picard rank one**: two roots of pairing `2` are opposite; with at most two sphere types per phase (Bayer–Bridgeland, Lemma 3.3 and Proposition 3.4) and Riemann–Roch for stable rigid objects, every wall is anisotropic, and the tower theorem follows through the split tower theorem with the Gram matrices of the walls | `MukaiVector.eq_neg_of_pairing_eq_two`, `RankOneWall.anisotropic`, `WallTowerHypotheses.tower_of_rankOne` |
| The wall of `𝒪_X` and `𝒪_X(-H)[1]` has Gram matrix `[[-2, d + 2], [d + 2, -2]]` and no isotropic sphere sum | `gram_structureSheaf_shift`, `WallStep.anisotropic_of_structureSheaf_shift` |

[K3TwistsTest/WallStepModel.lean](K3TwistsTest/WallStepModel.lean) computes the pairing-two wall of
`𝒪_C`, `𝒪_C(-1)[1]` on the elliptic K3 surface with a section: its Gram matrix is
`[[-2, 2], [2, -2]]`, `(1, 1)` is isotropic with class `v(𝒪_x)`, and where a point loses its carrier
(`PairingTwoWallTowerModel`) `WallStep.lost_isotropic` places the loss at an isotropic phase. It
keeps the per-phase and natural-coefficient regression tests, and builds consistency models of
`WallStep` (a step that crosses no wall) and `WallTowerHypotheses` relative to a slicing with a
nonzero semistable object, which Mathlib cannot yet construct.

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

### The stability-space interface

`StabilitySpaceHypotheses` is a metric space `Stab` of prestability conditions on
`C` with a class map, and a group acting through exact autoequivalences, with the facts about
Bridgeland's space as fields: the map to central charges is a covering onto its image
(Bridgeland, arXiv:math/0212237, Theorem 1.2; arXiv:math/0307164, Theorem 1.1 for K3 surfaces);
phases and masses move by at most the distance (Bridgeland, arXiv:math/0212237, §8); the support
property (Kontsevich–Soibelman, arXiv:0811.2435, §1.2); `Z_{gσ}(Φ_g E) = Z_σ(E)`; and Ikeda
subadditivity `m(B) ≤ m(A) + m(C)` on triangles (Ikeda, arXiv:1612.00995, Proposition 3.3).

| Assertion | Lean |
|---|---|
| `m_{gσ}(Φ_g E) = m_σ(E)` | `StabilitySpaceHypotheses.mass_smul` |
| The path layer: a path `[0, 1] → Stab` subdivides into steps with `ε`-close slicings, for any `ε > 0` | `StabilitySpaceHypotheses.exists_subdivision_phaseClose`, `phaseClose_of_dist_lt` |
| Exponential mass growth of any sequence of objects does not depend on the stability condition | `StabilitySpaceHypotheses.tendsto_log_mass_div_iff` |
| The `2m(D)` lemma at every point | `StabilitySpaceHypotheses.abs_sub_mass_cone_le` |

No field has an instance from real objects: Mathlib has no triangulated category with a slicing,
and the missing input is `D^b(X)` of a K3 surface with `Stab†(X)`.
[K3TwistsTest/StabilitySpaceModel.lean](K3TwistsTest/StabilitySpaceModel.lean) builds the
interface on the one-point space at a prestability condition with injective charge and Ikeda
subadditivity.

### Twist systems and the exponent of the centre counts

`HomTwistSystem₀` is a group acting on objects with centres `S_i`, letters `T_a` with centres
`S_{c(a)}`, and a count `h(U, V) ∈ ℕ` (intended: `dim Ext^*(U, V)`), with two fields: invariance
`h(gU, gV) = h(U, V)` and the one-letter bound `h(U, T_a V) ≤ h(U, V) + h(U, S) h(S, V)` from the
twist triangle (Seidel–Thomas, arXiv:math/0001043). `HomTwistSystem` adds `T_S S = S[-1]` read
through `h`. The exponent theorem also takes the lower bound
`h(U, S) h(S, V) ≤ h(U, V) + h(U, T_a V)`, sphericity `h(S_i, S_i) = 2` and directed
connectivity as named hypotheses; it uses neither `T_S S = S[-1]` nor symmetry of `h`, nor any
category, stability condition or K3 surface.

| Assertion | Lean |
|---|---|
| The domination recursion with constant one: tests of `W S_j` are bounded by the column `P_W e_j` of the product of transvections `1 + e_{c(a)} G_a` | `DominationSystem.test_word_le`, `DominationSystem.step_eq_mulVec`, `HomTwistSystem.toDomination`, `HomTwistSystem₀.toDomination0` |
| For `P_q = max h(S_i, W S_j)` over `\|W\| ≤ q`: `log P_N / N → η`, with `log(P_q/2^{d+1})/(q + d + 1) ≤ η ≤ log(1 + q P_q)/q`, and `η ≥ 0` | `HomTwistSystem₀.tendsto_homExponent`, `homExponent_lower`, `homExponent_upper`, `homExponent_nonneg` |
| `P_{q+1} ≤ (1 + g) P_q`, `g = max h(S_i, S_k)`, so the two certificates differ by at most `log(q + 1)/q + (d + 1)/(q + d + 1)(log(1 + g) + log g/q + log 2)` | `HomTwistSystem₀.maxCount_succ_le`, `homExponent_width` |
| A map of twist systems matching centres and letters and preserving counts preserves every `P_q` and `η` | `HomTwistSystem₀.maxCount_eq_of_map`, `homExponent_eq_of_map` |
| The same on the orbit of the centres: a map matching centres, intertwining the letters on the objects `W S_j` and preserving the counts from the centres to them preserves every `P_q` and `η` | `HomTwistSystem₀.maxCount_eq_of_map_orbit`, `homExponent_eq_of_map_orbit` |
| The bipartite bound: if the centres are two-coloured with `h(S_i, S_k) = 0` within a colour and `h(S_i, S_k) ≤ s` for distinct centres, `s ≥ 1`, then `P_q ≤ C R^q` for every `R > ρ_s` and `e^η ≤ ρ_s = (s + √(s² + 4))/2`; the domination recursion is a product of single twists of the coupling graph | `HomTwistSystem.exists_maxCount_le_of_bipartite`, `exp_homExponent_le_of_bipartite`, `HomTwistSystem.cast_dom` |
| Inverse letters: the bounds for `T_a⁻¹` from symmetry of `h` | `HomTwistSystem₀.upper_inv`, `lower_inv`, `withInverses` |

The real-object instance is `eulerTwistSystem`: on a K3 surface with `Pic X = ℤH`, `H² = 2d`,
the classes `v(𝒪_X)`, `v(𝒪_X(H))` in the Mukai lattice, the reflections by which the two twists
act, the isometry group, and the count `|χ(U, V)| = |⟨v(U), v(V)⟩|`, which equals the total
`Ext` dimension at the centres. Every field and every hypothesis of the theorem is proved for
it, and its exponent is positive, `η ≥ log(7/4)/3` (`eulerTwistSystem_homExponent_pos`). The
same theorem for the total `Ext` dimensions of the objects `W S_j` needs `D^b(X)` and the twist
functors. [K3TwistsTest/TwistSystemModel.lean](K3TwistsTest/TwistSystemModel.lean) shows that
the zero count satisfies every other input but not sphericity, and that the bound for inverse
letters does not follow without symmetry.
[K3TwistsTest/DominationSystemModel.lean](K3TwistsTest/DominationSystemModel.lean) builds a
domination system on count vectors with linear tests, in which the bound on centres is an
equality, and [K3TwistsTest/GrowthBoundModel.lean](K3TwistsTest/GrowthBoundModel.lean) runs the
bipartite bound (`d + 1 ≤ e^η ≤ ρ_{d+2}` for `eulerTwistSystem`), the fixed-word formula and the
bipartite joint spectral radius (the golden ratio for `D₄`) on the instances of the library.

### The mass comparison and Theorem C

`MassComparisonHypotheses` adds masses to the twist-system layer: objects with a group of
autoequivalences acting on them and on the points of a space of stability conditions, total Hom
`h`, masses `m_σ` with a distance bound `m_σ ≤ e^{δ(σ, σ')} m_{σ'}` (`δ ≥ 0` symmetric; Bridgeland's
metric is one), a split generator `G = ⊕ S_k` with spherical summands, the twist `T_E` along a
spherical `E` with the conjugation formula `T_{gE} = g T_E g⁻¹` (Seidel–Thomas,
arXiv:math/0001043, Lemma 2.11) and `T_E V = V` when `h(E, V) = 0`; the mass forms of the
twist-triangle bounds `m(T_E V) ≤ m(V) + h(E, V) m(E)` (and for `T_E⁻¹`) and
`h(E, V) m(E) ≤ m(V) + m(T_E V)` (Ikeda subadditivity, arXiv:1612.00995, Proposition 3.3); the
diagonal estimate (Orlov, arXiv:0804.1163, Theorem 4); and the upper comparison
`C₁ m_σ(U) ≤ m_σ(G) h(G, U)` as the single field `dhkk_comparison` (Ikeda, Proposition 3.4, with
Dimitrov–Haiden–Katzarkov–Kontsevich, arXiv:1307.8418, eq. (9)).

| Assertion | Lean |
|---|---|
| The lower comparison `h(G, V) ≤ L_σ m_σ(V)` from the twist triangles of the summands, and `h(U, V) ≤ K h(U, G) L_σ m_σ(V)` for every `U` | `MassComparisonHypotheses.hom_G_le_mul_mass`, `hom_le_mul_mass` |
| The uniform estimate `e^{-δ(σ,τ)} h(G, V) ≤ L_τ m_σ(V)` and `m_σ(V) ≤ e^{δ(σ,τ)} (m_τ(G)/C₁) h(G, V)`, for any distance bound | `MassComparisonHypotheses.uniform_estimate` |
| Categorical entropy `lim log h(G, Φⁿ G)/n` exists, `h_cat(Φ⁻¹) = h_cat(Φ)`; twists at Ext-orthogonal spherical objects commute | `MassComparisonHypotheses.tendsto_hcat`, `hcat_inv`, `twist_commute` |
| The masses form a domination system, with tests `m_σ` pulled back by `σ ↦ T_a⁻¹ σ` | `MassComparisonHypotheses.IsTwistSystem.toDomination` |
| **The twist-system exponent theorem in mass form**: `log max_{\|W\| ≤ N, j} m_σ(W S_j) / N → η`, the exponent of the centre counts, at every `σ` | `MassComparisonHypotheses.IsTwistSystem.tendsto_log_massMax` |
| σ-independence of exponential mass growth along any sequence of objects, and of `M_n(E) = max_{\|W\| = n} m_σ(W E)` | `MassDistanceBound.tendsto_log_mass_div_iff`, `MassComparisonHypotheses.tendsto_log_lenMax_iff` |
| The component decomposition: if the components of the centres are Ext-orthogonal, `h(S_b, W E) = h(S_b, W_B E)` for the subword `W_B` of the component of `b` | `MassComparisonHypotheses.IsTwistSystem.hom_word_eq_hom_filter`, `List.prod_map_eq_filter_mul_filter` |
| **Theorem C**: with an inverse-closed alphabet and Ext-orthogonal components each connected, `log M_n(E)/n → max({0} ∪ {η_B : B meets E})` for every `E ≠ 0` | `MassComparisonHypotheses.IsTwistSystem.tendsto_log_lenMax` |
| **The fixed-word formula**: for a word `W` and `m_σ(E) > 0`, `limsup m_σ(Wⁿ E)^{1/n} = max(1, limsup d(Wⁿ E)^{1/n})` with `d(Y) = max_i h(S_i, Y)`: a letter adds at most `h(S_{c(a)}, Y) m_σ(S_{c(a)})` to the mass and multiplies `d` by at most `1 + g`, `d ≤ A_σ m_σ`, and the letters fix `Y` once `d(Y) = 0` | `MassComparisonHypotheses.IsTwistSystem.limsup_mass_pow`, `mass_word_pow_le`, `centreCount_le_mul_mass`, `word_smul_eq_of_centreCount_eq_zero` |
| The envelope over any monoid: `μ₀ = sup_k e^{-ηk} M_k` dominates `m`, is a sub-eigenfunction and is subadditive on relations invariant under the whole monoid, given `BddAbove (e^{-ηk} M_k(P))`; a comparable sub-eigenfunction bounds `M_k` | `Monoid.le_extremal`, `extremal_smul_le`, `extremal_tri`, `lenMax_le_of_subeigen` |
| The periodic witness: two letters with `M = h(S, B) ≥ 2` give `h(B, (T_S T_B)ⁿ S) ≥ M (M - 1)^{2n}`, so `η ≥ log(M - 1)`; for `𝒪_X`, `𝒪_X(H)` read through `\|χ\|`, `η ≥ log(d + 1)` | `HomTwistSystem₀.theta_le_count`, `log_sub_one_le_homExponent`, `eulerTwistSystem_log_le_homExponent` |

The instance from the library's objects is `eulerMass`, at the level of classes: formal direct sums of Mukai
vectors of a K3 surface of Picard rank one, the isometry group, reflections as twists,
`G = 𝒪_X ⊕ 𝒪_X(H) ⊕ 𝒪_X(2H)`, the count `Σ |χ|` and the mass `m_g = h(gG, -)` of the moved
generator. Every field is proved there, the diagonal estimate with `K = 21`
(`abs_pairing_le`); Theorem C then gives the point class an exact rate `η ≥ log(d + 1)`
(`eulerClass_exists_tendsto_log_lenMax`). The fields `hom`, `mass` and `twist` have no geometric
instance: the Ext counts, Bridgeland masses and twist functors need `D^b(X)`.
[K3TwistsTest/MassComparisonModel.lean](K3TwistsTest/MassComparisonModel.lean) runs the theorems
on both models.

### Count cocycles: the growth sandwich and the squeeze

`CountCocycleHypotheses` packages counts `c(Y) ≥ 0` and signed vectors `v(Y)` with `|v| ≤ c`
entrywise, nonnegative count matrices `P_a` dominating the counts, `c(T_a Y) ≤ P_a c(Y)`, and
matrices `E_a` carrying the signed vectors, `v(T_a Y) = E_a v(Y)`. Sign coherence (a diagonal of
signs with `D E_a D = P_a`) and tightness (`v(Y) = D c(Y)`) are named hypotheses, not fields.

| Assertion | Lean |
|---|---|
| The squeeze, in any partial order with a modulus and a sign map: along a tight orbit every domination is an equality; the intertwining is needed only along the orbit, and in its all-`x` form it forces the count map to be additive when the signed maps are; the flag form | `Order.squeeze_orbit`, `Order.squeeze`, `Order.map_add_of_intertwine`, `Order.squeeze_flag` |
| The sign rule: `D E_i(e) D = P_i(e)` iff `-e d_i d_b K_{ib} = \|e\| G_{ib}`, for letters and words; with the parity-graded form (`K` skew, zero diagonal) adjacent letters have opposite signs, and a 2-colouring gives `D = 1`; `\|K\| ≤ G` gives `\|E_W\| ≤ P_W` for every word | `Matrix.signRule_letter`, `signRule_word`, `signRule_opposite`, `signRule_canonical`, `abs_signedWord_le` |
| The growth sandwich for a word `W`: `‖c(Wⁿ Y)‖ ≤ K rⁿ` for `r > ρ(P_W)`; `‖c(Wⁿ Y)‖ ≥ rⁿ` eventually for `r < ρ(E_W)` when the seed meets the top of the spectrum of `E_W`; `ρ(E_W) ≤ ρ(P_W)` when `\|E_a\| ≤ P_a` | `CountCocycleHypotheses.norm_count_pow_le`, `eventually_pow_le_norm_count`, `gelfandRadius_signedWord_le` |
| Under sign coherence, tight orbits have exact counts `c(W Y) = P_W c(Y)`, and a tight seed with counts bounded below grows at `ρ(P_W) = ρ(E_W)`, the complex spectral radius, with no Perron–Frobenius | `CountCocycleHypotheses.tight_word`, `tendsto_tight` |

The real-object instance is `eulerCountCocycle`: the Euler pairings `⟨v(S_i), Y⟩` of a class with
`v(𝒪_X)`, `v(𝒪_X(H))` and their absolute values, under the two twists; the sandwich holds for
every word. The sign rule fails for it with every sign diagonal
(`eulerCountCocycle_not_signCoherent`): the Euler form of a 2-Calabi–Yau category is symmetric
with `⟨S, S⟩ = -2`, while the squeeze needs the parity-graded form, an auxiliary `ℤ/2`-grading
that real classes do not carry. [K3TwistsTest/CountCocycleModel.lean](K3TwistsTest/CountCocycleModel.lean)
gives a sign-coherent model (the Kronecker wall in its canonical orientation), and
[K3TwistsTest/SignRuleModel.lean](K3TwistsTest/SignRuleModel.lean) checks that the symmetric form
defeats every sign diagonal and forces equal signs on adjacent letters.
### Braid relations from one conjugation condition
`TwistConjugation` is the conjugation formula for spherical twists, as a map `τ : C → AutQuot C`
sending an object to the class of its twist:
- `τ` depends only on the object up to isomorphism and shift, `T_{S[n]} = T_S`;
- `τ(Φ S) = [Φ] τ(S) [Φ]⁻¹` for every exact autoequivalence `Φ` and spherical `S`, that is
  `T_{Φ S} ≅ Φ T_S Φ⁻¹` (Seidel–Thomas, arXiv:math/0001043, Lemma 2.11).
These fields hold for `τ ≡ 1`, so the content sits in a `TwistConjugation.Configuration` of a
Coxeter matrix `M`: spherical objects `x_i`, autoequivalences `T_i` with the link `[T_i] = τ(x_i)`,
and one object identity per edge, `T_i x_{i'} ≅ x_{i'}[n]` for `m = 2` and `T_{i'} T_i x_{i'} ≅ x_i[n]`
for `m = 3` (in either orientation; `m = ∞` asks for nothing). No pairwise braid isomorphism is
assumed. From these, for every Coxeter matrix at once:
| The twists satisfy the braid relations of `M`, so `σ_i ↦ [T_i]` is a homomorphism `Art(M) →* AutQuot C` | `TwistConjugation.Configuration.isBraidLiftable`, `TwistConjugation.toAutQuot` |
| Two signed words with the same image in `Art(M)` act equally on slicings and carry HN filtrations to each other, with the same phases and isomorphic factors | `TwistConjugation.nonempty_iso_of_eq`, `TwistConjugation.hn_of_eq` |
| Twists commute when `T_X Y ≅ Y[n]` | `TwistConjugation.commute_of_iso` |
| Any action in which the twists act as involutions, the action on the Mukai lattice included, factors through the Coxeter group `W(M)`; so it sees no element of the pure Artin group | `TwistConjugation.exists_factor`, `TwistConjugation.toAutQuot_eq_one_of_mem_pureArtinGroup` |
[K3TwistsTest/ArtinModel.lean](K3TwistsTest/ArtinModel.lean) gives the model `τ ≡ 1`, with the
identity autoequivalences at one object as a configuration for every Coxeter matrix, in which the
whole Artin group acts trivially. Mathlib has no spherical twist functor (it needs functorial
cones, from a dg or Fourier–Mukai enhancement), so no configuration of real twists is built. Its
image on classes is: on an elliptic K3 surface with a section, `𝒪_X[1]` and `𝒪_C` form an `A₂`
configuration, with edge identity `T_{𝒪_C} T_{𝒪_X} 𝒪_C ≅ 𝒪_X[1]`; on the Mukai lattice the
reflections satisfy the same equivariant criterion and this identity, and `Art(A₂)` acts through
`W(A₂) = S₃` (table of the elliptic surface below). The configurations of Picard rank one and the
two simples of a wall of pairing two all have `m = ∞`, with no edge identity to check.

### Central annihilators along twist words

`CentralAnnihilatorHypotheses` lists the inputs of the annihilator obstruction: a central element
`z`, letters that commute with it, a seed killed by `z` and a target not killed by `z`. The field
`letter_commutes` is the linearity criterion: for a twist at a centre `S`, `z_S = 0` and
`Ext^{-1}(S, S) = 0` make `T_S^{±1}` commute with `z`. Its argument goes through the twist kernel,
the cone of `S^∨ ⊠ S → 𝒪_Δ` (Seidel–Thomas, arXiv:math/0001043, §2), so it needs functorial cones;
on objects, two completions of the same morphism of evaluation triangles need not agree. From the
fields:

| Assertion | Lean |
|---|---|
| For every word, every slicing and every HN filtration of the word applied to the seed, the target is not a retract (direct summand) of any factor, nor isomorphic to one | `CentralAnnihilatorHypotheses.not_retract_factor`, `not_iso_factor`, `app_word_seed` |

The instance from real objects is `CentralAnnihilatorHypotheses.ofLinear`: the derived category
of `R`-modules, `z` the multiplication by `t ∈ R`, any `R`-linear letters, a seed module killed by
`t` and a target module not killed by `t`, in degree zero;
[K3TwistsTest/CentralActionModel.lean](K3TwistsTest/CentralActionModel.lean) runs it with the
shifts, `R/(t)` and `R`. The geometric instance, `Ô_{Y,y}` acting on the complexes supported on
the exceptional locus of a contraction with the fibre twists as letters, `𝒪_x` as the seed and
the curve with an embedded point `M_{d,x}` as the target (for `x` on a multiplicity-one component
of the fundamental cycle and on no other curve), has no Lean instance: Mathlib has no derived
category of coherent sheaves on a surface and no twist functors.
### Window dévissage into a heart
`AbelianHeartHypotheses ι` lists what the abelian corollary of window dévissage uses about a fully
faithful additive functor `ι : H ⥤ D` from an abelian category: its essential image is closed under
extensions, short exact sequences of `H` extend to distinguished triangles, and distinguished
triangles with vertices in the image come from short exact sequences. Every heart of a t-structure
has these properties (Beilinson–Bernstein–Deligne, *Faisceaux pervers*, 1.2.5–1.2.6, 1.3.6), but
Mathlib does not yet prove hearts abelian. They are proved for the standard heart
`singleFunctor C 0 : C ⥤ D(C)` of the derived category of an abelian category
(`DerivedCategory.abelianHeartHypotheses_singleFunctor`). From the fields:
| If every object of a family is the image of a simple object of `H`, the objects whose image is in the extension closure of the family form a Serre class of `H`; for a triangulated functor with window data `a ≤ 2`, `1 ≤ b` on a family with simple images, the essential image of its extension closure is a Serre class | `AbelianHeartHypotheses.isSerreClass_extensionClosure`, `AbelianHeartHypotheses.isSerreClass_image` |
| Admissible subobjects of `X` in the extension closure (first maps of distinguished triangles with outer terms in it) go to subobjects of `F X` in `H`, and with window data `a ≤ 0`, `1 ≤ b` every subobject of `F X` arises so; this is the target heart, not a source heart (`RΓ : D^b(ℙ¹) → D^b(vect)` with the family `{𝒪}`) | `AbelianHeartHypotheses.mono_of_distinguished`, `AbelianHeartHypotheses.exists_distinguished_of_mono` |
[K3TwistsTest/ExtComparisonModel.lean](K3TwistsTest/ExtComparisonModel.lean) applies window
dévissage to the identity functor of any pretriangulated category, to one object `S` with no
shifted self-morphisms in nonzero degrees (the model `vect → ⟨S⟩`, `V ↦ V ⊗ S`, checked on its
hypotheses: Mathlib cannot build that functor), and the abelian corollary to the standard heart of
`D(C)`.
### Weyl-indexed galleries of tilts
`WeylGalleryHypotheses` takes a t-structure with heart `A`, a `TwistConjugation.Configuration`
of spherical objects `S_i` that are simple in `A`, and:
- the sign of the class: a class map, additive on triangles, on which `T_i` acts by the
  reflection in `cl(S_i)`, and a cone containing the classes of the nonzero objects of `A` and no
  pair `v, -v`;
- the simple tilt `T_i A = ⟨S_i^⊥ ∩ A, S_i[-1]⟩` (the `2`-Calabi–Yau case, `T_S S ≅ S[-1]`);
- tilt composition: tilting the lower tilt at a torsion class `T` at a simple object `X` of
  `T^⊥ ∩ A` is the lower tilt at `Filt(T ∪ {X})` (hearts between `A[-1]` and `A` are tilts of
  `A`: Happel–Reiten–Smalø; Woolf, arXiv:0909.0552);
- `C` Serre in `A`: objects of `A` in the thick subcategory of the `S_i` are filtered by them.
Tilts are properties of objects (`WeylGallery.lowerTilt`), with no claim that they are hearts.
For `F_ω = T_{i₁} ⋯ T_{i_k}` and `T_ω = A ∩ F_ω A[1]`, by one induction on root-positive words:
| Statement | Lean |
| `T_ω` is a torsion class of `A` and `F_ω A = ⟨T_ω^⊥ ∩ A, T_ω[-1]⟩` | `WeylGalleryHypotheses.isTorsionClass_torsionOf`, `WeylGalleryHypotheses.heartOf_eq_lowerTilt` |
| If `ω i` is root-positive, `F_ω S_i` is simple in `F_ω A`, of class `ω(α_i) > 0`, lies in `A ∩ T_ω^⊥`, and `T_{ω i} = Filt(T_ω ∪ {F_ω S_i})` | `WeylGalleryHypotheses.F_obj_mem`, `WeylGalleryHypotheses.torsionOf_append_singleton` |
| With linearly independent classes: `T_i S_i ≅ S_i[-1]`, and `F_{u i} S_i ≅ S_j[-1]` when `u(α_i) = α_j`; at the reduced words of `w₀` ending in each letter, `F_{w₀} S_i ≅ S_{π i}[-1]` | `WeylGalleryHypotheses.twist_obj_self`, `WeylGalleryHypotheses.F_obj_iso_shift`, `WeylGalleryHypotheses.longest_obj_iso_shift` |
| The Garside bound: a concatenation of `m` root-positive words sends `A` into the window `[A[-m], A]`, so `A[-(k+m)] ≤ Δ^k x₁ ⋯ x_m A ≤ A` | `WeylGalleryHypotheses.heartOf_flatten_le_window` |
| The left edge as the dual theorem: `A` is the lower tilt of `F_ω⁻¹ A` at `F_ω⁻¹ T_ω` | `WeylGalleryHypotheses.heart_eq_lowerTilt_image_symm` |
| Words with the same Artin image give the same heart; each step is the twist along the new simple object, `τ(F_ω S_i) = [F_{ω i}] [F_ω]⁻¹` | `WeylGalleryHypotheses.heartOf_eq_of_eq`, `WeylGalleryHypotheses.twist_F_obj`, `WeylGalleryHypotheses.image_heartOf_of_twist` |
| At the heart `P((a, a+1])` of a slicing: `IsSimpleIn` the heart is simplicity in the abelian heart; for `θ ≤ a + 1` the phase cut `P((θ, a+1])` is a torsion class; for `a ≤ θ ≤ a + 1` the lower tilt at it is `P((θ-1, θ])` | `TStructure.isSimpleIn_heart_iff`, `Slicing.isSimpleIn_heartProp_iff`, `Slicing.isTorsionClass_heartProp_inf_gtProp`, `Slicing.lowerTilt_heartProp` |
| The instance at `P((0, 1])`: a prestability condition gives the t-structure, the class map and the sign of the class (`Im Z > 0`, or `Im Z = 0` and `Re Z < 0`, a cone with no pair `x, -x` holding every nonzero class of `P((0, 1])`), and simple objects of the abelian `P((0, 1])` are simple in `A`; a gallery heart whose torsion class is `P((θ, 1])` is `P((θ-1, θ])` | `WeylGalleryHypotheses.ofWithClassMap`, `PreStabilityCondition.WithClassMap.chargeCone`, `WithClassMap.classOf_mem_chargeCone`, `WeylGalleryHypotheses.heartOf_eq_heartProp` |
[K3TwistsTest/WeylGalleryModel.lean](K3TwistsTest/WeylGalleryModel.lean) gives a consistency model
with no simple objects and checks that non-reduced words are not root-positive. No instance comes
from geometry: the twists, the simple tilt and tilt composition need the derived category of a K3
surface with twist functors and tilts of its hearts. The class-level inputs are instantiated on
the `A₂` configuration `𝒪_X[1]`, `𝒪_C` of an elliptic K3 surface (table below).
At an ADE contraction the class-level inputs hold for every connected exceptional fibre: the
classes of the simple objects have Gram matrix `rootMatrix`, their reflections generate `W_aff` and
`W(R)`, and root-positivity is the sign of the charge in the fundamental alcove
(`LinearAlgebra/Lattice/Mukai/AffineWeyl/Coxeter.lean`). `WeylGalleryHypotheses.ofWithClassMap`
builds the hypotheses at `P((0, 1])` of a prestability condition from the twists, the simple tilt,
tilt composition and `C` Serre in `A`, which still have no geometric instance.

### The formal wall model
`Quiver.Preprojective.FormalWallHypotheses` states the formal wall model over an abelian category
`𝒜` (the semistable objects of the phase of a wall), for a half `Q` of the `Ext`-quiver of the
stable objects `S_i` of that phase, loops allowed:
- the wall objects form a Serre class containing the simple objects `S_i`;
- each wall object has a model, a finite-dimensional nilpotent preprojective representation, and
  an order isomorphism of its subobjects with the subrepresentations of the model that carries the
  multiplicities of the `S_i` to dimension vectors (formality of the `Ext`-algebra, Davison,
  arXiv:2106.07692, Proposition 7.8);
- the phase windows: the charges `Z_±(S_i)` on the two sides of the wall lie in the upper
  half-plane (Bayer–Bridgeland, arXiv:1310.8266, Lemma 2.7 and Remark 2.8), and the seesaw: the
  two sides order the phases of any two `S_i` oppositely.

`Quiver.Preprojective.RealizationHypotheses` is a stronger hypothesis of the shape of the
Bondal–Orlov and Bridgeland criteria: a triangulated functor `F : C ⥤ D` with the window condition
`W_{0,1}` on the vertex simples of a source heart generated by them (bijective on `Hom` and `Ext¹`,
injective on `Ext²`), inducing a functor of hearts that sends them to simple objects, with a model
of each source object. For a finite collection of stable objects the source is the thick hull of
the simple modules over the Ginzburg dg algebra of the half `Ext`-quiver (Davison), which agrees
with `D^b(nilp Π_Q)` only off Dynkin components. From the fields:
| Statement | Lean |
|---|---|
| The multiplicities of a wall object are the dimension vector of its model; on either side of the wall the subobjects of a wall object carry the charge function of the restricted charge, with a unique HN filtration, the image of that of the model | `FormalWallHypotheses.dim_eq`, `FormalWallHypotheses.chargeFunction`, `FormalWallHypotheses.nonempty_hnFiltration` |
| The realization constructor: window dévissage makes the functor of hearts full, faithful and mono-preserving, with Serre essential image and every subobject of an image coming from the source, so it identifies subobject lattices and the realization hypotheses give the formal wall model of the target | `RealizationHypotheses.full_G`, `RealizationHypotheses.faithful_G`, `RealizationHypotheses.preservesMono_G`, `RealizationHypotheses.isSerreClass_wall`, `RealizationHypotheses.exists_of_mono`, `RealizationHypotheses.toFormalWallHypotheses` |

The instance from real objects is the wall of one sphere
(`Quiver.Preprojective.SingleVertex.realizationHypotheses`, `SingleVertex.formalWallHypotheses`):
the derived category of finite-dimensional vector spaces with its standard heart, the identity as
realization, the line as vertex simple, and each space its own model, its subobjects being its
subspaces. For a quiver with arrows or loops the source of the realization needs the derived
category of nilpotent preprojective modules, which Mathlib cannot build yet (no abelian category
of quiver representations with its derived category, no dg categories).
[K3TwistsTest/FormalWallModel.lean](K3TwistsTest/FormalWallModel.lean) checks the instance and the
Euler forms of the Jordan and Kronecker quivers.

### The letter-matrix obstruction on the double plane

On a double plane, write `λ(w)` for the point-mass multiplier of a word in `T₀^{±1}, T₁^{±1},
T₃^{±1}`, `T_j` the twist by `𝒪(jH)`. The one geometric input, from the computation of `W_s =
T₀T₁T₃ˢ` on the standard cohomology of line bundles, is that `λ(W_s)` is a root of `P_s`, for
`s ≥ 1` with `s ≡ 1 (mod 19)`; it is a hypothesis (`hroot`), since it needs `D^b(X)` and twist
functors. `P_s` has one real root, so the input fixes `λ(W_s)` to be the Perron root.

| Statement | Lean |
|---|---|
| No invertible complex letter matrices have, for `s ≥ 1`, `s ≡ 1 (mod 19)`, an eigenvalue of `A_{W_s}` of modulus `λ(W_s)`: only the positive spellings `W_s` and only some eigenvalue modulus are used | `AlgebraicGeometry.K3.PicardRankOne.DoublePlane.no_invertible_letter_matrices` |
| For `λ` on a group containing the three twists, no complex matrices of any size, possibly singular, give `ρ(A_{a₁} ⋯ A_{a_j}) = λ(a₁ ⋯ a_j)` on every spelling; no hypothesis `λ(1) ≠ 0` | `AlgebraicGeometry.K3.PicardRankOne.DoublePlane.no_letter_matrices` |
| The unit test: no integer matrix of determinant `±1` has spectral radius a real root of `P_s`, `s ≥ 1`; given the lower bound by such a matrix (the action on the numerical lattice; Kikuta–Shiraishi–Takahashi, Ikeda), it is strict | `AlgebraicGeometry.K3.PicardRankOne.DoublePlane.not_isIntegral_inv_of_root`, `spectralRadius_ne_of_isUnit_det`, `spectralRadius_lt_of_isUnit_det` |

[K3TwistsTest/LetterObstructionModel.lean](K3TwistsTest/LetterObstructionModel.lean) shows the
hypotheses of `no_letter_matrices` are satisfiable, realizes each single `P_s` by `M_s`, and runs
the S-unit theorem with `N = 1` on integer letters of determinant `±1`.

### Piecewise-linear integral models

A `PLModel f κ` is a finite family of cones covering the orthant with nonnegative integer cell
matrices that agree with `f` on their cells. `EigAtRate f`, an eigenvector `0 ≤ v ≠ 0` at the
cycle time, is a hypothesis: for continuous monotone homogeneous maps it follows from Brouwer's
fixed point theorem (Lemmens–Nussbaum, *Nonlinear Perron–Frobenius theory*, Chapter 5), which
Mathlib does not have.

| Statement | Lean |
|---|---|
| The cycle time is an algebraic integer, a root of the characteristic polynomial of a cell matrix | `PLModel.isIntegral_cycleTime` |
| `R(f) = max {t : v ∈ C_k, v ≥ 0, Σ v = 1, A_k v = t v}`, and `R(f) = ρ(A_k[J, J])` on the support `J` of an eigenvector at the rate, also on a face | `PLModel.isGreatest_cycleTime`, `PLModel.gelfandRadius_submatrix_eq_cycleTime` |

[K3TwistsTest/MonotoneHomogeneousModel.lean](K3TwistsTest/MonotoneHomogeneousModel.lean) builds a
one-cell model with `EigAtRate` from the count letters of a wall of two spheres pairing to two and a
two-cell model whose eigenvector at the rate lies on a face; it re-derives the Gelfand-radius
certificates as the linear case, brackets the rate of `M₂` by the ratio test in `[121, 123]`, and
gives a non-additive monotone homogeneous count map that satisfies the squeeze along one orbit. The
polynomial envelope of a piecewise-linear model is not proved.

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
| The Mukai lattice `R ⊕ N ⊕ R` of a bilinear module, its roots and reflections (adapted from derived-alg-geo-lean) | `Mukai.pairing`, `Mukai.mukaiForm`, `Mukai.reflect_reflect`, `Mukai.pairing_reflect_reflect` |
| `C² = -2`, `C·F = 1`, `F² = 0`; `H = C + 2F` has `H² = 2` and contracts `C` and only `C` | `intersection_curve_fibre`, `intersection_polarization`, `intersection_polarization_pos` |
| The wall: `⟨v(A), v(B)⟩ = 2`, `v(A) + v(B) = v(𝒪_x)`, `v(aA + bB)² = -2(a - b)² = -2 q₂(a, b)` with `q₂` the Kronecker form | `pairing_wallA_wallB`, `wallA_add_wallB`, `selfPairing_wallClass_eq_kroneckerForm` |
| The wall word acts on classes as a line bundle: `T_B T_A = ⊗𝒪(C) = E(pt, v(B), -1)`, and `(T_B T_A)ⁿ = ⊗𝒪(nC)` | `reflectHom_wallB_mul_reflectHom_wallA`, `reflectHom_wallB_mul_reflectHom_wallA_eq_eichler`, `reflectHom_wallB_mul_reflectHom_wallA_pow` |
| The affine Weyl group of the curve wall: `C` with `Θ = C` is a fundamental cycle, its affine simple roots are `v(A)`, `v(B)`, the Riemann–Roch membership field holds on `NS` at `H`, so for `0 < β·C < 1` no rank-zero root orthogonal to `H` has `β·c = s`; `Λ = ℤ`, `Λ_H = Q^∨ = 2ℤ` of index `2 = det A₁`; the length-zero element `⊗𝒪(F) ∘ ρ_B` swaps `v(A)` and `v(B)` and fixes `v(𝒪_x)`, and its square is `⊗𝒪(H) ≠ 1` | `sectionFibre`, `sectionFibre_affineRoot_none`, `sectionFibre_riemannRochMembership`, `fibreCharge_ne_zero_of_mem_alcove`, `degreeLattice_sectionFibre`, `polarizedDegreeLattice_sectionFibre`, `index_corootLattice_sectionFibre`, `lengthZero_wallA`, `lengthZero_wallB`, `affineRootPerm_lengthZero`, `lengthZero_mul_self`, `lengthZero_mul_self_ne_one` |
| On the curve wall every degree is realized and `NS` is even, so the length-zero permutations form a group isomorphic to `P^∨/Q^∨ = ℤ/2`, of order `2`; the length-zero element at the minuscule node is `⊗𝒪(F) ∘ w` with `w ∈ W(A₁)`, sending `v(A)` to `v(B)`, and `⊗𝒪(F) ∘ ρ_B` is one; `⟨v(A), v(B)⟩ = 2`, so the Coxeter matrix of the two simples is `Ã₁`, its reflection representation has image `W_aff`, and for `0 < β·C < 1` root-positivity of a word is the sign of `β·c - s` on its prefix roots | `sectionFibreLengthZeroPermEquiv`, `card_lengthZeroPerm_range_sectionFibre`, `exists_lengthZero_sectionFibre`, `lengthZero_mem_lengthZeroGroup`, `affineExt_sectionFibre`, `affineCoxeterMatrix_sectionFibre`, `range_affineWeylRep_sectionFibre`, `isRootPositive_sectionFibre_iff` |
| The wall matrix of `A`, `B` is `[[2, -2], [-2, 2]]`: the curve wall is of affine type, its null vector is `v(𝒪_x)`, its isotropic classes are the multiples of `v(𝒪_x)`, and the Tits identity gives `v(aA + bB)² = -(a, b)ᵀA(a, b)`; `𝒪_x`, `T_A 𝒪_x` and `𝒪_X/(I_C I_x)` have multiplicities `(1, 1)`, `(1, 1)`, `(2, 1)` | `wallMatrix_curveWall`, `curveWall_posSemidef_and_not_posDef`, `isIsotropic_wallClass_iff`, `selfPairing_wallClass_eq_neg_dotProduct`, `curveWall_pairingTwoWall_classes` |
| Riemann–Roch on the wall: an `(m, 1)` object `D₀ ⊕ A^r` has `dim Ext¹ = 2(1 + pq) - 2(p + q - 1)² + 2r(2 - p - q)`, which is `2` only at `p = q = 1`; the class `(2, 2)` is isotropic | `ext_one_count`, `ext_one_count_eq_two_iff`, `selfPairing_wallClass_two_two` |
| `v(𝒪_C(j)) = (j + 1)v(A) + j v(B)`; `M_{d,x}` has multiplicities `(d + 2, d + 1)` and square `-2`; `D(jC)/(I_x ⊗ D(-C))` grows by layers `𝒪_C(d - 2j)`; the thickening `K_ε ⊗ 𝒪_X/(I_x I_C^{r+1})` has class `(0, (r + 1)C, (r + 1)(r + 1 + ε) + 1)` and square `-2(r + 1)²`, so `dim Ext¹ = 2` | `curveSheaf_eq_wallClass`, `embeddedPoint_eq_wallClass`, `idealQuotient_succ`, `thickening_eq`, `selfPairing_thickening` |
| The quotients of each tower add up to the class of the twisted point: the two towers of the thickening, `T_{K_ε(-(r+1)C)} 𝒪_x`, the two-letter word `T_{D(nF)}⁻¹ T_{D(-C)} 𝒪_x` in every degree, the rank-two example | `point_add_sum_curveSheaf`, `sum_A_side_odd`, `sum_A_side_even`, `reflect_lineBundle_point`, `reflect_reflect_point`, `reflect_rankTwo_point` |
| The charge at the wall: `Z(aA + bB) = -(a + b)/2` (phase one), `Z(M_{d,x}) = -(2d + 3)/2`, `Z(𝒪_X[1]) = -2 + i`, `Z(𝒪_X(-C - F)[1]) = -7/4 + 2i`, `Z(𝒪_X(-C + 2F)) = 4 + i`, `Z(𝒪_X(-C + 3F)) = 19/4 + 2i`, `Z(𝒪_X(-2C + 2F)) = 17/2 + i`, `Z(I_x(-2C + 2F)) = 19/2 + i`, and the order of their phases | `charge_wallClass`, `charge_embeddedPoint`, `charge_structureSheaf_shift`, `charge_tailOdd_shift`, `charge_twoLetter`, `charge_rankTwo`, `arg_charge_wallClass`, `arg_charge_structureSheaf_shift` |
| The parity argument: a root of odd rank and imaginary charge `2` is not the sum of two roots of imaginary charge `1`; so `𝒪_X(-C - F)[1]` and every line bundle of `H`-slope `3` are stable | `not_isSpherical_sub_of_odd_rank`, `not_split_tail_odd`, `not_split_slope_three` |
| The words `T_{𝒪_X(-2C)}`, then `T_{𝒪_X(-C + 2F)}⁻¹`, then `T_{𝒪_X(-C + 3F)}⁻¹` applied to `𝒪_x`: the two-letter tower has charges `-4 - i`, `-7/2`, `19/2 + 4i` adding up to `2 + 3i`; the wall masses are `4 + √5`, `(7/2)(1 + √17)` and `3/2 + √41/4`; the third word has the class `(0, C + F, 3)` of `𝒪_{C+Γ}(C + 4F)` and of `𝒪_C(1) ⊕ 𝒪_Γ(x)` | `charge_twoLetter_tower`, `mass_oneLetter`, `mass_twoLetter`, `mass_threeLetter`, `reflect_threeLetter_point` |
| Stable classes in charge coordinates: with `p = 4 Re Z`, `q = Im Z`, `v² ≥ -2` iff `(43r - 2(p + 2q))² + 43(4a - r - 2q)² ≤ 4(p + 2q)² + 172q² + 688` | `neg_two_le_selfPairing_iff` |
| The charge of the curve wall is `Z = ⟨Ω, -⟩` with `Ω = (1, β + iH, -3 + i)` and `Ω² = 31/8 - 2i ≠ 0`; it is a `GL₂⁺(ℝ)`-translate of an exponential charge: `⟨exp(B + iω), v⟩ = Re Z(v) + (1/2 + i√43/4) Im Z(v)` for `B = C/4 + F`, `ω = (√43/4) H` | `charge_eq_mukaiCharge`, `selfPairing_chargeClass`, `isIsotropic_expClass`, `mukaiCharge_expClass` |
| Near the wall phases follow `B`-fractions: `j/(2j + 1)` (for `𝒪_C(j)`) increases below `1/2`, `j/(2j - 1)` (for `T_A 𝒪_C(j)`) decreases above it, and a subobject in the section-evaluation argument has fraction at most `j/(2j + 1)` | `cross_restrictedCharge`, `curveSheaf_fraction_strictMono`, `twistCurveSheaf_fraction`, `subobject_fraction_le` |
| `exp h_cat(T_{𝒪_C} T_{𝒪_C(2)}) = (4² - 2 + √(4⁴ - 4·4²))/2 = 7 + 4√3` (Barbacovi–Kim, arXiv:2107.06079), while points off `C` are fixed | `barbacoviKim_four`, `barbacoviKim_four_root` |
| `v(𝒪_X[1])` and `v(𝒪_C)` pair to `1`, an `A₂` configuration: reflections in roots are conjugation-equivariant under isometries, `ρ_{v(𝒪_C)} ρ_{v(𝒪_X)} v(𝒪_C) = v(𝒪_X[1])` (the class of `T_{𝒪_C} T_{𝒪_X} 𝒪_C ≅ 𝒪_X[1]`), so `Art(A₂)` acts on the Mukai lattice, through `W(A₂)`, and every pure braid acts trivially | `reflection_smul`, `a2_edge`, `a2Hom`, `exists_factor_a2Hom`, `a2Hom_eq_one_of_mem_pureArtinGroup` |
| The classes `v(𝒪_X[1])`, `v(𝒪_C)` have Gram matrix `A₂` in the Mukai sign and are linearly independent; the reduced words `[0, 1, 0]`, `[1, 0, 1]` of `w₀` are root-positive on them (prefix roots `α₀, α₀ + α₁, α₁`), equal in `Art(A₂)`, and `w₀(α_i) = -α_{1-i}`: the class-level inputs of `F_{w₀} 𝒪_X[1] ≅ 𝒪_C[-1]` and `F_{w₀} 𝒪_C ≅ 𝒪_X` | `mukaiForm_a2Class`, `linearIndependent_a2`, `isRootPositive_a2_longest`, `prefixRoots_a2_longest`, `ofSignedWord_a2_longest`, `reflectWord_a2_longest`, `a2_longest_inputs` |

## The framed multiplier

The framed multiplier is the product of units `S_e = ∏_{α > 0} (1 - x^α)^{e_α}` in
`MvPowerSeries σ R`, for any commutative ring `R`, any type `σ` of vertices and integer exponents
on the nonzero exponent vectors. A framing `p : σ → ℤ`, possibly signed, pairs with a class by
`p·α = Σ p_i α_i`; for an external object `D` and wall simples `A_i`, `p_i = χ(D, A_i)`. The
numerical framed DT statement for BPS invariants `Ω` is that the series framed by `p` is the
multiplier with exponents `e_α(p) = Ω_α (p·α)`. The sign convention is Mozgovoy's
(arXiv:1107.6044, Theorem 5.1, Corollary 2.8): the factor is `(1 - x^α)^{(p·α)Ω_α}` in the twisted
variables `x^α = (-1)^{w·α} y^α`, and `Ω = -A(1)` for the Kac polynomials `A`. Only the formal
multiplier is formalized: integer exponents, so the numerical and not the motivic DT formula, and
neither the automorphism of the twisted torus algebra nor the analytic Riemann–Hilbert problem
(Bridgeland, arXiv:1611.03697). The values of Kac polynomials and the identification of framed
counts with the multiplier are cited, not formalized.

| Statement | Lean |
|---|---|
| Agreement of coefficients on a lower set of exponents is a ring congruence; a product over any index type whose factors are `1` below each exponent, up to finitely many, converges in the product topology | `MvPowerSeries.CoeffEqOn.mul`, `MvPowerSeries.hasProd_of_coeffEqOn_one` |
| Over any commutative ring: `S_e` is the infinite product of its factors; `S_{e+e'} = S_e S_{e'}`, so the multiplier is multiplicative in the framing; finitely many nonzero exponents give the finite product; coefficient inversion `[x^α] S_e - [x^α] S_{e'} = -(e_α - e'_α)` when `e, e'` agree below `α`; the `(1, 1)` coefficient `e_a e_b - e_{a+b}` for `a ≠ b` | `hasProd_S`, `S_add`, `framedS_add`, `Z_add`, `S_eq_prod`, `coeff_S_sub`, `coeff_S_one_one`, `coeff_two_simple` |
| Over a ring of characteristic zero `e ↦ S_e` is injective, and one framing with `p·α ≠ 0` on every positive class determines `Ω`; over `ℤ` it is a bijection onto the series with constant term one (big Witt vectors), and the DT statement is the equation `e_α(p) = Ω_α (p·α)` for these exponents | `S_injective`, `framedS_injective`, `S_bijective_int`, `isFramedDT_iff` |
| A framing does not see `Ω_α` where `p·α = 0`: the curve-wall framing `(m + 1, -m)` misses the root `(m, m + 1)` | `framedS_update_of_pair_eq_zero`, `pair_signed_blind` |
| The positive roots of `A_n`, for the Tits form `½ αᵀ A_n α` of Mathlib's Cartan matrix, are the intervals; the multiplier of type `A_n` is the finite product over them | `Quiver.TypeA.titsForm_eq_one_iff`, `Quiver.TypeA.dotProduct_cartanA_mulVec`, `framedS_typeA` |
| The Jordan quiver: `Z_2(y) = Z_1(-y)² ≠ Z_1(y)²`. The affine Kronecker quiver with framing `(p, q)`: exponents `-((n + 1)p + nq)`, `-(np + (n + 1)q)`, `-2n(p + q)`; `xy` coefficient `pq + 2(p + q)`; coefficient `8` at `(2, 2)` for the framing `(1, 0)`, computed by a verified table recursion | `jordan_Z_two_eq`, `jordan_Z_two_ne`, `kronecker_exponent_R`, `kronecker_exponent_L`, `kronecker_exponent_diag`, `coeff_kronecker_one_one`, `coeff_S_mk2`, `coeff_kronecker_two_two` |
| The curve wall of the elliptic K3: the Kronecker indices `-1` and `-2` mark the spherical and the nonzero isotropic wall classes; `𝒪_X(D)` frames the wall by `(1 - C·D, C·D)`; for `C·D = -m` the exponents are `-(n + m + 1)`, `m - n`, `-2n`, the `xy` coefficient is `2 - m(m + 1)` and the class `(m, m + 1)` is not seen; framed by `𝒪_X` the coefficient at `(2, 2)` is `8`; a point is framed by the rank, and the rank-two extension `S` gives `Z_1(-y)²` | `kroneckerIndex_eq_neg_one_iff`, `kroneckerIndex_eq_neg_two_iff`, `wallFraming_eq`, `curveWall_exponent_R`, `coeff_curveWallMultiplier_one_one`, `curveWall_blind`, `coeff_curveWallMultiplier_two_two`, `pointMultiplier_rankTwo_ne` |

Unqualified names are in `MvPowerSeries.FramedMultiplier`, those of the last row in
`AlgebraicGeometry.K3.EllipticWithSection`.
[K3TwistsTest/FramedMultiplierCounterexamples.lean](K3TwistsTest/FramedMultiplierCounterexamples.lean)
keeps the counterexamples: over `ℤ/2`, `(1 - x)² = 1 - x²`, so injectivity needs characteristic
zero; over `ℚ`, `1 + x/2` is no multiplier with integer exponents; the `(1, 1)` formula fails for
`a = b`; and an exponent proportional to `p·α` need not be an integer multiple of it.

### The BPS interface of a wall block

For stable spherical objects of one phase with `Ext`-quiver `Q` (`e i j = e j i` arrows between
distinct vertices, no loops), `Quiver.KacData` holds the Kac polynomials `A_α(q)` on `ℤ^σ` with
their published properties, stated on the root form of `Q`: `A = 1` on the positive real roots,
`A = 0` where `q(α) ≥ 2`, and `A_{sᵢα} = A_α` for `α ≠ eᵢ` (Kac, *Infinite root systems,
representations of graphs and invariant theory*, Invent. Math. 56, 1980, with the reflection
functors of Bernstein, Gelfand and Ponomarev). `Quiver.BPSHypotheses` adds three numerical fields:
- Mozgovoy's formula localized to the nilpotent locus: the nilpotent framed series of the tripled
  quiver, framed by `w ≥ 0`, is `Z_w` with exponents `-(w·α) A_α(1)` (Mozgovoy, arXiv:1107.6044,
  Theorem 5.1, Corollary 2.8; the localization by the `ℂ*`-action adapts the
  Behrend–Bryan–Szendrői argument; Davison, arXiv:1602.02110, Proposition 8.3 with Theorem B,
  proves a cohomological form for the preprojective algebra, and Bozec–Schiffmann–Vasserot,
  arXiv:1701.01797, Proposition 1.2, the agreement of nilpotent and ordinary Kac polynomials at
  `q = 1`);
- the framed/unframed identity: the same series is `Z_w` with exponents `(w·α) Ω^Q_α` for the
  nilpotent BPS invariants `Ω^Q` of the tripled quiver (Mozgovoy, arXiv:1104.4335,
  Corollary 4.17);
- the CY3 local model `localModel`: the local BPS invariants `Ω` of the wall block on `X × 𝔸¹`
  are those of the tripled quiver with its potential. This statement has no published proof and
  no human review, and a theorem over it is only as good as the field. Its `2`-Calabi–Yau form,
  the objects filtered by the simples as nilpotent representations of the preprojective algebra of
  a half of `Q`, is Davison–Hennecart–Schlegel Mejia, arXiv:2212.07668, Corollary 7.2.

| Statement | Lean |
|---|---|
| `Ω^Q = -A(1)` from the two framed fields at the one framing `(1, …, 1)`, and `Ω = -A(1)` with the CY3 local model; the interface says no more: for given Kac data and `Ω` the fields can be met iff `Ω = -A(1)` on the positive classes | `Quiver.BPSHypotheses.bpsQ_eq`, `Quiver.BPSHypotheses.omega_eq`, `Quiver.BPSHypotheses.exists_iff` |
| Weyl descent: for a sign-coherent root form, `A = 1` on the real roots follows from `A_{eᵢ} = 1` and the reflection invariance; with the CY3 local model, `Ω = -1` on the simple objects and on every positive real root, in particular on the prefix roots of a root-positive word, the classes of the new simple objects along a Weyl gallery; `Ω_{sᵢα} = Ω_α`; `Ω = 0` where `q ≥ 2` | `Quiver.KacData.ofSignCoherent`, `omega_single`, `omega_eq_neg_one_of_isRealRoot`, `omega_eq_neg_one_of_isRootPositive`, `omega_reflect`, `omega_eq_zero` |
| The curve wall of the elliptic K3, an instance from a quiver: the `Ext`-quiver computed from `⟨v(A), v(B)⟩ = 2` is the affine Kronecker quiver, with root form `-2(a - b)²`, sign coherent; the Kronecker Kac polynomials `1`, `q + 1`, `0` give its Kac data, with `A = 1` on the real roots by descent; the affine Kronecker indices are `-A(1)` and give the interface, with the curve-wall multiplier as framed series; `Ω = -1` on the real roots, `Ω = -2` at `(n, n)`, and `Ω = 0` at `(a, b)` with `\|a - b\| ≥ 2`, the classes `(0, kC, n)` with `\|k\| ≥ 2` | `curveWallExt_eq`, `rootForm_curveWallExt`, `isSignCoherent_curveWallExt`, `curveWallKac`, `kroneckerBPS_eq_neg_kac`, `curveWallBPS`, `curveWallMultiplier_eq`, `curveWall_omega_real`, `curveWall_omega_null`, `curveWall_omega_eq_zero` |

Unqualified names of the second row are in `Quiver.BPSHypotheses`, those of the last row in
`AlgebraicGeometry.K3.EllipticWithSection`. Every theorem about `Ω` uses the CY3 local model and
says so in its docstring. [K3TwistsTest/BPSModel.lean](K3TwistsTest/BPSModel.lean) gives the
consistency model of one spherical object and checks the curve wall at `(2, 1)`, `(2, 2)`,
`(3, 1)` and along an alternating word. The three numerical fields have no geometric instance:
the framed moduli of the tripled quiver, the Behrend function and the moduli of objects on
`X × 𝔸¹` are not in the library, and at the curve wall the fields are met by taking the framed
series to be the multiplier and `Ω` to be the quiver's.

## Layout

The library mirrors Mathlib: a file sits at the Mathlib path of the API it extends, or of its
nearest Mathlib precedent, and its declarations use Mathlib's namespaces. Moving a file into
Mathlib or into derived-alg-geo-lean keeps its path below the library root.

| Module under `K3Twists/` | Job | Namespace |
|---|---|---|
| `Analysis/SpecificLimits/GrowthRate.lean` | exponential growth rates of sequences: Fekete with a constant and with a gap, padding, a submultiplicative sequence without polynomial envelope | `Real` |
| `GroupTheory/Commutator/ForkWord.lean` | fork words are conjugate to a two-letter period | root |
| `Analysis/Matrix/GelfandRadius.lean` | rates of nonnegative matrices, certificates and variational bounds for the Gelfand radius, the `SL₂` rate and the Thurston matrices | `Matrix` |
| `Analysis/Matrix/BipartiteCompression.lean` | the compression of bipartite multitwists to Thurston matrices and the rate of their words | `Matrix.BipartiteCompression` |
| `Analysis/Matrix/JointSpectralRadius.lean` | word maxima in a monoid, the joint spectral radius, a pair of unipotent matrices and the triangle | `Monoid`, `Matrix` |
| `Analysis/Matrix/SLTwoRate.lean` | the larger root of `x² - tx + 1` as the Gelfand radius of a hyperbolic matrix of determinant one | `Matrix` |
| `Analysis/Matrix/BlockTriangular.lean` | block-triangular certificates: the chain bound `C(1 + k)^{c-1}ρᵏ` and the tower certificate | `Matrix` |
| `Analysis/Matrix/BipartiteJointSpectralRadius.lean` | the single twists of a weighted graph, the compression to two colour sums, the joint spectral radius of a bipartite graph | `Matrix` |
| `Analysis/Matrix/StarWord.lean` | the star word and its rate, the larger root of `t² - (d + 2)t + 1` | `Matrix.BipartiteCompression` |
| `Analysis/Matrix/Variational.lean` | the variational formula: the period certificates converge to the rate, which is their infimum | `Matrix` |
| `Analysis/Convex/HilbertMetric.lean` | the Thompson and Hilbert pseudometrics on positive functions, as plain `[0, ∞]`-valued functions | root |
| `Analysis/Convex/Birkhoff2.lean` | the ratio map of a `2 × 2` matrix, Birkhoff's contraction coefficient `tanh(Δ/4)` | `Matrix` |
| `Analysis/Convex/IFS.lean` | the coding map of an iterated function system and its Cantor embedding; the two-block alphabet and its continued fractions | `IFS`, `Matrix` |
| `Analysis/Normed/Algebra/PowerBound.lean` | the polynomial envelope of powers from an annihilating polynomial; complex matrices | root, `Matrix` |
| `LinearAlgebra/Dimension/ExactSequenceDefect.lean` | Poincaré polynomials of long exact sequences and the defect identity | `LaurentPolynomial`, `LinearMap` |
| `Algebra/PoincareParity.lean` | `P(1)`, `P(-1)` of a family of dimensions and their parity | `Finsupp` |
| `Analysis/Complex/Crofton.lean` | the Crofton constant, the barycentre identity and the directional ratio | `Complex` |
| `GroupTheory/GroupAction/TwistSystem.lean` | twist systems, the domination recursion and the exponent of the centre counts | root |
| `GroupTheory/GroupAction/TwistSystem/Orbit.lean` | the orbit of the centres; invariance of `P_q` and `η` under maps compatible on it | root |
| `GroupTheory/GroupAction/TwistSystem/Bipartite.lean` | the coupling graph of the centres and the bipartite bound `e^η ≤ ρ_s` | root |
| `GroupTheory/GroupAction/MassComparison.lean` | `MassDistanceBound`, `MassComparisonHypotheses`: the two comparisons, the mass domination system and the exponent theorem in mass form | root |
| `GroupTheory/GroupAction/MassComparison/FixedWord.lean` | the largest count from a centre, the masses along a word and the fixed-word formula | root |
| `GroupTheory/GroupAction/MassGrowth.lean` | Theorem C: σ-independence, the component decomposition, the analytic core; the envelope over a monoid; subsystems | root |
| `GroupTheory/GroupAction/CountCocycle.lean` | count cocycles: the growth sandwich, exact counts and rates on tight seeds | root |
| `Order/Squeeze.lean` | the squeeze along a tight orbit, in any partial order | `Order` |
| `LinearAlgebra/Matrix/SignRule.lean` | count and signed letters, the sign rule with the parity-graded form, word-level domination | `Matrix` |
| `LinearAlgebra/Lattice/Mukai/PicardRankOne.lean` | the Mukai lattice of a Picard-rank-one K3 in coordinates: module structure, pairing, roots, punctures | `MukaiVector` |
| `LinearAlgebra/Lattice/Mukai/Basic.lean`, `Mukai/Reflection.lean`, `BilinearForm/Hyperbolic.lean`, `BilinearForm/Reflection.lean`, `Lattice/Arithmetic/TorsionFree.lean` | the Mukai lattice `R ⊕ N ⊕ R` of a bilinear module over a commutative ring and its reflections (Mathlib's `Module.preReflection`), adapted from derived-alg-geo-lean | `Mukai`, `BilinearForm`, `IntegralLattice` |
| `LinearAlgebra/Lattice/Mukai/Slice.lean` | the slice of a class, the Picard-rank-one lattice as a Mukai lattice, exponential points and the slice lemma | `Mukai` |
| `LinearAlgebra/Lattice/Mukai/CentralCharge.lean` | central charges `⟨Ω, -⟩`, the exponential chart and the half-turn of an isometry | `Mukai` |
| `LinearAlgebra/BilinearForm/Eichler.lean`, `BilinearForm/Gram.lean` | Eichler transvections, products of two reflections, the Eichler homomorphism; the Gram matrix and the Tits identity | `BilinearForm` |
| `LinearAlgebra/BilinearForm/ReflectionGrowth.lean` | two reflections on their plane, the pairings along the orbit and the rate at pairing `\|g\| > 2` | `BilinearForm` |
| `LinearAlgebra/Lattice/Mukai/Eichler.lean` | the Mukai quadratic form, `⊗𝒪(D)` as an Eichler transvection, the wall of a `(-2)`-curve | `Mukai` |
| `LinearAlgebra/Lattice/Mukai/AffineWeyl.lean`, `Mukai/AffineWeyl/Group.lean`, `AffineWeyl/Index.lean`, `AffineWeyl/LengthZero.lean` | a connected exceptional fibre with its fundamental cycle: affine simple roots, the extended Dynkin matrix, the fundamental-alcove theorem; the affine Weyl group `E(Q) ⋊ W(R)`; the translation lattices and their index bounds; length-zero elements | `Mukai`, `Mukai.FundamentalCycle` |
| `LinearAlgebra/Lattice/Mukai/AffineWeyl/SimpleReflection.lean` | simple reflections of a fibre: positive roots, generation of `W_aff` and `W(R)`, the trivial stabilizer, simple roots to positive roots | `Mukai.FundamentalCycle` |
| `LinearAlgebra/Lattice/Mukai/AffineWeyl/Minuscule.lean` | inversion sets and the descent; a length-zero element in every coset of `W_aff`; length-zero elements at minuscule nodes | `Mukai.FundamentalCycle` |
| `LinearAlgebra/Lattice/Mukai/AffineWeyl/LengthZeroGroup.lean` | the extended affine Weyl group as `E(N) ⋊ W(R)`; the class of a length-zero element in `P^∨/Q^∨`; the length-zero permutations as `Λ/Q^∨` | `Mukai.FundamentalCycle` |
| `LinearAlgebra/Lattice/Mukai/AffineWeyl/Coxeter.lean` | the Coxeter matrices and reflection representations of the Weyl groups of a fibre; the charge cone and the sign of the class in the fundamental alcove | `Mukai.FundamentalCycle`, `BilinearForm` |
| `LinearAlgebra/Lattice/Mukai/AffineWeyl/SeveralFibres.lean` | roots on several orthogonal fibres lie on one; the fundamental-alcove theorem for several fibres | `Mukai.FundamentalCycle` |
| `Combinatorics/Quiver/Kronecker/RealRoots.lean` | the real roots of the `g`-Kronecker quiver and their determinants | `Quiver.Kronecker` |
| `LinearAlgebra/Matrix/ZMatrix.lean`, `Matrix/ZMatrix/Integer.lean`, `Matrix/ZMatrix/Isotropic.lean` | symmetric Z-matrices: the ground-state identity, the M-matrix criterion, the affine kernel, integer certificates, isotropic sums of spheres, the wall matrix of a family and the Tits identity | `Matrix`, `LinearMap.BilinForm` |
| `LinearAlgebra/Lattice/Mukai/SphericalConfiguration.lean` | isotropic sums with natural coefficients of a Gram matrix of spheres, for any index type; independence of sign and indexing; anisotropy is not closed under orthogonal sums; one and two spheres; the lattice core of a lost carrier | `Matrix`, `BilinearForm` |
| `LinearAlgebra/Matrix/ZMatrix/SignCoherence.lean` | sign coherence of the roots of a positive semidefinite symmetric Z-matrix | `Matrix` |
| `LinearAlgebra/Matrix/ZMatrix/OneSummand.lean` | roots of an orthogonal sum lie in one summand | `LinearMap.BilinForm` |
| `LinearAlgebra/Matrix/IsotropicRankTwo.lean` | a symmetric `2 × 2` matrix is isotropic iff minus its determinant is a square | `Matrix` |
| `LinearAlgebra/Matrix/Cartan/Basic.lean` | finite-type Cartan matrices from certificates; `E₆`, `E₇`, `E₈`, `Ẽ₈` | `Matrix`, `CartanMatrix` |
| `LinearAlgebra/Matrix/Cartan/Determinant.lean` | the determinants of `Aₙ` and `Dₙ` | `Matrix`, `CartanMatrix` |
| `Combinatorics/Quiver/Kronecker/CartanMatrix.lean` | the wall matrix `[[2, -g], [-g, 2]]` of two spheres and its trichotomy | `Quiver.Kronecker` |
| `AlgebraicGeometry/Surface/K3/PicardRankOne/WallMatrix.lean` | the wall matrix of two spherical simples in Picard rank one | `AlgebraicGeometry.K3.PicardRankOne` |
| `AlgebraicGeometry/Surface/K3/EllipticWithSection/WallMatrix.lean` | the wall matrix of the curve wall and of a wall of pairing two | `AlgebraicGeometry.K3` |
| `Combinatorics/Quiver/TypeA/Roots.lean` | the Tits form of `A_n` and its positive roots, the intervals | `Quiver.TypeA` |
| `RingTheory/MvPowerSeries/LowerSet.lean` | agreement of coefficients on a lower set of exponents, locally finite products | `MvPowerSeries` |
| `Combinatorics/DT/FramedMultiplier.lean` | the framed multiplier over any commutative ring: products, multiplicativity, coefficient inversion, framings | `MvPowerSeries.FramedMultiplier` |
| `Combinatorics/DT/Inversion.lean` | injectivity in characteristic zero, the big Witt bijection over `ℤ`, recovering `Ω` from one framing, the framed DT statement | same |
| `Combinatorics/DT/TwoVertex.lean` | coefficients of the multiplier of a two-vertex quiver by a computable table recursion | same |
| `Combinatorics/DT/Quivers.lean` | the multiplier of the Jordan, type-`A_n` and affine Kronecker quivers | same |
| `Combinatorics/DT/BPS.lean` | the Kac data of a loopless quiver and the BPS interface of a wall block: `Ω = -A(1)` from its fields, Weyl descent | `Quiver` |
| `AlgebraicGeometry/Surface/K3/PicardRankOne/CentralCharge.lean` | central charges, the half-turn of a twist, the opening example | `AlgebraicGeometry.K3.PicardRankOne` |
| `AlgebraicGeometry/Surface/K3/PicardRankOne/WallArithmetic.lean` | the integers of a wall with two spherical simples | same |
| `AlgebraicGeometry/Surface/K3/PairingTwoWall.lean` | the length-three object at a wall of pairing two, its two HN filtrations and that of the point | `AlgebraicGeometry.K3` |
| `CategoryTheory/Abelian/Subobject/Valuation.lean` | additive functions are valuations on subobjects; modularity; the charge function of a stability function | `CategoryTheory.Subobject` |
| `CategoryTheory/Abelian/Uniserial.lean` | the subobjects of nonsplit extensions of simple objects | `CategoryTheory` |
| `CategoryTheory/Abelian/TorsionTheory/Saturation.lean` | the interval class on the subobjects of an object of a class closed under quotients and extensions; its radical and saturation | `CategoryTheory.ObjectProperty` |
| `CategoryTheory/Abelian/TorsionTheory/Transport.lean` | subobjects along an equivalence; transport of subquotient classes, saturations and the radical | `CategoryTheory.Functor`, `CategoryTheory.ObjectProperty` |
| `CategoryTheory/ObjectProperty/Coreflection.lean` | coreflections into a class of objects; the partial right adjoint of its inclusion | `CategoryTheory.ObjectProperty` |
| `CategoryTheory/Subobject/FullyFaithful.lean` | subobjects along a fully faithful functor: the image of a subobject, order reflection, the order isomorphism | `CategoryTheory.Functor`, `CategoryTheory.Subobject` |
| `CategoryTheory/MassProfile/Basic.lean` | profiles `Obj → ℝ≥0` with the arrow action, `Hom` profiles, limits of normalized profiles, the Thompson and half-Hilbert pseudometrics of profiles | `Profile` |
| `CategoryTheory/MassProfile/FibreFunctor.lean` | fibre-functor profiles: `μ_F ≥ \|⟨w_F, v⟩\|` with parity | root (`FibreFunctorProfile`) |
| `CategoryTheory/Abelian/TorsionTheory/Radical.lean` | the radical as a coreflection: monic counit, existence on Noetherian objects or from coproducts, generators, `Ext¹`, a torsion pair from a potential | `CategoryTheory.ObjectProperty` |
| `CategoryTheory/Triangulated/TStructure/HeartAbelian.lean` | the heart of a t-structure is abelian; its short exact sequences are distinguished triangles | `CategoryTheory.Triangulated.TStructure` |
| `CategoryTheory/Abelian/SerreClass/Additive.lean` | the kernel of a nonnegative additive function is a Serre class; a torsion pair from torsion sequences; a torsion sequence is a coreflection | `CategoryTheory.ObjectProperty`, `CategoryTheory.Abelian.TorsionTheory` |
| `CategoryTheory/Triangulated/TStructure/Tilting.lean` | the converse of the tilting theorem: a heart between `A` and `A[1]` is a tilt of `A` | `CategoryTheory.Triangulated.TStructure` |
| `CategoryTheory/Abelian/SerreClass/ExtensionClosure.lean` | the extension closure of a class of objects of an abelian category; for simple objects a Serre class | `CategoryTheory.ObjectProperty` |
| `CategoryTheory/Triangulated/ExtComparison.lean` | window dévissage: the window condition on shifted morphisms spreads from a family to its extension closure; full faithfulness and the essential image there; Yoneda compatibility | `CategoryTheory.Functor`, `CategoryTheory.ObjectProperty` |
| `CategoryTheory/Triangulated/ExtComparison/Heart.lean` | the abelian corollary under the heart-type fields `AbelianHeartHypotheses`: Serre images, admissible subobjects | `CategoryTheory.Triangulated` |
| `Algebra/Homology/DerivedCategory/AbelianHeart.lean` | the heart-type fields for the standard heart `C ⥤ D(C)` | `DerivedCategory` |
| `LinearAlgebra/PoincareDuality.lean` | injectivity from a pairing into a space of dimension at most one (the degree-two lemma); Poincaré duality decides injectivity of a graded algebra map from its top degree | `LinearMap`, `AlgHom` |
| `CategoryTheory/Triangulated/SerreFunctor/CompositionTrace.lean` | the composition–trace pairing of a Serre functor, the degree-two lemma for functors commuting with shifts, the Euler form and the orthogonality lemma | `CategoryTheory.SerreFunctor.SerreFunctorData`, `CategoryTheory.Functor`, `CategoryTheory.Triangulated` |
| `Topology/Spectral/ConstructibleCover.lean` | finite and directed covers of a spectral space by constructible sets | `Topology` |
| `RingTheory/Polynomial/Basic.lean` | multiplication by `X` enlarges every nonzero finite-dimensional subspace of `K[X]` | `Polynomial` |
| `RingTheory/Polynomial/Chebyshev.lean` | powers under `x² = tx - 1` through Chebyshev polynomials; `2 × 2` Cayley–Hamilton | `Polynomial.Chebyshev`, `Matrix` |
| `Combinatorics/Quiver/ChebyshevSeries.lean` | the matrix Chebyshev series, reachability at the graph distance, the Euler characteristic of the bar complex, the Koszul shadow | `Matrix`, `SimpleGraph` |
| `AlgebraicGeometry/Surface/K3/PicardRankOne/PointMassEstimates.lean` | the inequalities inside Lemma A.1 and the constant `K` | same |
| `AlgebraicGeometry/Surface/K3/PicardRankOne/PointMass.lean` | the point-mass corollary from its inputs (`PointMassHypotheses` extends `MassComparisonHypotheses`) | same |
| `AlgebraicGeometry/Surface/K3/PicardRankOne/TwistWords.lean` | standard words and the words `Θ`, `Ψ` of the mass section | same |
| `AlgebraicGeometry/Surface/K3/PicardRankOne/EulerTwistSystem.lean` | the twist system of `𝒪_X` and `𝒪_X(H)` read through the Euler pairing, with positive exponent | same |
| `AlgebraicGeometry/Surface/K3/PicardRankOne/PeriodicWitness.lean` | the periodic witness `(T_S T_B)ⁿ` and the bound `η ≥ log(d + 1)` for the Euler-pairing system | same |
| `AlgebraicGeometry/Surface/K3/PicardRankOne/EulerMass.lean` | the lattice instance of `MassComparisonHypotheses` and Theorem C for the point class | same |
| `AlgebraicGeometry/Surface/K3/PicardRankOne/EulerCountCocycle.lean` | the count cocycle of the Euler pairings with `𝒪_X` and `𝒪_X(H)`, and the failure of the sign rule for it | same |
| `AlgebraicGeometry/Surface/K3/PicardRankOne/HNTower.lean` | the tower theorem of the draft: deprecated aliases for `CategoryTheory/Triangulated/StabilityCondition/Tower.lean` | same |
| `AlgebraicGeometry/Surface/K3/PicardRankOne/AnisotropicWall.lean` | two roots of pairing two are opposite; every rank-one wall is anisotropic; the tower theorem through the split tower theorem; the wall of `𝒪_X` and `𝒪_X(-H)[1]` | same |
| `AlgebraicGeometry/Surface/K3/PicardRankOne/RigidWall.lean` | the example of a rigid wall at `g = 3` | same |
| `Order/HarderNarasimhan.lean` | Harder–Narasimhan filtrations in a lattice with a charge function: extremality, uniqueness, existence; slope functions as charge functions | `Order.ChargeFunction`, `Order.SlopeFunction` |
| `Order/IntervalClass.lean` | interval classes on a lattice: the saturation closure operator, the radical, the nested formula, transport, the socle iteration | root (`IntervalClass`) |
| `RepresentationTheory/Quiver/Kronecker/HarderNarasimhan.lean` | slope and charge functions on subrepresentations, existence, the two sides of a wall, the HN filtrations of the rigid representation | `Quiver.Kronecker` |
| `Order/Valuation.lean` | valuations on a lattice: modularity, maximizers, Topkis's theorem, the chain lemma | `Order` |
| `Order/HarderNarasimhan/Polytope.lean` | the HN polytope, with a vertical edge | `Order.ChargeFunction`, `Order.SlopeFunction` |
| `RepresentationTheory/Quiver/Kronecker/Preprojective.lean` | representations of the doubled Kronecker quiver: preprojective relations, nilpotence, morphisms, isomorphisms, subrepresentations, dimension vectors, restrictions, quotients, subquotients, kernels and images | `Quiver.Kronecker` |
| `RepresentationTheory/Quiver/Kronecker/Ext.lean` | `Ext¹` by the standard complex, extensions as cocycles, the injection into `Ext¹(N, N)`, the dimension of `Ext¹` and Mukai's inequality | `Quiver.Kronecker` |
| `RepresentationTheory/Quiver/Kronecker/IncomingFlag.lean` | a rigid wall object is determined by its incoming flag, from the open-orbit input | `Quiver.Kronecker` |
| `RepresentationTheory/Quiver/Kronecker/Budget.lean` | the Mukai budget lemma in the quiver model: `e = dim Ext¹` invariant under isomorphism, even, Riemann–Roch, superadditive along flags and HN filtrations | `Quiver.Kronecker` |
| `RepresentationTheory/Quiver/Kronecker/TwoExtensions.lean` | the exact endomorphism count and the one-copy lemma; the wall group that carries the point: classification and table of HN quotients; the rank-one form with one copy of a spherical simple | `Quiver.Kronecker` |
| `LinearAlgebra/Dual/PairOrbit.lean` | the splitting `V ≃ k × ker φ`; `GL(V)` is transitive on pairs `(φ, w)` of a nonzero functional and a nonzero vector it kills | `LinearMap` |
| `RepresentationTheory/Quiver/Kronecker/OneCopyClassification.lean` | semirigid wall objects with one copy of a spherical simple: the decomposition `M_α ⊕ S^{p-2}`, its converse, and the isomorphism class determined by the line of the classes | `Quiver.Kronecker` |
| `RepresentationTheory/Quiver/Kronecker/TwoCopyExclusion.lean` | no semirigid wall object with two copies of each simple: `dim End ≥ 2` at dimension vector `(2, 2)`; exchanging the vertices; socle and top of a nilpotent representation | `Quiver.Kronecker` |
| `RepresentationTheory/Quiver/Kronecker/HomProfile.lean` | relabelling the arrows; the profile `dim Hom(A, -)` and its translates | `Quiver.Kronecker` |
| `RepresentationTheory/Quiver/Kronecker/FibreFunctorProfile.lean` | `Ext²` of the standard complex and its dimension; the fibre-functor profile of `RHom(A, -)` | `Quiver.Kronecker` |
| `RepresentationTheory/Quiver/Kronecker/Radical.lean` | the saturation and radical of the representations supported at vertex zero; the top HN step as a radical | `Quiver.Kronecker` |
| `RepresentationTheory/Quiver/Kronecker/RigidRep.lean` | the rigid representation of dimension `(g², g)` with arrows in both directions | `Quiver.Kronecker` |
| `RepresentationTheory/Quiver/Preprojective/Basic.lean` | representations of the double of a quiver with loops: preprojective relations, nilpotence, morphisms, isomorphisms, subrepresentations, dimension vectors, restrictions, quotients, subquotients, charge functions and HN filtrations | `Quiver.Preprojective` |
| `RepresentationTheory/Quiver/Preprojective/CrawleyBoevey.lean` | the standard complex and `Ext¹`, the duality of its differentials, Crawley-Boevey's formula, Riemann–Roch, bricks, invariance of `e` | `Quiver.Preprojective` |
| `RepresentationTheory/Quiver/Preprojective/Budget.lean` | extensions, Mukai's inequality, a subrepresentation as an extension, the budget along Hom-orthogonal flags | `Quiver.Preprojective` |
| `RepresentationTheory/Quiver/Preprojective/Kronecker.lean` | the wall quiver of two stable objects; the Kronecker files as its case without loops; the wall that carries the point, with its loop | `Quiver.Preprojective` |
| `RepresentationTheory/Quiver/Preprojective/WallModel.lean` | `FormalWallHypotheses`, `RealizationHypotheses` and the realization constructor | `Quiver.Preprojective` |
| `RepresentationTheory/Quiver/Preprojective/SingleVertex.lean` | the wall of one sphere from real objects: finite-dimensional vector spaces, their subspaces, the realization hypotheses and the formal wall model | `Quiver.Preprojective` |
| `AlgebraicGeometry/Surface/K3/PicardRankOne/Visibility.lean` | punctures, clear sight lines, the lattice arguments of visibility on the cover, the finite search | same |
| `AlgebraicGeometry/Surface/K3/PicardRankOne/VisibilityOnCover.lean` | the lemma "Visibility on the cover" from its inputs | same |
| `Analysis/Complex/Sector.lean` | sectors, the projection onto a ray, the sector budget | `Complex` |
| `Analysis/Complex/PhaseGap.lean` | a ray determines its phase modulo two; the phase gap of finitely many charges at finitely many phases | `Complex` |
| `Topology/Order/Selection.lean` | the selection lemma in increment form | root |
| `LinearAlgebra/Lattice/Mukai/Support.lean` | the support property, Finsler's lemma, signature `(2, n)`, constituents in a sector, the completed square and the root test, the real model of an integral Mukai lattice | `Mukai` |
| `LinearAlgebra/Lattice/Mukai/PhaseGap.lean` | the lattice-gap lemma: finitely many classes of square at least `-2` and bounded charge, and the phase gap of their charges | `Mukai` |
| `AlgebraicGeometry/Surface/K3/PicardRankOne/SupportProperty.lean` | the support property of the central charge in Picard rank one | `AlgebraicGeometry.K3.PicardRankOne` |
| `AlgebraicGeometry/Surface/K3/PicardRankOne/StratumRootSystem.lean` | every stratum is `A₁`: the kernel root systems over `ℤ` and `ℚ` at a puncture and their bases | `AlgebraicGeometry.K3.PicardRankOne` |
| `AlgebraicGeometry/Surface/K3/EllipticWithSection/SupportProperty.lean` | the root test and the support property at the curve wall | `AlgebraicGeometry.K3.EllipticWithSection` |
| `AlgebraicGeometry/Surface/K3/EllipticWithSection/PhaseGap.lean` | the lattice gap at the curve wall | `AlgebraicGeometry.K3.EllipticWithSection` |
| `LinearAlgebra/RootSystem/Spherical.lean` | root pairings of `(-2)`-vectors, definite lattices, Cartan matrices of a base, the kernel root system, the root system over `ℚ` | `RootPairing` |
| `LinearAlgebra/RootSystem/Stratum.lean` | the root system of a stratum over `ℚ` on `ℚ ⊗ (ker Z ∩ N)`; bases and Cartan matrices of `A₁` pairings and strata | `RootPairing` |
| `LinearAlgebra/Lattice/Arrangement.lean` | positive periods, the stratum trichotomy, two roots | `Mukai` |
| `LinearAlgebra/Lattice/Arrangement/Lorentzian.lean` | two roots with pairing above two: the orthogonal complement of their span has one positive direction | `Mukai` |
| `AlgebraicGeometry/Surface/K3/EllipticWithSection/KernelRootSystem.lean` | signature `(2, 2)`, an `A₁` stratum and its punctured support bound, roots that meet and roots that do not | `AlgebraicGeometry.K3.EllipticWithSection` |
| `AlgebraicGeometry/Surface/K3/EllipticWithSection/StratumRootSystem.lean` | the bases of the `A₁` stratum over `ℤ` and `ℚ`; its Cartan matrix | `AlgebraicGeometry.K3.EllipticWithSection` |
| `Analysis/Complex/UpperHalfPlane/ProjectiveModel.lean` | the projective model `(Re z, \|z\|²)` of the half-plane, whose geodesics are straight | `UpperHalfPlane` |
| `Analysis/Complex/QuadraticModulus.lean` | the polynomial modulus lemma: square-root approximation, forward differences, Gregory–Newton, the monic quadratic | `Polynomial` |
| `LinearAlgebra/Lattice/Mukai/ProjectiveModel.lean` | the signature, negative cone and projective model of the Mukai lattice; reverse Cauchy–Schwarz | `MukaiVector` |
| `AlgebraicGeometry/Surface/K3/EllipticWithSection/Lattice.lean` | the Mukai lattice of an elliptic K3 with a section and the classes of its curve wall | `AlgebraicGeometry.K3.EllipticWithSection` |
| `AlgebraicGeometry/Surface/K3/EllipticWithSection/CurveWall.lean` | the charge of the curve wall, its phases, and the parity argument for the tails | same |
| `AlgebraicGeometry/Surface/K3/EllipticWithSection/MukaiCharge.lean` | the charge of the curve wall as a Mukai charge and a `GL₂⁺(ℝ)`-translate of an exponential charge | same |
| `AlgebraicGeometry/Surface/K3/EllipticWithSection/Braid.lean` | the `A₂` configuration `𝒪_X[1]`, `𝒪_C` on classes: the Artin group acting on the Mukai lattice through the Coxeter group | same |
| `GroupTheory/Coxeter/ArtinGroup.lean` | the Artin group of a Coxeter matrix, the pure Artin group, braid relations from one conjugation identity per edge | `CoxeterMatrix` |
| `GroupTheory/Coxeter/GeometricRepresentation.lean` | the reflection representation of `W(ofExt e)`, root-positive words, lengths from a finite root set, explicit longest words of `A_n` | `CoxeterMatrix`, `BilinearForm`, `CoxeterSystem` |
| `GroupTheory/Coxeter/Deletion.lean` | the first sign change, deletion, positivity of minimal words and the trivial stabilizer, for words of reflections | `BilinearForm` |
| `GroupTheory/Coxeter/RealRoots.lean` | real roots of the root form of a loopless quiver, sign coherence from semidefiniteness, descent on the height | `CoxeterMatrix` |
| `AlgebraicGeometry/Surface/K3/EllipticWithSection/WeylGallery.lean` | the `A₂` Weyl gallery on classes: root-positive reduced words of `w₀` on `v(𝒪_X[1])`, `v(𝒪_C)` | `AlgebraicGeometry.K3.EllipticWithSection` |
| `AlgebraicGeometry/Surface/K3/EllipticWithSection/FramedMultiplier.lean` | the framed multiplier of the curve wall and of a point, from the classes of the lattice | same |
| `AlgebraicGeometry/Surface/K3/EllipticWithSection/AffineWeyl.lean` | the fundamental cycle of the curve wall, its alcove, affine Weyl group, translation lattices and length-zero element | same |
| `AlgebraicGeometry/Surface/K3/EllipticWithSection/LengthZeroGroup.lean` | the length-zero group `ℤ/2` and the Coxeter group `Ã₁` of the curve wall | same |
| `AlgebraicGeometry/Surface/K3/EllipticWithSection/BPS.lean` | the BPS interface of the curve wall from its `Ext`-quiver and the Kac polynomials of that quiver | same |
| `RingTheory/IntegralClosure/Away.lean` | integrality over `ℤ[1/N]`, integrally closed; the arithmetic core of the S-unit theorem | root |
| `RingTheory/IntegralClosure/Specialization.lean` | one `N` for a finitely generated subring of a field of characteristic zero, by Zariski's lemma and lying over | root |
| `LinearAlgebra/Matrix/UnitSpectrum.lean` | eigenvalues integral over the entries, inverse moduli, the unit test | `Matrix` |
| `NumberTheory/SUnitSpectral.lean` | the S-unit theorem for spectral moduli of a matrix semigroup and its family form | `Matrix` |
| `LinearAlgebra/Matrix/SingularReduction.lean` | spectral radius of a restriction; invertible letter matrices from singular ones | `Module.End`, `Matrix` |
| `RingTheory/Polynomial/DoublePlaneCubics.lean` | the cubics `P_s` and block matrices `M_s` of the double plane: real roots, irreducibility, primes, units | `Polynomial.DoublePlane` |
| `AlgebraicGeometry/Surface/K3/PicardRankOne/LetterObstruction.lean` | no fixed letter matrices for `T₀^{±1}, T₁^{±1}, T₃^{±1}`; the unit test | `AlgebraicGeometry.K3.PicardRankOne.DoublePlane` |
| `Analysis/Topical/Basic.lean` | monotone homogeneous maps, the cycle time, other starts, sub-solutions | `MonotoneHomogeneous` |
| `Analysis/Topical/CollatzWielandt.lean` | Collatz–Wielandt bounds, the ratio test, the linear case | `MonotoneHomogeneous` |
| `Analysis/Topical/MaxOperator.lean` | the dual maximum operator over words; the forward operator and the joint spectral radius | root |
| `Analysis/Topical/PiecewiseLinear.lean` | piecewise-linear integral models, `EigAtRate`, algebraicity of the rate | `PLModel` |
| `Analysis/Topical/Nonexpansive.lean` | Thompson and Hilbert nonexpansiveness on parts of the orthant | `MonotoneHomogeneous` |

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
| `Triangulated/StabilityCondition/Symmetry/Autoequivalence/Slicing/Artin.lean` | Artin groups acting by autoequivalences; braid relations from the conjugation formula (`TwistConjugation`) |
| `Triangulated/StabilityCondition/WallCrossing.lean` | carrying the point once across a wall and a letter |
| `Triangulated/StabilityCondition/Budget.lean` | `MukaiBudget` (`e : C → ℕ`, invariant under isomorphism, Mukai's lemma: Bayer–Bridgeland, arXiv:1310.8266, Lemma 2.5) and the Mukai budget lemma along Hom-orthogonal towers and HN filtrations |
| `Triangulated/StabilityCondition/Tower.lean` | carrying the point once as at most once plus existence; a path of walls (`Leg`); `TowerHypotheses` and the tower theorem, also through the budget |
| `Triangulated/StabilityCondition/SplitTower.lean` | the slice fields, transport steps and paths, `SplitTowerHypotheses` and the split tower theorem; the old inputs give the new ones |
| `Triangulated/StabilityCondition/WallStep.lean` | a named wall, the sphere types of each phase and their Gram matrix; a lost carrier forces an isotropic sphere sum at one phase; the split tower theorem over paths of named walls |
| `Triangulated/StabilityCondition/WallAlgorithm.lean` | HN filtrations with nonzero factors; the outgoing clause for a wall group without the point, and a wall crossing from the slice fields; on the rank-free form, a wall crossing from existence statements, the carrier clause from a named wall, the factors after a wall, and the transport step of a grouping and a named wall |
| `Triangulated/SerreFunctor/TwoCalabiYau.lean` | `TwoCYHypotheses`: Hom-finiteness, Serre functor `≅ ⟦2⟧`, Mukai's lemma, evenness of `e`, Riemann–Roch for simple objects (Mukai's sign) |
| `Triangulated/StabilityCondition/Weak/Foundation/Slicing/Evaluation.lean` | the evaluation lemma, as far as it holds in any slicing |
| `Triangulated/StabilityCondition/Weak/Foundation/Slicing/Coreflection.lean` | truncations of a slicing as coreflections; the top quotient of the evaluation lemma as a radical |
| `Triangulated/SerreClosure.lean` | the Serre preimage of a homological functor as a thick subcategory; twist words modulo a thick subcategory (the Verdier form) and on objects; the Serre-preimage theorem |
| `Triangulated/CentralAction.lean` | central annihilators along twist words: `z`-linear letters, vanishing on HN factors and truncations, `CentralAnnihilatorHypotheses` (the linearity criterion as a field) and its instance on `D(R-Mod)` |
| `Triangulated/StabilityCondition/Weak/Foundation/Slicing/TStructure.lean` | the half-open predicate `P((a, a+1])`, the bounded t-structure of a slicing and its heart |
| `Triangulated/StabilityCondition/Weak/Foundation/Slicing/Heart.lean` | the heart `P((a, a+1])` as an abelian category; its torsion pairs; `P(a+1)` as a Serre class given a charge; hearts in degrees `[0, 1]` and the heart at fixed `Im Z` |
| `Triangulated/StabilityCondition/Weak/Foundation/Slicing/HeartRadical.lean` | the radical of `P(a+1)` in the heart without a chain condition; interval classes and the charge function `(Im Z, -Re Z)` on the subobjects of heart objects |
| `Triangulated/StabilityCondition/Weak/Foundation/Slicing/ExtensionClosure.lean` | the `(≥ t, < t)` split; the four phase cuts as orthogonals, closed under extensions |
| `Triangulated/StabilityCondition/Weak/Foundation/Slicing/ConeHN.lean` | the cut criterion for cones |
| `Triangulated/StabilityCondition/Weak/Foundation/Slicing/ConeHNStrict.lean` | the cut criterion for cones at a strict cut `(> t, ≤ t)`; the interval below a phase bound and the heart |
| `Triangulated/StabilityCondition/Weak/Foundation/Slicing/DivisibilityObstruction.lean` | the divisibility obstruction for a cone on a semistable object; truncations of finite biproducts |
| `Triangulated/StabilityCondition/Foundation/OneUnitOfWeight.lean` | the rotated imaginary charge and the one-unit-of-weight lemma |
| `Triangulated/StabilityCondition/WeylTilt.lean` | lower tilts, simple objects and torsion classes as properties of objects; `WeylGalleryHypotheses` and the Weyl-gallery induction on root-positive words |
| `Triangulated/StabilityCondition/WeylTilt/Slicing.lean` | simple objects, phase-cut torsion classes and their lower tilts at `P((a, a+1])`; the charge cone; the Weyl-gallery hypotheses at `P((0, 1])` |
| `Triangulated/StabilityCondition/Weak/Foundation/Slicing/ShortStep.lean` | the short-step stability test: closed intervals by Hom vanishing, phase closeness, stable objects, the Im-form test |
| `Triangulated/StabilityCondition/Mass.lean` | the mass, HN sums up to zero factors, invariances, the split identity, `m ≥ \|Z\|`, Ikeda subadditivity as a predicate, the `2m(D)` lemma |
| `Triangulated/StabilityCondition/MassAdditivity.lean` | partial charges and their jumps, the mass from the jumps, flag reassembly gives additive mass |
| `Triangulated/StabilityCondition/StabilitySpace.lean` | `StabilitySpaceHypotheses`: covering, metric bound, support, action, subadditivity; equivariant mass, the path layer, σ-independent growth |
| `Triangulated/StabilityCondition/IntersectingWalls.lean` | intersecting ordinary walls: phase gaps, the `τ`-HN factors near `σ` stay in `P_σ(φ)`, the greedy rule, the rotated charge function on the subobjects in the heart |

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
