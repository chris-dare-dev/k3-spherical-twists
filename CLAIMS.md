# Claims and records

This page lists what the [guide](GUIDE.md) says the code computes, claim by claim, and, in the last column of each table, what the records of the scheduler in [data/records/](data/records/) say about it.

Contents: [Tasks and records](#tasks-and-records) · [Cohomology of the sheaves of short words](#cohomology-of-the-sheaves-of-short-words) · [Euler characteristics of pairs](#euler-characteristics-of-pairs) · [The marked curve on a quartic](#the-marked-curve-on-a-quartic) · [Twists realized as complexes](#twists-realized-as-complexes) · [HN arrows in a supplied window](#hn-arrows-in-a-supplied-window) · [What the tasks do not cover](#what-the-tasks-do-not-cover)

## Tasks and records

The tables below are generated: their rows are in [data/claims/claims.toml](data/claims/claims.toml), and `make tables` writes them here. Every column but the last is the row as it was written by hand.

The last column, *Run under the scheduler*, is computed from the records in [data/records/](data/records/). A claim that a program can check has tasks: computations with one answer each, defined by the batch files in [data/batches/](data/batches/) and run by the scheduler under time and memory limits ([GUIDE.md](GUIDE.md#running-a-batch)). The column reads:

- **all N tasks ok**, when every task of the claim has a record and each computed value agrees with the predicted one, with the day and the commit of the records;
- the count of tasks by status otherwise: `ok`, `mismatch`, `unsupported` (there is no method for the task), `timeout`, `memory`, `blocked` (a task it depends on gave no output), `error`, `crashed`, `stale` for a record of a task that has changed since it was computed (another surface, another object, another predicted value; such a record supports nothing), and `not re-run` for tasks without a record;
- **not re-run**, when no task of the claim has a record: nothing in this repository then says what its tasks compute to;
- **no task**, with the reason, when nothing in the batch files computes the claim.

"ok" records agreement with a task's prediction on its specified input. The K3 surface records use the field with 32003 elements and seed 1. The local arrow records use the polynomial ring in two variables over the rationals. Every task, prediction and record appears in the [record index](data/claims/RECORDS.md).

A record in [data/records/](data/records/) was computed by this repository at the commit it names, from a working tree without uncommitted changes. `make record BATCH=data/batches/NAME.toml` runs a batch and copies its records there; [src/batch/claims/adopt.py](src/batch/claims/adopt.py) says what is copied and what is refused. The scheduler's own rule for reusing a record is stricter than the tables': it computes a task again whenever the code has changed, while a committed record stays the record of its task and names the commit that computed it.

## Cohomology of the sheaves of short words

The sheaves are those of the table at the top of the [guide](GUIDE.md#what-this-is-about). The surface for d = 2, 3, 4 is a quartic, the intersection of a quadric and a cubic, and the intersection of three quadrics. Batches: `invariants` (the first five rows), `invariants-slow` (the last two).

<!-- BEGIN GENERATED sheaves: make tables -->
| Claim | Predicted, with n = d + 2 | Surfaces | Run under the scheduler |
|---|---|---|---|
| hⁱ(O), hⁱ(O(H)), hⁱ(O(−H)) | (1, 0, 1), (n, 0, 0), (0, 0, n) | d = 2, 3, 4 | all 9 tasks **ok**; 2026-11-19, `8014a21`; [tasks](data/claims/RECORDS.md#claim-line-bundles) |
| hⁱ(I_x), hⁱ(I_x(−H)), hⁱ(I_x(H)); the ideal of x has n − 1 generators | (0, 0, 1), (0, 1, n), (n − 1, 0, 0); n − 1 | d = 2, 3, 4 | all 12 tasks **ok**; 2026-11-19, `8014a21`; [tasks](data/claims/RECORDS.md#claim-ideal-of-the-point) |
| rank M_H, hⁱ(M_H), hⁱ(M_H(−H)) | n − 1, (0, 0, n), (0, 1, n² − 1) | d = 2, 3, 4 | all 9 tasks **ok**; 2026-11-19, `8014a21`; [tasks](data/claims/RECORDS.md#claim-m-h) |
| rank M_x, hⁱ(M_x), hⁱ(M_x(−H)) | n − 2, (0, 0, n − 1), (0, 0, n² − n − 1) | d = 2, 3, 4 | all 9 tasks **ok**; 2026-11-19, `8014a21`; [tasks](data/claims/RECORDS.md#claim-m-x) |
| rank Q, hⁱ(Q) | n − 1, (n² − 1, 1, 0) | d = 2, 3, 4 | all 6 tasks **ok**; 2026-11-19, `8014a21`; [tasks](data/claims/RECORDS.md#claim-q) |
| Four of the above again, as Ext groups of sheaves: Extⁱ(O, O(H)), Extⁱ(O(H), O), Extⁱ(O(H), M_H), Extⁱ(M_x, O_x) | (n, 0, 0), (0, 0, n), (0, 1, n² − 1), (n − 2, 0, 0) | d = 2 | all 4 tasks **ok**; 2026-11-19, `8014a21`; [tasks](data/claims/RECORDS.md#claim-again-as-ext) |
| Extⁱ(F, F) for F = I_x(H), M_H, M_x | (1, 2, 1), (1, 0, 1), (1, 2, 1) | d = 2 | all 3 tasks **ok**; 2026-11-19, `8014a21`; [tasks](data/claims/RECORDS.md#claim-self-ext) |
<!-- END GENERATED sheaves -->

## Euler characteristics of pairs

For two sheaves E, F of the catalogue the task computes the three dimensions of Extⁱ(E, F) and compares their alternating sum with −⟨v(E), v(F)⟩. Only that sum is predicted; the dimensions are recorded and compared with nothing. A pair of two sheaves that are not locally free has no method and ends `unsupported`. Batches: `ext-table` (every pair on the four surfaces), `quartic-sample` (25 pairs on the quartic), `limits-demo` (6 pairs on the quartic).

<!-- BEGIN GENERATED pairs: make tables -->
| Claim | Surface | Ordered pairs | Run under the scheduler |
|---|---|---|---|
| χ(E, F) = −⟨v(E), v(F)⟩ for the sheaves E, F of the catalogue | quartic, d = 2 | 22 × 22 = 484 | tasks: ok 24; unsupported 1; not re-run 459 (of 484); 2026-11-19, `8014a21`; [tasks](data/claims/RECORDS.md#claim-pairs-d2) |
| the same | quadric and cubic, d = 3 | 22 × 22 = 484 | **not re-run**: 484 tasks in `ext-table`, no record; [tasks](data/claims/RECORDS.md#claim-pairs-d3) |
| the same, with the rank 2 bundle of class (2, 1, 2) and its twists in the catalogue | d = 3 with the quadric x₀x₁ + x₂x₃ + x₄² | 26 × 26 = 676 | **not re-run**: 676 tasks in `ext-table`, no record; [tasks](data/claims/RECORDS.md#claim-pairs-d3-special) |
| the same | three quadrics, d = 4 | 22 × 22 = 484 | **not re-run**: 484 tasks in `ext-table`, no record; [tasks](data/claims/RECORDS.md#claim-pairs-d4) |
<!-- END GENERATED pairs -->

## The marked curve on a quartic

Batch: `marked-quartics`.

<!-- BEGIN GENERATED marked: make tables -->
| Claim | Predicted | Surfaces | Run under the scheduler |
|---|---|---|---|
| hⁱ(O_C) and Extⁱ(O_C, O_C) for the marked curve C, with C² = −2 | (1, 0, 0) and (1, 0, 1) | a quartic with a line, a quartic with a conic | all 4 tasks **ok**; 2026-11-19, `8014a21`; [tasks](data/claims/RECORDS.md#claim-marked-curve) |
<!-- END GENERATED marked -->

## Twists realized as complexes

Each of the first five rows is one dependent batch: a task builds the marked quartic, a task realizes the cone and stores it, and the remaining tasks load both and compute. The predicted dimensions are written in the batch file with the hypotheses they rest on. The fourth and fifth batches also store the two maps of the cone, and their last task rebuilds the cone from them before it applies the inverse twist or the second forward twist. The five batches use the same task ids for different objects; [data/claims/RECORDS.md](data/claims/RECORDS.md) names the batch of each row.

<!-- BEGIN GENERATED twists: make tables -->
| Claim | Predicted | Where | Run under the scheduler |
|---|---|---|---|
| The cone that realizes T_O(O(H)) has the cohomology of M_H[1] and its Ext groups to O | cohomology (0, 0, 4) in degrees −1 to 1; Ext to O (4, 0, 0) in degrees 1 to 3 | the quartic with a line; `data/batches/resumable-quartic.toml` | all 4 tasks **ok**; 2026-11-19, `43ee811`, `8014a21`; [tasks](data/claims/RECORDS.md#claim-twist-of-the-hyperplane-bundle) |
| The cone that realizes T_O(O_x) has the cohomology of I_x[1] and its Ext groups to O | cohomology (0, 0, 1) in degrees −1 to 1; Ext to O (1, 0, 0) in degrees 1 to 3 | the quartic with a line; `data/batches/resumable-quartic-point.toml` | all 4 tasks **ok**; 2026-11-19, `43ee811`, `8014a21`; [tasks](data/claims/RECORDS.md#claim-twist-of-the-point) |
| The cone that realizes T_O(O(−H)) has hypercohomology in degree 3 only | dimension 4 in degree 3, zero in degrees −1 to 2 | the quartic with a line; `data/batches/resumable-quartic-hypercohomology.toml` | all 3 tasks **ok**; 2026-11-19, `43ee811`, `8014a21`; [tasks](data/claims/RECORDS.md#claim-twist-of-the-dual-hyperplane-bundle) |
| The word {T_O, T_O⁻¹} applied to O(−H) is realized from the stored cone of T_O(O(−H)) and its two stored maps, and the result is quasi-isomorphic to O(−H) as a complex of sheaves | a quasi-isomorphism of sheaves; the Serre pairing has rank 4 | the quartic with a line; `data/batches/resumable-quartic-inverse.toml` | all 3 tasks **ok**; 2026-11-19, `43ee811`; [tasks](data/claims/RECORDS.md#claim-inverse-cancellation) |
| The word {T_O, T_O} applied to O(−H) is realized from the same stored cone and maps, as a second cone with the Mukai class of O(−H) | sheaf homology O(−H), O⁴, O⁴ in degrees 0, 1, 2 | the quartic with a line; `data/batches/resumable-quartic-second-forward.toml` | all 3 tasks **ok**; 2026-11-19, `43ee811`; [tasks](data/claims/RECORDS.md#claim-second-forward-twist) |
| The word {T_O, T_{O(H)}⁻¹} on O_x is realized from the stored point cone, via the comparison with I_x[1] | Mukai class (2,3H,9); sheaf homology O(H) and coker(I_x → O(H)⁴) in degrees −1 and 0 | the quartic with a line; `data/batches/resumable-quartic-mixed-point.toml` | tasks: ok 2; not re-run 1 (of 3); 2026-11-19, `43ee811`, `8014a21`; [tasks](data/claims/RECORDS.md#claim-class-of-a-word) |
| On the Fermat quintic threefold over ZZ/101: hⁱ(O) = (1, 0, 0, 1), and the twist of the marked point about O is realized with numerical class (−1, 1) | (1, 0, 0, 1); (−1, 1) | the quintic threefold | no task: a test of the package (`src/macaulay2/K3Twists/tests/quintic.m2`, run by `make test`); it leaves no record |
<!-- END GENERATED twists -->

## HN arrows in a supplied window

Each task starts with the chain map and the homological degree of the strict upper cut. The cone computation pulls back the top cycles from the cone on the lower inputs. The fibre computation cuts the bottom quotient from the fibre on the upper inputs. The test compares the resulting inclusion with a separately constructed arrow. A commuting square and two quasi-isomorphisms identify the arrows over the specified output. [Implementation](src/macaulay2/K3Twists/derived/cut-arrows.m2) · [Regression fixture](src/macaulay2/K3Twists/tasks/hn-arrows.m2) · [Issue #99](https://github.com/chris-dare-dev/k3-spherical-twists/issues/99)

For the six local examples the supplied geometric window puts all punctual sheaves at phase one and their shifts by −1 at phase zero. The strict cut is at zero. Kernels, cokernels and maps are computed on presented modules. The two quartic tasks use the actual structure-sheaf evaluation and coevaluation. Their strict cut is at one, with the point ideal sequence supplied as exact in the geometric heart. The records check chain algebra with these phase inputs. Determining a marked stability condition or a window heart from a surface equation is a separate problem.

<!-- BEGIN GENERATED hn-arrows: make tables -->
| Chain maps | Predicted result | Model | Run under the scheduler |
|---|---|---|---|
| Zero or tangent map k[−1] → k, with an unmapped k[−1] target summand | Upper summand inclusions of k ⊕ k and Dᵤ, each of length 2 with lower length 1. Their radicals have lengths 0 and 1. | ℚ[u,v] at the origin | **not re-run**: 2 tasks in `hn-arrows`, no record; [tasks](data/claims/RECORDS.md#claim-punctual-cone-arrows) |
| Socle inclusion k → fib(Dₐ → k → Dᵦ) over the given fibre | Kernel and lower quotient each have length 1. Oriented boundary coefficients for uu, uv, vu, vv are 0, +1, −1, 0. | ℚ[u,v] at the origin | **not re-run**: 4 tasks in `hn-arrows`, no record; [tasks](data/claims/RECORDS.md#claim-punctual-fibre-arrows) |
| T_O(kₓ) and T_O⁻¹(Iₓ[1]) at the strict cut above phase 1 | Iₓ[1] includes quasi-isomorphically into the evaluation cone. The inverse fibre projects onto kₓ by a quasi-isomorphism and has zero upper cut. | quartic with a line over 𝔽₃₂₀₀₃ | **not re-run**: 2 tasks in `hn-arrows`, no record; [tasks](data/claims/RECORDS.md#claim-quartic-point-cut-arrows) |
<!-- END GENERATED hn-arrows -->

Run `make run BATCH=data/batches/hn-arrows.toml` from the repository root. Each record includes the module presentations, differentials, input map, computed and reference inclusions, the two comparison maps, and the projection onto the identified lower quotient. The four fibre records also give the first Koszul lift in the ordered parameters $u,v$. [Batch and expected values](data/batches/hn-arrows.toml) · [Recorded matrices](data/records/hn-arrows/results.jsonl)

## What the tasks do not cover

- **Stability.** Computing the phases or testing semistability in an arbitrary geometric heart remains outside the recorded calculations.
- **Other surfaces.** The K3 batch records use one seed and characteristic for each specified model. Their Picard ranks are undetermined.
- **The dimensions of Ext for a pair.** Only the Euler characteristic of a pair is predicted.
- **Pairs of large rank.** The time of a pair grows quickly with the ranks of the two sheaves; `data/batches/ext-table.toml` gives a pair between a quarter of an hour and four hours, by the rank of the sheaf Hom(E, F), and a pair that needs more ends `timeout`. The table of pairs says how many of its tasks have a record.
- **Longer words.** The recorded complexes cover the twists and two-letter words above. A general word with a numerically known image still needs its derived evaluation and coevaluation maps for an arrow calculation.
- **The quintic threefold row.** It is covered by a package test in `make test`.
- **The synthetic tasks.** `data/batches/limits-demo.toml` has two tasks that are stopped on purpose, one at its time limit and one at its memory limit. They show what such records look like, and they count for no claim.
