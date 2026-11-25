# k3-spherical-twists

<!--
  Badges: the GitHub-dynamic ones (CI, last commit) render once the repo is
  public. The static ones always render.
-->
[![CI](https://github.com/chris-dare-dev/k3-spherical-twists/actions/workflows/tests.yml/badge.svg?branch=main)](https://github.com/chris-dare-dev/k3-spherical-twists/actions/workflows/tests.yml)
[![Macaulay2](https://img.shields.io/badge/Macaulay2-1.25-blue.svg)](https://macaulay2.com)
[![Python](https://img.shields.io/badge/python-3.11%2B-blue.svg)](pyproject.toml)
[![Lean](https://img.shields.io/badge/Lean-4.36-blue.svg)](src/lean/)
[![License: MIT](https://img.shields.io/badge/license-MIT-green.svg)](LICENSE)
[![Status](https://img.shields.io/badge/status-not%20peer%20reviewed-orange.svg)](#what-this-does-not-show)
[![Last commit](https://img.shields.io/github/last-commit/chris-dare-dev/k3-spherical-twists.svg)](https://github.com/chris-dare-dev/k3-spherical-twists/commits)

**Macaulay2 checks of spherical-twist computations on explicit K3 surfaces,** plus a small scheduler that runs them in batches under time and memory limits, and Lean proofs of the statements that Lean can check today.

For a K3 surface X with ample class H, H² = 2d, the objects O and O(H) are spherical, and each gives a twist T_O, T_{O(H)}. The images of a point's skyscraper sheaf under short words are built from a few sheaves (I_x, M_H, M_x, Q). The study predicts their cohomology as formulas in n = d + 2; this code builds random surfaces over a prime field and compares.

| d | n | Surface |
|---|---|---|
| 2 | 4 | quartic in P³ |
| 3 | 5 | quadric and cubic in P⁴ |
| 4 | 6 | three quadrics in P⁵ |

## Try it

Needs Macaulay2 1.25, Python 3.11+ and Linux; or build the container (`docker build -t k3-twists-m2 .`).

```bash
make test     # package and scheduler tests, about two minutes
make smoke    # 45 tasks in about ten seconds: predicted vs computed invariants
```

```bash
make lean-deps && make lean   # the Lean proofs; needs elan
```

```m2
needsPackage "K3Twists"
sheafInvariants k3Surface 2   -- computed and predicted h^i of the sheaves, on a quartic
```

For a surface, a word, a pair of sheaves or a batch of your own, start from the files in [data/examples/](GUIDE.md#examples-to-start-from).

## What is in it

| | |
|---|---|
| [src/macaulay2/](src/macaulay2/) | The Macaulay2 package K3Twists: surfaces, sheaves, catalogue, invariants, twists, Ext tables |
| [src/batch/](src/batch/) | Runs the package's computations in batches under time and memory limits, keeps a record of each, and writes the claim tables from them |
| [src/lean/](src/lean/) | Lean 4 proofs: lattice and charge identities, the integers of rigid walls, and the point-mass corollary from its stated inputs |
| [CLAIMS.md](CLAIMS.md) | Each claim, and what the committed records say about it |
| [GUIDE.md](GUIDE.md) | Full reference: what is computed, batches, records, design, layout |

## What this does not show

It computes sheaf cohomology, not Bridgeland stability. The Lean proofs take the geometric inputs of the point-mass corollary (Orlov's generation theorem, Bridgeland's metric, the entropy formula, two lemmas of the study) as hypotheses and check that the corollary follows from them. The surfaces are over finite fields with undetermined Picard rank, only words of length at most two are covered, and agreement confirms the short exact sequences and the code, not the theory as a whole. The idea is mine; Claude was used extensively for derivations, code and drafting. Nothing here has been independently reviewed.
