# k3-spherical-twists

Macaulay2 code that checks, on explicit K3 surfaces, numbers that come out of a study of words in two spherical twists.

## What this is about

Let X be a K3 surface with an ample class H, H² = 2d, and put n = d + 2 = h⁰(O(H)). The structure sheaf O and the line bundle O(H) are spherical objects of the derived category of X, and each gives an autoequivalence, the spherical twist T_O or T_{O(H)}. The study behind this repository describes what words in these two twists do to the skyscraper sheaf O_x of a point.

For short words the images are built from a few sheaves that can be written down:

| Sheaf | Definition | Where it occurs |
|---|---|---|
| I_x | ideal sheaf of the point x | T_O(O_x) = I_x[1], T_{O(H)}(O_x) = I_x(H)[1] |
| M_H | kernel of H⁰(O(H)) ⊗ O → O(H) | T_O(O(H)) = M_H[1] |
| M_x | kernel of H⁰(I_x(H)) ⊗ O → I_x(H) | T_O T_{O(H)}(O_x) = M_x[2] |
| Q | cokernel of O → H⁰(O(H))* ⊗ O(H) | T_{O(H)}⁻¹(O) = Q[−1] |

The study predicts the cohomology of these sheaves as formulas in n. This code computes the same numbers on a surface and compares.

## What is computed

`k3Surface d` builds a smooth K3 surface of degree 2d through the point x = (1:0:…:0), over a prime field, as a random complete intersection:

| d | n | Surface |
|---|---|---|
| 2 | 4 | a quartic in P³ |
| 3 | 5 | a quadric and a cubic in P⁴ |
| 4 | 6 | three quadrics in P⁵ |

`sheafInvariants` returns, for one surface, computed and predicted values of:

| Invariant | Predicted |
|---|---|
| hⁱ(O), hⁱ(O(H)), hⁱ(O(−H)) | (1, 0, 1), (n, 0, 0), (0, 0, n) |
| hⁱ(I_x), hⁱ(I_x(−H)), hⁱ(I_x(H)) | (0, 0, 1), (0, 1, n), (n − 1, 0, 0) |
| rank M_H, hⁱ(M_H), hⁱ(M_H(−H)) | n − 1, (0, 0, n), (0, 1, n² − 1) |
| rank M_x, hⁱ(M_x), hⁱ(M_x(−H)) | n − 2, (0, 0, n − 1), (0, 0, n² − n − 1) |
| rank Q, hⁱ(Q) | n − 1, (n² − 1, 1, 0) |

The numbers n − 1 and n² − n − 1 are the terms c_1, c_2 of the sequence c_0 = 1, c_{k+1} = n·c_k − c_{k−1} (`chainNumber`).

With `Slow => true` some of these are computed a second time as Ext groups, together with Extⁱ(F, F) for F = I_x(H), M_H, M_x (predicted (1, 2, 1), (1, 0, 1), (1, 2, 1)). Those take minutes on the quartic and are not practical for d = 3, 4.

## Running it

With Macaulay2 installed (version 1.25 was used):

```bash
make test
```

```bash
make invariants D=3
```

```bash
make all-degrees
```

`make test` runs the package's tests (seven tests, about half a minute). `make invariants` prints the table for one surface and exits with status 1 if a computed value differs from the predicted one. `make invariants-slow D=2` adds the Ext groups.

Without a system install, build the container once and run inside it:

```bash
docker build -t k3-twists-m2 .
```

```bash
docker run --rm -v "$PWD":/work -w /work k3-twists-m2 make test
```

The surface is chosen by a seed and a characteristic (`K3SEED`, `K3CHAR` for the scripts; the options `Seed` and `Characteristic` of `k3Surface`). The defaults are seed 1 and the prime 32003.

## Layout

| Path | Content |
|---|---|
| `K3Twists.m2` | the package: surfaces, sheaves, invariants, tests |
| `scripts/run-tests.m2` | runs the tests |
| `scripts/sheaf-invariants.m2` | prints the comparison for one surface |
| `Dockerfile`, `Makefile` | container and targets |

## What this does not show

- It computes sheaf cohomology. It does not test Bridgeland stability, which is what most of the study's statements are about.
- The surfaces are over finite fields and their Picard rank is not determined. The numbers checked here do not depend on the Picard rank.
- Only the sheaves above are covered, which correspond to words of length at most two. Images of longer words are complexes, and building them is the next thing to add.
- The predicted values follow from short exact sequences; agreement confirms those computations and the code, not the theory as a whole.

## A note on method

The idea for this project and its direction are my own. AI tools (Anthropic's Claude) were used extensively in carrying it out, including the derivations, code, computations and drafting. The results have not been independently reviewed. If you would like more detail on how the work was done, get in touch.

Chris Dare

## Licence

MIT, see [LICENSE](LICENSE).
