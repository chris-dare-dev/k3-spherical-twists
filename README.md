# k3-spherical-twists

Macaulay2 code that checks, on explicit K3 surfaces, numbers that come out of a study of words in two spherical twists, and a small scheduler that runs such checks in batches under time and memory limits.

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

The surface is determined by d, a seed and a characteristic; the defaults are seed 1 and the prime 32003.

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

`catalogue` lists the sheaves of the study on a surface with their classes (r, c, s), where c is the multiple of H and the pairing is ⟨v, w⟩ = 2d·cc′ − rs′ − r′s: the line bundles O(tH), the ideal sheaves I_x(tH), O_x, the bundles M_H, M_x, their duals and twists, the bundle E_2 (the kernel of sl(V) ⊗ O → V ⊗ O(H), rank n² − n − 1), and M_2H (the kernel of H⁰(O(2H)) ⊗ O → O(2H)). There are 22 sheaves on each surface. For d = 3 the option `SpecialQuadric => true` takes the quadric x₀x₁ + x₂x₃ + x₄²; `mukaiBundle` is then a rank 2 bundle of class (2, 1, 2) with End = (1, 0, 1), and the catalogue has 26 sheaves.

`extTableRow` computes Extⁱ(E, F) for two sheaves of the catalogue as the cohomology of the sheaf Hom(E, F), using Serre duality when F is the locally free one, and compares the Euler characteristic with −⟨v(E), v(F)⟩. The time grows quickly with the ranks: on the quartic a pair of rank 3 bundles takes about 15 seconds, and a pair of rank 11 bundles does not finish in a quarter of an hour.

## Requirements

Macaulay2 (version 1.25 was used) and Python 3.11 or later; the scheduler uses the standard library only. Linux is assumed: the scheduler reads `/proc` and, where `systemd-run --user` is available, uses control groups.

Without a system install, build the container once and run inside it:

```bash
docker build -t k3-twists-m2 .
```

```bash
docker run --rm -v "$PWD":/work -w /work k3-twists-m2 make test
```

## Running a batch

A long computation is described as a batch: a file that says which surfaces, which tasks, which limits, and how much of the machine to use. One task is one computation with one answer, for example Extⁱ(M_H, M_x) on the quartic with seed 1 over the field with 32003 elements.

```bash
python3 -m k3batch plan batches/quartic-sample.toml
```

```bash
python3 -m k3batch run batches/quartic-sample.toml
```

```bash
python3 -m k3batch report results/quartic-sample
```

`plan` lists the tasks a run would compute, with their costs and limits, and computes nothing. `run` computes every task that has no record yet. `report` prints tables from the records. `make plan`, `make run` and `make report` do the same with `BATCH=batches/….toml`.

### The batch file

```toml
name = "example"                 # results go to results/example

[scheduler]
workers = 4                      # task processes at a time
memory_budget_mb = 4000          # the memory limits of running tasks never add up to more

[limits]                         # limits of one task
time_seconds = 300
memory_mb = 1000

[[limits.tier]]                  # tasks of cost 9 or more get other limits
min_cost = 9
time_seconds = 3600
memory_mb = 3000

[[surfaces]]
d = 2                            # also: seed, characteristic, special_quadric

[[tasks]]
kind = "ext_pair"
sheaves = ["O", "O(1H)", "M_H", "M_x", "O_x"]
```

Every `[[tasks]]` table is expanded on every surface. The kinds are:

| Kind | Tasks | Keys |
|---|---|---|
| `ext_pair` | Extⁱ(E, F) for each ordered pair | `sheaves = "all"` or a list of names; or `sources` and `targets` |
| `invariant` | one entry of `sheafInvariants` | `names = "fast"`, `"slow"`, `"all"` or a list of names |
| `synthetic` | no mathematics: sleeps, holds memory or fails | `items`, each with `name` and `sleep_seconds`, `allocate_mb`, `fail` |

A `[[tasks]]` table may carry its own `limits = { time_seconds = …, memory_mb = … }`. A task gets the limits of its table if there are any, otherwise those of the highest tier whose `min_cost` it reaches, otherwise the defaults. On the command line `--workers`, `--memory-budget`, `--time-limit` and `--memory-limit` replace the scheduler settings and the default limits.

Each task has a cost. For a pair it is the rank of the sheaf Hom(E, F). The cost is a hint and not an estimate of the time: tasks run in order of cost, cheapest first, and tiers use it to give expensive tasks larger limits. Tasks whose memory limits do not fit the budget together never run at the same time; a task whose limit is the whole budget runs alone.

The batches in `batches/`:

| File | Content |
|---|---|
| `quartic-sample.toml` | 25 pairs among five sheaves on the quartic; half a minute |
| `invariants.toml` | the fast invariants for d = 2, 3, 4; seconds |
| `invariants-slow.toml` | the slow invariants on the quartic; minutes |
| `ext-table.toml` | every pair of the catalogue on four surfaces, 2128 tasks; many hours, and the largest pairs will reach their limits |
| `limits-demo.toml` | six pairs and two synthetic tasks that are stopped at a time limit and at a memory limit |

### What a run guarantees

- **One process per task.** Each task runs in its own Macaulay2 process. A task that fails, hangs or runs out of memory cannot affect another task or its record.
- **Limits are enforced from outside.** The scheduler measures the wall time of each process and kills it at the time limit. The memory limit is a control-group limit set through `systemd-run --user --scope` where that is available (`--memory-guard cgroup`); elsewhere the scheduler reads the resident size of each process every 20 ms and kills it over the limit (`--memory-guard poll`).
- **A memory budget.** A task starts only when a worker is free and its memory limit fits in what remains of the budget. A run is refused if the budget is more than the memory available on the machine at that moment, unless `--overcommit` is given.
- **One record per task.** When a task ends, whatever the reason, one JSON object is appended to `results/<name>/results.jsonl` in a single write.
- **Exact resumption.** A rerun computes the tasks that have no record and nothing else. An interrupted run leaves no record for the tasks that were in flight, so a rerun computes them. `--retry timeout,memory` computes again the tasks whose latest record has one of those statuses, for example after raising a limit.
- **No orphans.** Task processes are killed by the kernel if the scheduler itself is killed. Two runs cannot write to the same results.

### Records

A record carries the task, its outcome and where it came from:

```json
{"task_id": "ext_pair/d2-p32003-s1/M_H/M_x",
 "task": {"kind": "ext_pair", "source": "M_H", "target": "M_x", "cost": 6,
          "surface": {"d": 2, "seed": 1, "characteristic": 32003, "special_quadric": false}, "…": "…"},
 "status": "ok",
 "value": {"dims": [0, 0, 1], "chi": 1}, "predicted": {"chi": 1}, "agrees": true,
 "detail": {"method": "Serre duality", "setup_seconds": 0.006, "compute_seconds": 2.1},
 "wall_seconds": 2.6, "cpu_seconds": 3.9, "peak_rss_mb": 325.6,
 "limits": {"time_seconds": 300, "memory_mb": 1000}, "memory_guard": "cgroup",
 "exit_code": 0, "exit_signal": null, "error": null, "log": null,
 "started_at": "…", "run_id": "…",
 "runner": {"m2_version": "1.25.11", "package": "K3Twists 0.2"},
 "code": {"commit": "…", "dirty": false}}
```

| Status | Meaning |
|---|---|
| `ok` | a value was computed; it agrees with the predicted value, or there is none |
| `mismatch` | a value was computed and differs from the predicted value |
| `unsupported` | there is no method for the task (a pair of two sheaves that are not locally free) |
| `timeout` | stopped at the time limit |
| `memory` | stopped at the memory limit |
| `error` | Macaulay2 reported an error; the message is in the record |
| `crashed` | the process ended without a result for another reason |

`peak_rss_mb` is the largest resident size of the task's process, as the kernel reports it when the process ends. The output of a task that did not end with a value is kept in `results/<name>/logs/`. Next to the records, `runs.jsonl` has one line per run with the configuration as it was resolved, the command line, the versions and the memory available at the start, and `manifest.json` lists the tasks of the latest run with their limits.

`run` exits with status 0 when every task of the batch is `ok` or `unsupported`, 1 when a task is `mismatch`, `error` or `crashed`, 3 when nothing failed but tasks were stopped at a limit, and 2 when the batch cannot be run as asked.

### Reports

`report` prints, as Markdown: a summary by group and status, the computed values that differ from the predicted ones, the tasks stopped at a limit with their limits, wall time and peak memory, the errors, and the pairs with no method. `--full` lists every computed value against its predicted value. For the sample batch:

```
| group | tasks | ok | unsupported |
|---|---|---|---|
| ext_pair d2-p32003-s1 | 25 | 24 | 1 |
```

## Design

Macaulay2 does the mathematics and nothing else. `runTask` computes one task and `expandBatch` lists the tasks of a batch, including which pairs exist and what they cost; `runners/task-runner.m2` exposes the two as a command that reads and prints JSON. The scheduler is in Python and knows no mathematics: it calls the runner, enforces limits and keeps records. It is tested against a fake runner without Macaulay2.

The process boundary is the task because Macaulay2 cannot be relied on to stop itself or to isolate work inside one process:

- `alarm` interrupts interpreted loops, Gröbner bases, resolutions and Hom sheaves within a fraction of a second of the set time, but a global `Ext` of sheaves on the degree 6 surface ran for seven minutes past a five second alarm without being interrupted.
- Macaulay2's tasks (`schedule`, `parallelApply`) are threads of one process. They share its memory, a single one cannot be killed, and `cancelTask` sets the same interrupt flag as `alarm`.
- A process that serves several tasks carries state from one to the next: sheaves cache what was computed with them, so the time and memory of a task would depend on which tasks ran before it.

A process per task costs the start of Macaulay2 and the loading of the package, 0.4 seconds, plus the construction of the two sheaves of the task. The catalogue builds each sheaf on request for that reason: building all of it takes 0.02 seconds on the quartic, 4.6 seconds for d = 3 and 1.1 seconds for d = 4, almost all of it for the duals of M_H and M_x.

## Tests

```bash
make test
```

```bash
make test-slow
```

`make test` runs the fast tests of the package (twelve tests, a few seconds) and the tests of the scheduler (about twenty seconds; they include real Macaulay2 tasks stopped at a time limit and at a memory limit). `make test-slow` runs the three package tests that compute Ext groups and take about a minute together; a test is slow when its first line is `-- slow`. `make test-all` runs both. In Macaulay2, `check "K3Twists"` runs every test of the package.

`make lint` runs `ruff` and `mypy` on the scheduler; neither is needed to run it. There is no linter or formatter for the Macaulay2 language; `installPackage "K3Twists"` checks that every exported function is documented and that the examples run.

## Layout

| Path | Content |
|---|---|
| `K3Twists.m2` | the package: exports, and the files it loads |
| `K3Twists/` | surfaces, classes, sheaves, catalogue, invariants, tasks, documentation, tests |
| `runners/task-runner.m2` | the command the scheduler calls: expands a batch, computes one task |
| `runners/run-tests.m2` | runs the fast or the slow tests of the package |
| `k3batch/` | the scheduler: batch file, runner protocol, limits, records, reports, command line |
| `batches/` | batch files |
| `tests/` | tests of the scheduler, and the fake runner they use |
| `results/` | records of runs; not in git |
| `Dockerfile`, `Makefile`, `pyproject.toml`, `.github/workflows/` | container, targets, lint settings, continuous integration |

## What this does not show

- It computes sheaf cohomology. It does not test Bridgeland stability, which is what most of the study's statements are about.
- The surfaces are over finite fields and their Picard rank is not determined. The numbers checked here do not depend on the Picard rank.
- Only the sheaves above are covered, which correspond to words of length at most two. Images of longer words are complexes, and building them is the next thing to add.
- The predicted values follow from short exact sequences; agreement confirms those computations and the code, not the theory as a whole.
- For a pair of sheaves only the Euler characteristic is predicted; the three dimensions are computed and recorded but compared with nothing.

## A note on method

The idea for this project and its direction are my own. AI tools (Anthropic's Claude) were used extensively in carrying it out, including the derivations, code, computations and drafting. The results have not been independently reviewed. If you would like more detail on how the work was done, get in touch.

Chris Dare

## Licence

MIT, see [LICENSE](LICENSE).
