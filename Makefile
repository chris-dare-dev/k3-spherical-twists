# Targets run from the repository root.
#   make test                              fast tests: Macaulay2 package and scheduler
#   make test-slow                         the Macaulay2 tests that take longer
#   make examples                          the scripts of data/examples/, each a short computation to copy
#   make run BATCH=data/batches/invariants.toml compute the tasks of a batch that have no record yet
#   make report BATCH=data/batches/invariants.toml REPORT_ARGS=--full
#   make record BATCH=data/batches/invariants.toml   run, then copy the records into data/records/ (committed code only)
#   make adopt BATCHES="invariants limits-demo" copy the records of runs that are already in results/
#   make smoke       the invariants batch, computed afresh, and the headline table of GUIDE.md from it
#   make tables      write the generated tables of CLAIMS.md, GUIDE.md and data/claims/RECORDS.md
#   make check       fail if those tables are not what the registry and the records give
#   make lean-deps   once: fetch Mathlib's build cache for the Lean proofs in src/lean
#   make lean        build the Lean proofs (a warning fails it), their tests, linters, umbrella,
#                    axiom audit, cited-name check and style check
# ARGS is passed to the batch command, for example ARGS="--workers 8 --memory-budget 16000".
M2     ?= M2
PYTHON ?= python3
BATCH  ?= data/batches/quartic-sample.toml
ARGS   ?=
REPORT_ARGS ?=

# the Python package (src/batch) is imported from src/
export PYTHONPATH := $(CURDIR)/src

LAKE   ?= lake

CLI      = $(PYTHON) -m batch
CLAIMS   = $(PYTHON) -m batch.claims
RUNNER   = --runner '$(M2) --script src/batch/runner/task-runner.m2'
RUN_DIR  = results/$(basename $(notdir $(BATCH)))
CHECKED  = src/batch tests
# a batch with a dependency graph needs the SQLite store; its records are adopted from there
STORE    = $(if $(shell grep -l '^\[graph\]' $(BATCH)),--store $(RUN_DIR)/results.sqlite)
# the status `make record` expects of the run: 0, or 3 for a batch whose tasks are stopped on purpose
EXPECT  ?= 0
BATCHES ?=

.PHONY: test test-m2 test-python test-slow test-all examples lint format plan run report record adopt smoke tables check lean lean-deps

test: test-m2 test-python

test-m2:
	$(M2) --script tests/macaulay2/run-tests.m2 fast

test-python:
	$(PYTHON) -m unittest discover -s tests -t .

test-slow:
	$(M2) --script tests/macaulay2/run-tests.m2 slow

test-all: test test-slow

examples:
	set -e; for script in data/examples/*.m2; do echo "== $$script"; $(M2) --script $$script; done

lint:
	ruff check $(CHECKED)
	ruff format --check $(CHECKED)
	mypy

format:
	ruff format $(CHECKED)

plan:
	$(CLI) plan $(BATCH) $(RUNNER) $(STORE) $(ARGS)

run:
	$(CLI) run $(BATCH) $(RUNNER) $(STORE) $(ARGS)

report:
	$(CLI) report $(RUN_DIR) $(REPORT_ARGS)

record:
	status=0; $(CLI) run $(BATCH) $(RUNNER) $(STORE) $(ARGS) || status=$$?; \
	if [ $$status -ne $(EXPECT) ]; then echo "run ended with status $$status, expected $(EXPECT)"; exit 1; fi
	$(CLAIMS) adopt $(RUN_DIR)

adopt:
	$(CLAIMS) adopt $(addprefix results/,$(BATCHES))

smoke:
	rm -rf results/smoke
	$(CLI) run data/batches/invariants.toml $(RUNNER) --out results/smoke $(ARGS)
	$(CLAIMS) headline results/smoke

tables:
	$(CLAIMS) tables

check:
	$(CLAIMS) check

lean-deps:
	cd src/lean && $(LAKE) exe cache get

lean:
	cd src/lean && $(LAKE) build --wfail
	cd src/lean && $(LAKE) test
	cd src/lean && $(LAKE) lint
	cd src/lean && $(LAKE) exe mk_all --lib K3Twists --check
	cd src/lean && $(LAKE) env lean scripts/AxiomAudit.lean
	cd src/lean && $(LAKE) env lean scripts/CheckDocNames.lean
	cd src/lean && $(PYTHON) scripts/check_mathlib_style.py --check-baseline
