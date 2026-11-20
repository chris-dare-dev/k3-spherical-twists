# Targets run from the repository root.
#   make test                              fast tests: Macaulay2 package and scheduler
#   make test-slow                         the Macaulay2 tests that take longer
#   make run BATCH=batches/invariants.toml compute the tasks of a batch that have no record yet
#   make report BATCH=batches/invariants.toml REPORT_ARGS=--full
#   make record BATCH=batches/invariants.toml   run, then copy the records into records/ (committed code only)
#   make adopt BATCHES="invariants limits-demo" copy the records of runs that are already in results/
#   make smoke       the invariants batch, computed afresh, and the headline table of GUIDE.md from it
#   make tables      write the generated tables of CLAIMS.md, GUIDE.md and claims/RECORDS.md
#   make check       fail if those tables are not what the registry and the records give
# ARGS is passed to k3batch, for example ARGS="--workers 8 --memory-budget 16000".
M2     ?= M2
PYTHON ?= python3
BATCH  ?= batches/quartic-sample.toml
ARGS   ?=
REPORT_ARGS ?=

K3BATCH  = $(PYTHON) -m k3batch
RUNNER   = --runner '$(M2) --script runners/task-runner.m2'
RUN_DIR  = results/$(basename $(notdir $(BATCH)))
CHECKED  = k3batch tests tools
# a batch with a dependency graph needs the SQLite store; its records are adopted from there
STORE    = $(if $(shell grep -l '^\[graph\]' $(BATCH)),--store $(RUN_DIR)/results.sqlite)
# the status `make record` expects of the run: 0, or 3 for a batch whose tasks are stopped on purpose
EXPECT  ?= 0
BATCHES ?=

.PHONY: test test-m2 test-python test-slow test-all lint format plan run report record adopt smoke tables check

test: test-m2 test-python

test-m2:
	$(M2) --script runners/run-tests.m2 fast

test-python:
	$(PYTHON) -m unittest discover -s tests -t .

test-slow:
	$(M2) --script runners/run-tests.m2 slow

test-all: test test-slow

lint:
	ruff check $(CHECKED)
	ruff format --check $(CHECKED)
	mypy

format:
	ruff format $(CHECKED)

plan:
	$(K3BATCH) plan $(BATCH) $(RUNNER) $(STORE) $(ARGS)

run:
	$(K3BATCH) run $(BATCH) $(RUNNER) $(STORE) $(ARGS)

report:
	$(K3BATCH) report $(RUN_DIR) $(REPORT_ARGS)

record:
	status=0; $(K3BATCH) run $(BATCH) $(RUNNER) $(STORE) $(ARGS) || status=$$?; \
	if [ $$status -ne $(EXPECT) ]; then echo "run ended with status $$status, expected $(EXPECT)"; exit 1; fi
	$(PYTHON) tools/claims.py adopt $(RUN_DIR)

adopt:
	$(PYTHON) tools/claims.py adopt $(addprefix results/,$(BATCHES))

smoke:
	rm -rf results/smoke
	$(K3BATCH) run batches/invariants.toml $(RUNNER) --out results/smoke $(ARGS)
	$(PYTHON) tools/claims.py headline results/smoke

tables:
	$(PYTHON) tools/claims.py tables

check:
	$(PYTHON) tools/claims.py check
