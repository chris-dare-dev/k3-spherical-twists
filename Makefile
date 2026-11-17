# Targets run from the repository root.
#   make test                              fast tests: Macaulay2 package and scheduler
#   make test-slow                         the Macaulay2 tests that take longer
#   make run BATCH=batches/invariants.toml compute the tasks of a batch that have no record yet
#   make report BATCH=batches/invariants.toml REPORT_ARGS=--full
# ARGS is passed to k3batch, for example ARGS="--workers 8 --memory-budget 16000".
M2     ?= M2
PYTHON ?= python3
BATCH  ?= batches/quartic-sample.toml
ARGS   ?=
REPORT_ARGS ?=

K3BATCH  = $(PYTHON) -m k3batch
RUNNER   = --runner '$(M2) --script runners/task-runner.m2'
RUN_DIR  = results/$(basename $(notdir $(BATCH)))

.PHONY: test test-m2 test-python test-slow test-all lint format plan run report

test: test-m2 test-python

test-m2:
	$(M2) --script runners/run-tests.m2 fast

test-python:
	$(PYTHON) -m unittest discover -s tests -t .

test-slow:
	$(M2) --script runners/run-tests.m2 slow

test-all: test test-slow

lint:
	ruff check k3batch tests
	ruff format --check k3batch tests
	mypy

format:
	ruff format k3batch tests

plan:
	$(K3BATCH) plan $(BATCH) $(RUNNER) $(ARGS)

run:
	$(K3BATCH) run $(BATCH) $(RUNNER) $(ARGS)

report:
	$(K3BATCH) report $(RUN_DIR) $(REPORT_ARGS)
