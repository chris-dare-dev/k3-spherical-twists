# Targets run Macaulay2 from the repository root.  D is the degree parameter d (2, 3 or 4);
# LIMIT is a wall-clock limit in seconds for one run of the invariants.
M2     ?= M2
D      ?= 2
LIMIT  ?= 2400

.PHONY: test test-slow test-all invariants invariants-slow all-degrees

test:
	$(M2) --script runners/run-tests.m2 fast

test-slow:
	$(M2) --script runners/run-tests.m2 slow

test-all:
	$(M2) --script runners/run-tests.m2 all

invariants:
	K3D=$(D) timeout $(LIMIT) $(M2) --script scripts/sheaf-invariants.m2

invariants-slow:
	K3D=$(D) K3SLOW=1 timeout $(LIMIT) $(M2) --script scripts/sheaf-invariants.m2

all-degrees:
	for d in 2 3 4; do K3D=$$d timeout $(LIMIT) $(M2) --script scripts/sheaf-invariants.m2 || exit 1; done
