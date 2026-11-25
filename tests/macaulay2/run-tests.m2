-- Runs the tests of the package (its TEST blocks, in src/macaulay2/K3Twists/tests/) and exits with
-- status 1 if one fails.
--   M2 --script tests/macaulay2/run-tests.m2 [fast|slow|all]      (default: all)
-- A test is slow when its first line is "-- slow".
path = prepend(currentFileDirectory | "../../src/macaulay2/", path);
needsPackage "K3Twists";

which = if #scriptCommandLine > 1 then scriptCommandLine#1 else "all";
if not member(which, {"fast", "slow", "all"}) then (
    stderr << "usage: M2 --script run-tests.m2 [fast|slow|all]" << endl;
    exit 2;
    );
all' = tests "K3Twists";
isSlow = i -> match("^[^\n]*\n\\s*-- slow\\s*\n", toString all'#i);
chosen = select(#all', i -> which == "all" or (which == "slow") == isSlow i);
-- check runs every test when it is given an empty list
if #chosen > 0 then check(chosen, "K3Twists");
<< "passed: " << #chosen << " tests (" << which << "; the package has " << #all' << ")" << endl;
