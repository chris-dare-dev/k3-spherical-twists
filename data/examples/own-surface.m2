-- A K3 surface of your own: its degree, the prime of its field and the seed of its random equations.
-- Paste the expressions into M2, or run with M2 --script data/examples/own-surface.m2 from the repository root.
--
-- d is 2, 3 or 4 (a quartic, a quadric and a cubic, three quadrics); the characteristic is any prime;
-- another seed gives another surface of the same family.  The predictions are formulas in n = d + 2,
-- so they do not change with the prime or the seed, and every row below should agree.
path = prepend("src/macaulay2/", path);      -- the package is in src/macaulay2/ of the repository
needsPackage "K3Twists";
d = 3; p = 101; seed = 7;
K = k3Surface(d, Characteristic => p, Seed => seed);
rows = sheafInvariants K;                       -- {name, computed, predicted} for each fast invariant
<< "degree " << 2 * d << " in P^" << d + 1 << " over the field of " << p << " elements, seed " << seed << endl;
<< netList(prepend({"invariant", "computed", "predicted"}, rows)) << endl;
differing = select(rows, row -> row#1 =!= row#2);
<< #rows - #differing << " of " << #rows << " invariants agree with their predictions" << endl;
assert(#differing == 0);
