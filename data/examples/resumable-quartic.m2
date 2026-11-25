-- Paste these expressions into M2, or run with M2 --script data/examples/resumable-quartic.m2 from the repository root.
path = prepend("src/macaulay2/", path);      -- the package is in src/macaulay2/ of the repository
needsPackage "K3Twists";
K = realizeK3Surface k3Recipe hashTable {
    "family" => "quartic_with_line", "seed" => 1, "characteristic" => 32003
    };
assert(K#"lattice"#"gram" == matrix {{4, 1}, {1, -2}});
<< "marked lattice " << K#"lattice"#"basis" << endl << K#"lattice"#"gram" << endl;
<< "named objects " << apply(catalogue K, first) << endl;
E = lineBundleObject(K, K#"polarization");
S = sphericalObject structureObject K;
W = twistWord {twistStep(S, 1)};
A = applyWord(W, E);
<< "Mukai class " << mukaiClass A << endl;
R = realizeTwistImage A;
assert(R#"status" === "realized");
assert(cohomologyDims realizedHomology(R, -1) === {0,0,4});
<< R << endl;
<< cohomologyObservation(realizedHomology(R, -1), 1) << endl;
U = realizeTwistImage applyWord(inverseTwistWord W, E);
assert(U#"status" === "unsupported");
<< U << endl;
