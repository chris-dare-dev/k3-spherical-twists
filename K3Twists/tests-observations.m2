TEST ///
    K = k3Surface 2;
    E = structureObject K;
    shifted = shiftObject(E, 1);
    obs = cohomologyObservation shifted;
    assert(obs#"subjects" === {shifted} and obs#"convention" === "cohomological");
    assert(obs#"support" === {-1, 1} and obs#"complete");
    assert(obs#"dimensions" === hashTable {-1 => 1, 0 => 0, 1 => 1});
    assert(observedDimension(obs, -2) === 0 and degreeStatus(obs, -2) === "zero");
    partial = cohomologyObservation(shifted, Degrees => {-1, -1});
    assert(not partial#"complete");
    assert(degreeStatus(partial, 0) === "uncomputed" and observedDimension(partial, 0) === null);
    assert(degreeStatus(partial, 2) === "zero");
    a = extObservation(shiftObject(E, 1), shiftObject(E, -1), Degrees => {2, 3});
    assert(a#"support" === {2, 4} and observedDimension(a, 2) === 1);
    assert(degreeStatus(a, 4) === "uncomputed");
    unsupported = cohomologyObservation objectReference(K, "unknown", mukaiClass E);
    assert(unsupported#"status" === "unsupported" and degreeStatus(unsupported, 0) === "unsupported");
    assert(try (extObservation(E, structureObject k3Surface 2); false) else true);
///

TEST ///
    K = k3Surface 2;
    shifted = shiftObject(structureObject K, 1);
    obs = cohomologyObservation shifted;
    eulerPrediction = observationPrediction("shifted Euler", "1", {"K3 surface"}, ("cohomology", -2));
    wrong = observationPrediction("shifted table", "1", {}, ("cohomology", hashTable {-1 => 2}), Full => true);
    revisedPrediction = observationPrediction("shifted table", "2", {}, ("cohomology", hashTable {-1 => 1, 1 => 1}), Full => true);
    assert((checkObservation(obs, eulerPrediction))#"status" === "match");
    assert((checkObservation(obs, wrong))#"status" === "mismatch");
    assert(match("mismatch", toString net checkObservation(obs, wrong)));
    checked = checkObservation(obs, revisedPrediction);
    assert(checked#"status" === "match" and checked#"observation" === obs and checked#"prediction" === revisedPrediction);
    partial = cohomologyObservation(shifted, Degrees => {-1});
    assert((checkObservation(partial, eulerPrediction))#"status" === "inconclusive");
    assert((checkObservation(partial, revisedPrediction))#"status" === "inconclusive");
    selected = observationPrediction("one degree", "1", {}, ("cohomology", hashTable {-1 => 1}));
    assert((checkObservation(partial, selected))#"status" === "match");
///
TEST ///
    K = realizeK3Surface k3Recipe hashTable {"family" => "quartic_with_line"};
    W = twistWord {twistStep(sphericalObject structureObject K, 1)};
    A = realizeTwistImage applyWord(W, lineBundleObject(K, K#"polarization"));
    C = A#"complex";
    H = hypercohomologyObservation(K, C);
    S = cohomologyObservation(realizedHomology(A, -1), 1);
    assert(H#"complete" and H#"support" === {-1,2});
    assert(all(-1..2, i -> observedDimension(H, i) === observedDimension(S, i)));
    assert(degreeStatus(H, 3) === "zero");
    selected = hypercohomologyObservation(K, C, Degrees => {1});
    assert(not selected#"complete" and observedDimension(selected, 1) === 4);
    assert(degreeStatus(selected, 0) === "uncomputed");
///
