TEST ///
    needsPackage "Complexes";
    K = k3Surface 2;
    Oref = structureObject K;
    Href = lineBundleObject(K, K#"polarization");
    W = twistWord {twistStep(sphericalObject Href, 1)};
    I = realizeTwistImage applyWord(inverseTwistWord W, Oref);
    assert(I#"status" === "realized" and I#"relativeShift" === -1);
    R = K#"ring";
    C = I#"complex";
    assert(concentration C === (-1,0) and isWellDefined C);
    assert(C.dd_0 == -I#"coevaluation");
    assert(I#"coevaluation" == map(R^{4:1}, R^1, transpose vars R));
    assert(realizedHomology(I, 0) == 0);
    assert(realizedHomology(I, 1) == quotientBundle K);
    assert(cohomologyDims realizedHomology(I, 1) === {15,1,0});
    v = mukaiClass I;
    assert({v#"rank", v#"divisor"#"coordinates", v#"eulerComponent"} === {-3,{-4},-11});
    Oagain = realizeTwistImage applyWord(W, I#"representative");
    assert(Oagain#"status" === "realized" and isWellDefined Oagain#"complex");
    assert(Oagain#"evaluation" * Oagain#"kernelInclusion" == 0);
    assert(realizedHomology(Oagain, 1) == 0);
    assert(isIsomorphic(module realizedHomology(Oagain, 0), R^1));
    assert(mukaiClass Oagain === mukaiClass Oref);
///

TEST ///
    needsPackage "Complexes";
    K = k3Surface 2;
    Oref = structureObject K;
    W = twistWord {twistStep(sphericalObject Oref, 1)};
    forward = realizeTwistImage applyWord(W, Oref);
    assert(forward#"strategy" === "quartic-spherical-self-split");
    assert(forward#"derivedHomDegrees" === {{0,1},{2,1}});
    assert(extDims(realizedHomology(forward, 1), realizedHomology(forward, 1)) === {1,0,1});
    assert(forward#"shift" === -1 and isWellDefined forward#"complex");
    assert(mukaiClass forward === mukaiClass shiftObject(Oref, -1));
    restored = realizeTwistImage applyWord(inverseTwistWord W, forward#"representative");
    X = K#"variety";
    assert(restored#"shift" === 0 and realizedHomology(restored, 0) == OO_X^1);
    composed = realizeTwistImage applyWord(composeTwistWords(W, W), Oref);
    assert(composed#"directions" === {1,1} and composed#"shift" === -2);
    assert(composed#"realizationSeconds" >= 0);
    assert(concentration composed#"complex" === (-2,-2));
    assert(cohomologyDims realizedHomology(composed, 2) === {1,0,1});
    assert(mukaiClass composed === mukaiClass Oref);
    Href = lineBundleObject(K, K#"polarization");
    hw = twistWord {twistStep(sphericalObject Href, 1)};
    hyperplaneSelf = realizeTwistImage applyWord(hw, Href);
    assert(hyperplaneSelf#"shift" === -1);
    assert(cohomologyDims realizedHomology(hyperplaneSelf, 1) === {4,0,0});
    assumed = assumeSphericalObject(Oref, "no certified evidence");
    assert((realizeTwistImage applyWord(twistWord {twistStep(assumed, 1)}, Oref))#"status" === "unsupported");
///
