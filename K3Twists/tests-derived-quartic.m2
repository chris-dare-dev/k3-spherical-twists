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

TEST ///
    needsPackage "Complexes";
    K = realizeK3Surface k3Recipe hashTable {"family" => "quartic_with_line"};
    Oref = structureObject K;
    Lref = catalogueObject(K, "O(-1H)");
    W = twistWord {twistStep(sphericalObject Oref, 1)};
    result = realizeTwistImage applyWord(W, Lref);
    assert(result#"status" === "realized" and result#"strategy" === "quartic-degree-two-evaluation");
    assert(result#"extDimensions" === {{0,0},{1,0},{2,4}});
    assert(result#"serrePairing" == id_((K#"field")^4));

    R = K#"ring";
    u = result#"chainMap";
    D = source u;
    C = result#"complex";
    assert(concentration D === (-2,0) and concentration C === (-1,1));
    assert(isComplexMorphism u and isWellDefined C);

    -- Postcompose the four actual evaluation components with each coordinate.
    -- Their degree-two cochains agree with the claimed pairings modulo coboundaries.
    model = first components D;
    coboundary = transpose (model.dd)_0;
    traceLift = result#"traceCocycle";
    inImage = f -> coboundary * (transpose f // coboundary) == transpose f;
    assert(not inImage traceLift);
    scan(4, j -> (
            f := u_0 * (D_[j])_0;
            scan(4, i -> (
                    product := map(R^1, source traceLift, (gens R)#i * f);
                    assert(inImage (product - if i == j then traceLift else 0));
                    ));
            ));
    assert(isIsomorphism sheaf homology(0, canonicalMap(C, target u)));
    toO = (result#"sourceAugmentation")[-1] * canonicalMap(D[-1], C);
    assert(isIsomorphism sheaf homology(-1, toO));
    assert(realizedHomology(result, -1) == 0);
    v = mukaiClass result;
    assert({v#"rank", v#"divisor"#"coordinates", v#"eulerComponent"} === {-3,{-1,0},-1});

    shifted = realizeTwistImage applyWord(W, shiftObject(Lref, 1));
    assert(shifted#"status" === "realized" and shifted#"shift" === 1);
    assert(concentration shifted#"complex" === (0,2));
    assert(all(1..2, i -> ((shifted#"complex").dd)_i == -(C.dd)_(i-1)));
    assert(mukaiClass shifted === mukaiClass shiftObject(result#"representative", 1));
///

TEST ///
    needsPackage "Complexes";
    K = realizeK3Surface k3Recipe hashTable {"family" => "quartic_with_line"};
    S = sphericalObject structureObject K;
    W = twistWord {twistStep(S, 1), twistStep(S, -1)};
    Lref = catalogueObject(K, "O(-1H)");
    assert(applyWord(W, Lref) === Lref);
    scan({0,1}, shift -> (
        input := shiftObject(Lref, shift);
        result := realizeTwistImage(W, input);
        assert(result#"status" === "realized" and result#"strategy" === "quartic-degree-two-inverse-cancellation");
        assert(result#"directions" === {1,-1} and result#"shift" === shift);
        assert(result#"serrePairingRank" === 4 and result#"derivedHomDegrees" === {{shift-1,4}});
        forward := result#"forward";
        assert(forward#"strategy" === "quartic-degree-two-evaluation");
        assert(forward#"serrePairing" == id_((K#"field")^4));
        p := result#"chainMap";
        q := result#"comparison";
        C := result#"complex";
        assert(source p == forward#"complex" and concentration target p === (shift-1,shift-1));
        assert(target q == C and concentration source q === (shift,shift));
        assert(isComplexMorphism p and isComplexMorphism q and isWellDefined C);
        assert(isIsomorphism sheaf homology(shift, q));
        (lo, hi) := concentration C;
        assert(all(lo..hi, i -> i == shift or sheaf HH_i C == 0));
        assert(result#"representative" === input and mukaiClass result === mukaiClass input);
        ));
///

TEST ///
    needsPackage "Complexes";
    K = realizeK3Surface k3Recipe hashTable {"family" => "quartic_with_line"};
    S = sphericalObject structureObject K;
    W = twistWord {twistStep(S, 1), twistStep(S, 1)};
    Lref = catalogueObject(K, "O(-1H)");
    scan({0,1}, shift -> (
        input := shiftObject(Lref, shift);
        result := realizeTwistImage(W, input);
        assert(result#"status" === "realized" and result#"strategy" === "quartic-degree-three-evaluation");
        assert(result#"directions" === {1,1} and result#"shift" === shift);
        assert(result#"forward"#"strategy" === "quartic-degree-two-evaluation");
        assert(result#"derivedHomDegrees" === {{3,4}} and result#"evaluationClassRank" === 4);
        u := result#"chainMap";
        assert(isComplexMorphism u and isHomogeneous u and isWellDefined u);
        assert(isComplexMorphism result#"sourceAugmentation");
        C := result#"complex";
        assert(concentration C === (shift-2,shift+1) and isWellDefined C);
        O := OO_(K#"variety")^1;
        assert(realizedHomology(result, -shift) == O(-1));
        firstCone := target u;
        firstEval := result#"forward"#"chainMap";
        firstAug := result#"forward"#"sourceAugmentation";
        secondAug := result#"sourceAugmentation";
        assert(sheaf (target firstAug)_(-2) == O^4 and sheaf (target secondAug)_(-3) == O^4);
        assert(isIsomorphism sheaf homology(-1, firstAug[-1] * canonicalMap((source firstEval)[-1], firstCone)));
        assert(isIsomorphism sheaf homology(-1, canonicalMap(cone u, firstCone)));
        assert(isIsomorphism sheaf homology(-2, secondAug[-1] * canonicalMap((source u)[-1], cone u)));
        assert(realizedHomology(result, -1-shift) == 0);
        assert(result#"representative" === input and mukaiClass result === mukaiClass input);
        ));
///
