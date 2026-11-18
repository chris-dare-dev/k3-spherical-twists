TEST ///
    Y = quinticThreefold();
    K = k3Surface 2;
    assert({varietyDimension K, serreShift K} === {2,2});
    assert({varietyDimension Y, serreShift Y} === {3,3});
    evidence = varietyEvidence Y;
    assert(evidence#"smooth" and evidence#"canonicalDegree" === 0);
    assert(char Y#"field" == 101 and degree Y#"variety" == 5);
    assert(degree(Y#"ring"/Y#"point") == 1);
    assert(distinguishedObjects Y === {"O","O_x","I_x"});
    assert((varietyCapabilities K)#"numerical" =!= (varietyCapabilities Y)#"numerical");
    Oref = structureObject Y;
    P = catalogueObject(Y, "O_x");
    Iref = catalogueObject(Y, "I_x");
    Hobs = cohomologyObservation Oref;
    assert(Hobs#"complete" and Hobs#"support" === {0,3});
    assert(apply(4, i -> observedDimension(Hobs,i)) === {1,0,0,1});
    forward = extObservation(Oref,P);
    backward = extObservation(P,Oref);
    assert(apply(4, i -> observedDimension(forward,i)) === {1,0,0,0});
    assert(apply(4, i -> observedDimension(backward,i)) === {0,0,0,1});
    assert((extObservation(P,Iref))#"status" === "unsupported");
    assert(eulerPairing(numericalClass Oref, numericalClass P) === 1);
    assert(eulerPairing(numericalClass P, numericalClass Oref) === -1);
    assert(eulerPairing(numericalClass structureObject K, numericalClass catalogueObject(K,"O_x")) === 1);
    assert(eulerPairing(numericalClass catalogueObject(K,"O_x"), numericalClass structureObject K) === 1);
///

TEST ///
    Y = quinticThreefold();
    Oref = structureObject Y;
    P = catalogueObject(Y, "O_x");
    S = sphericalObject Oref;
    assert(S#"dimension" === 3 and S#"evidence"#"selfExt" === {1,0,0,1});
    assert(try (sphericalObject P; false) else true);
    W = twistWord {twistStep(S,1)};
    U = inverseTwistWord W;
    imageRef = applyWord(W,P,VerifiedOnly=>true);
    assert(instance(imageRef, SymbolicQuinticTwistImage));
    assert(applyWord(W,P) === imageRef and applyWord(U,imageRef) === P);
    v = numericalClass imageRef;
    assert(v#"coordinates" === {-1,1});
    assert((applyWordToClass(U,numericalClass P))#"coordinates" === {1,1});
    assert(applyWordToClass(composeTwistWords(W,U),numericalClass P) === numericalClass P);
    assert(applyWordToClass(W,numericalClass P) === v);
    assert(try (applyWord(W,structureObject quinticThreefold()); false) else true);
    result = realizeTwistImage imageRef;
    assert(result#"status" === "realized" and numericalClass result === v);
    assert(isWellDefined result#"complex");
    assert(HH_1 result#"complex" == module pointIdealSheaf Y and HH_0 result#"complex" == 0);
    assert(module realizedHomology(result,-1) == module pointIdealSheaf Y);
    IH = cohomologyObservation result#"representative";
    assert(IH#"support" === {-1,2} and observedDimension(IH,2) === 1);
    unsupported = realizeTwistImage applyWord(U,P);
    assert(unsupported#"status" === "unsupported" and (numericalClass unsupported)#"coordinates" === {1,1});
///
