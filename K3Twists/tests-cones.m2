TEST ///
    K = k3Surface 2;
    S = sphericalObject structureObject K;
    W = twistWord {twistStep(S, 1)};
    P = catalogueObject(K, "O_x");
    L = lineBundleObject(K, K#"polarization");
    RP = realizeTwistImage applyWord(W, P);
    RL = realizeTwistImage applyWord(W, L);
    assert(RP#"status" === "realized" and RL#"status" === "realized");
    assert(mukaiClass RP === mukaiClass shiftObject(catalogueObject(K, "I_x"), 1));
    assert(mukaiClass RL === mukaiClass shiftObject(catalogueObject(K, "M_H"), 1));
    -- Compare the native differential and its kernel with the independent sheaf constructions.
    CP = RP#"complex";
    CL = RL#"complex";
    assert(isWellDefined CP and isWellDefined CL);
    assert(CP.dd_1 == RP#"evaluation" and CL.dd_1 == RL#"evaluation");
    assert(HH_1 CP == module pointIdealSheaf K);
    assert(HH_1 CL == module kernelBundle K);
    assert(HH_0 CP == 0 and HH_0 CL != 0);
    assert(realizedHomology(RP, 0) == 0 and realizedHomology(RL, 0) == 0);
    assert(cohomologyDims realizedHomology(RP, -1) === {0, 0, 1});
    assert(cohomologyDims realizedHomology(RL, -1) === {0, 0, 4});
    inverseResult = realizeTwistImage applyWord(inverseTwistWord W, L);
    assert(inverseResult#"status" === "unsupported" and inverseResult#"reason" === "inverse twists require coevaluation");
    assert(instance(mukaiClass inverseResult, MukaiClass));
    other = realizeTwistImage applyWord(W, structureObject K);
    assert(other#"status" === "unsupported");
///
