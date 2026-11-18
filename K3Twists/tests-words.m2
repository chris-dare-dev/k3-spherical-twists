TEST ///
    K = k3Surface 2;
    O = structureObject K;
    H = lineBundleObject(K, K#"polarization");
    P = catalogueObject(K, "O_x");
    S = sphericalObject O;
    U = sphericalObject H;
    a = twistStep(S, 1);
    b = twistStep(U, -1);
    A = twistWord {a};
    B = twistWord {b};
    W = composeTwistWords(A, B);
    assert(W#"steps" === {a, b});
    assert(instance(applyWord(W, P), SymbolicTwistImage));
    I = applyWord(W, P, VerifiedOnly => true);
    assert(I#"start" === P);
    assert(I#"prefix" === applyWord(A, P));
    assert(I === applyWord(twistWord {a, b}, catalogueObject(K, "O_x")));
    assert(applyWord(B, I#"prefix") === I);
    v = mukaiClass I;
    assert({v#"rank", (v#"divisor")#"coordinates", v#"eulerComponent"} === {2, {3}, 9});
    w = mukaiClass applyWord(composeTwistWords(B, A), P);
    assert({w#"rank", (w#"divisor")#"coordinates", w#"eulerComponent"} === {2, {-1}, 1});
    assert(v === applyWordToClass(W, mukaiClass P, VerifiedOnly => true));
    assert(applyWord(inverseTwistWord W, I) === P);
    assert(applyWord(composeTwistWords(W, inverseTwistWord W), P) === P);
    assert(applyWord(twistWord {}, P) === P);

    L = twistWord flatten apply(256, i -> {a, b});
    longClass = applyWordToClass(L, mukaiClass P);
    assert(abs(longClass#"rank") > 10^100);
    assert(applyWordToClass(inverseTwistWord L, longClass) === mukaiClass P);
///

TEST ///
    K = k3Surface 2;
    O = structureObject K;
    O2 = shiftObject(O, 2);
    assert(instance(O2, ShiftedK3Object));
    assert(O2 =!= O);
    assert(mukaiClass O2 === mukaiClass O);
    assert((sphericalObject O2)#"object" === O2);
    assert(shiftObject(O2, -2) === O);
    assert((mukaiClass shiftObject(O, -1))#"rank" == -1);
    S = sphericalObject O;
    W = twistWord {twistStep(S, 1)};
    I = applyWord(W, O);
    J = applyWord(W, O2);
    assert(I =!= J and mukaiClass I === mukaiClass J);
    assert(shiftObject(I, 2) =!= I and mukaiClass shiftObject(I, 2) === mukaiClass I);
    assert(I#"evidence" === {S#"evidence"});
    assert(S#"dimension" == 2 and (S#"evidence")#"kind" == "theorem");

    F = catalogueObject(K, "O");
    T = checkedSphericalObject F;
    assert((T#"evidence")#"kind" == "checked" and (T#"evidence")#"selfExt" === {1, 0, 1});
    assert(try (checkedSphericalObject catalogueObject(K, "O_x"); false) else true);

    G = objectReference(K, "external generator", mukaiClass O);
    assert(G === objectReference(K, "external generator", mukaiClass O));
    assert(try (sphericalObject G; false) else true);
    assumed = assumeSphericalObject(G, "external hypothesis");
    V = twistWord {twistStep(assumed, -1)};
    R = applyWord(V, O2);
    assert(R#"evidence" === {assumed#"evidence"});
    assert((applyWord(W, shiftObject(R, 1)))#"evidence" === {assumed#"evidence", S#"evidence"});
    assert(try (applyWord(V, O, VerifiedOnly => true); false) else true);
    assert(try (applyWord(W, shiftObject(R, 1), VerifiedOnly => true); false) else true);
    assert(try (applyWordToClass(V, mukaiClass O, VerifiedOnly => true); false) else true);
    assert(instance(applyWord(inverseTwistWord V, R), SymbolicTwistImage));

    K' = k3Surface 2;
    other = twistStep(sphericalObject structureObject K', 1);
    assert(try (twistWord {first(W#"steps"), other}; false) else true);
    assert(try (applyWord(W, structureObject K'); false) else true);
    assert(try (applyWordToClass(W, mukaiClass structureObject K'); false) else true);
    assert(try (objectReference(K, "wrong parent", mukaiClass structureObject K'); false) else true);
    assert(try (twistStep(S, 0); false) else true);
///

TEST ///
    L = markedDivisorLattice(ZZ/32003, {"H", "C"}, matrix {{4, 1}, {1, -2}});
    s = mukaiClass(0, divisorClass(L, {0,1}), 1);
    v = mukaiClass(2, divisorClass(L, {2,3}), -1);
    reflected = mukaiReflection(v, s);
    assert({reflected#"rank", (reflected#"divisor")#"coordinates", reflected#"eulerComponent"} === {2,{2,-3},-7});
    assert(mukaiReflection(reflected, s) === v);
    assert(mukaiPairing(reflected, reflected) == mukaiPairing(v, v));
    assert(try (mukaiReflection(s, v); false) else true);
///
