TEST ///
    L = markedDivisorLattice(ZZ/32003, {"H", "C"}, matrix {{4, 1}, {1, -2}});
    c = divisorClass(L, {2, -1});
    D = divisorClass(L, {1, 3});
    assert(divisorPairing(c, D) == 19);
    v = mukaiClass(3, c, 5);
    w = mukaiClass(2, D, 7);
    assert(mukaiPairing(v, w) == -12);
    v' = tensorByDivisor(v, D);
    assert(v'#"rank" == 3 and v'#"eulerComponent" == 12);
    assert((v'#"divisor")#"coordinates" == {5, 8});
    assert(((dualVector v)#"divisor")#"coordinates" == {-2, 1});
    assert(dualVector(dualVector v) === v);
    assert(tensorByDivisor(v', divisorClass(L, {-1, -3})) === v);

    L' = markedDivisorLattice(L#"field", L#"basis", L#"gram");
    c' = divisorClass(L', c#"coordinates");
    assert(try (divisorPairing(c, c'); false) else true);
    assert(try (mukaiPairing(v, mukaiClass(3, c', 5)); false) else true);
    assert(try (tensorByDivisor(v, c'); false) else true);
    assert(try (divisorClass(L, {1}); false) else true);
    assert(try (markedDivisorLattice(QQ, {"H", "H"}, matrix {{4, 0}, {0, -2}}); false) else true);
    assert(try (markedDivisorLattice(QQ, {"H", "C"}, matrix {{4, 1}, {0, -2}}); false) else true);
    assert(try (markedDivisorLattice(QQ, {"H"}, matrix {{3}}); false) else true);
///

TEST ///
    L = markedDivisorLattice(QQ, {"H", "C", "D"}, matrix {{4, 1, 0}, {1, -2, 1}, {0, 1, -2}});
    c = divisorClass(L, {1, 2, 3});
    D = divisorClass(L, {-1, 0, 2});
    assert(divisorPairing(c, D) == -14);
    v = tensorByDivisor(mukaiClass(-2, c, -3), D);
    assert(v#"rank" == -2 and v#"eulerComponent" == -13);
    assert((v#"divisor")#"coordinates" == {3, 2, -1});
///

TEST ///
    recipe = k3Recipe hashTable {"family" => "complete_intersection", "d" => 3, "special_quadric" => true};
    assert(instance(recipe, K3FamilyRecipe) and not recipe#?"equations");
    normalized = hashTable {"d" => 3, "seed" => 1, "characteristic" => 32003, "special_quadric" => true};
    assert(recipe#"parameters" === normalized);
    K = realizeK3Surface recipe;
    assert(K#"recipe" === recipe and char K#"field" == 32003 and isField K#"field");
    assert(#(K#"equations") == 2 and K#"grading" == {{1}, {1}, {1}, {1}, {1}});
    x = K#"coordinates";
    assert(first K#"equations" == x#0 * x#1 + x#2 * x#3 + (x#4)^2);
    assert((K#"markedIdeals")#"point" == K#"point");
    H = K#"polarization";
    assert(H#"lattice" === K#"lattice" and H#"coordinates" == {1});
    assert(divisorPairing(H, H) == 6);
    assert(#catalogueClasses K == 26);

    Q = k3Surface 2;
    assert(#catalogueClasses Q == 22);
    v = catalogueMukaiClass(Q, "M_H");
    w = catalogueMukaiClass(Q, "O(1H)");
    v0 = (select(catalogueClasses Q, row -> row#0 == "M_H"))#0#1;
    w0 = (select(catalogueClasses Q, row -> row#0 == "O(1H)"))#0#1;
    assert(mukaiPairing(v, w) == mukaiPairing(2, v0, w0));
    v' = tensorByDivisor(v, Q#"polarization");
    assert({v'#"rank", first ((v'#"divisor")#"coordinates"), v'#"eulerComponent"} == twistVector(2, v0, 1));
    Q' = k3Surface 2;
    assert(try (mukaiPairing(v, catalogueMukaiClass(Q', "M_H")); false) else true);
///

TEST ///
    assert(try (k3Recipe hashTable {"d" => 2, "family" => "unknown_family"}; false) else true);
    assert(try (k3Recipe hashTable {"d" => 2, "special_quadric" => true}; false) else true);
    assert(try (k3Recipe hashTable {"d" => 3, "special_quadric" => 1}; false) else true);
    assert(try (k3Recipe hashTable {"d" => 2, "seed" => "1"}; false) else true);
    assert(try (k3Recipe hashTable {"d" => 2, "characteristic" => 9}; false) else true);

    tasks = {hashTable {"kind" => "ext_pair", "sheaves" => {"O"}}};
    description = surfaces -> hashTable {"surfaces" => surfaces, "tasks" => tasks};
    direct = first expandBatch description {hashTable {"d" => 2}};
    named = first expandBatch description {hashTable {"family" => "complete_intersection", "d" => 2}};
    assert(named === direct);
    nullableSpec = hashTable {"d" => 2, "seed" => null, "characteristic" => null, "special_quadric" => null};
    assert(first expandBatch description {nullableSpec} === direct);
    assert(try (expandBatch description {hashTable {"d" => 2, "marking" => {"H", "C"}}}; false) else true);
    invalid = merge(direct, hashTable {"surface" => hashTable {"d" => 2, "typo" => 1}}, (a, b) -> b);
    assert(try (runTask invalid; false) else true);
///
