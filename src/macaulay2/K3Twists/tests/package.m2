-- Tests of the package.  A test whose first line is "-- slow" takes more than a few seconds;
-- tests/macaulay2/run-tests.m2 uses that line to run the fast and the slow tests separately.

TEST ///
    -- the recursion c_(k+1) = n c_k - c_(k-1)
    assert(apply(4, k -> chainNumber(4, k)) == {1, 3, 11, 41});
    assert(chainNumber(5, 2) == 19);
///

TEST ///
    -- classes: the pairing, twists and duals
    assert(mukaiPairing(2, {1, 0, 1}, {1, 0, 1}) == -2);
    assert(twistVector(2, {1, 0, 1}, 1) == {1, 1, 3});
    assert(twistVector(3, twistVector(3, {4, -1, 1}, 2), -2) == {4, -1, 1});
    assert(dualVector {3, -1, 1} == {3, 1, 1});
///

TEST ///
    -- the quartic surface: the surface itself and the two line bundles
    K = k3Surface 2;
    X = K#"variety";
    assert(instance(K, K3Surface));
    assert(dim X == 2);
    assert(degree X == 4);
    assert(cohomologyDims(OO_X^1) == {1, 0, 1});
    assert(cohomologyDims(OO_X^1(1)) == {4, 0, 0});
    assert(extDims(OO_X^1(1), OO_X^1) == {0, 0, 4});
///

TEST ///
    -- the quartic surface: every invariant of the fast list
    K = k3Surface 2;
    scan(sheafInvariants K, r -> assert(r#1 === r#2));
///

TEST ///
    -- a second quartic, from another seed and another prime field
    K = k3Surface(2, Seed => 7, Characteristic => 10007);
    scan(sheafInvariants K, r -> assert(r#1 === r#2));
///

TEST ///
    -- degree 6: a quadric and a cubic in P^4
    K = k3Surface 3;
    assert(degree K#"variety" == 6);
    scan(sheafInvariants K, r -> assert(r#1 === r#2));
///

TEST ///
    -- degree 8: three quadrics in P^5
    K = k3Surface 4;
    assert(degree K#"variety" == 8);
    scan(sheafInvariants K, r -> assert(r#1 === r#2));
///

TEST ///
    -- slow
    -- on the quartic, three of the numbers again as Ext groups
    K = k3Surface 2;
    X = K#"variety";
    assert(extDims(OO_X^1, OO_X^1(1)) == {4, 0, 0});
    assert(extDims(OO_X^1(1), kernelBundle K) == {0, 1, 15});
    assert(extDims(pointKernelBundle K, pointSheaf K) == {2, 0, 0});
///

TEST ///
    -- the classes of the catalogue have the ranks of the sheaves, and chi(O, F) = r + s
    K = k3Surface 2;
    scan(catalogue K, a -> (
        assert(rank a#1 == a#2#0);
        if a#3 and a#2#0 <= 3 then (
            h := cohomologyDims a#1;
            assert(h#0 - h#1 + h#2 == a#2#0 + a#2#2));
        ));
///

TEST ///
    -- the catalogue one sheaf at a time agrees with the whole catalogue
    K = k3Surface 2;
    cat = catalogue K;
    assert(apply(cat, a -> {a#0, a#2, a#3}) == catalogueClasses K);
    assert(#cat == 22);
    a = catalogueEntry(K, "M_H^dual(1H)");
    assert(a#2 == {3, 4, 11} and a#3 and rank a#1 == 3);
    assert(#catalogueClasses k3Surface(3, SpecialQuadric => true) == 26);
    assert(try (catalogueEntry(K, "no such sheaf"); false) else true);
///

TEST ///
    -- slow
    -- the rank 2 bundle on the degree 6 surface with the special quadric: class (2, 1, 2), spherical
    K = k3Surface(3, SpecialQuadric => true);
    U = mukaiBundle K;
    assert(rank U == 2);
    assert(cohomologyDims U == {4, 0, 0});
    assert(extViaHom(U, U) == {1, 0, 1});
///

TEST ///
    -- slow
    -- Ext groups through Hom sheaves and Serre duality, against known values on the quartic
    K = k3Surface 2;
    cat = catalogue K;
    pick = name -> first select(cat, a -> a#0 == name);
    assert((extTableRow(2, pick "M_H", pick "M_H"))#2 == {1, 0, 1});
    assert((extTableRow(2, pick "O(1H)", pick "M_H"))#2 == {0, 1, 15});
    assert((extTableRow(2, pick "I_x(1H)", pick "M_x"))#2 == {0, 1, 10});
    assert((extTableRow(2, pick "M_x", pick "O_x"))#2 == {2, 0, 0});
///

TEST ///
    assert(try (k3Surface(2, Characteristic => 4); false) else true);
    K = k3Surface 2;
    X = K#"variety";
    P = pointSheaf K;
    H = catalogueEntry(K, "O(1H)");
    p = catalogueEntry(K, "O_x");
    assert(extDims(P, P) == {1, 2, 1});
    assert(try (extViaHom(P, P); false) else true);
    assert(extViaHom(OO_X^1, P) == {1, 0, 0});
    assert(extViaHom(pointKernelBundle K, P) == {2, 0, 0});
    -- The irrelevant ideal represents the structure sheaf and is not a free graded module.
    S = K#"ring";
    E = sheaf module ideal vars S;
    assert(not isFreeModule module E);
    assert(extViaHom(E, P) == {1, 0, 0});
    assert(extTableRow(H, H) == {"O(1H)", "O(1H)", {1, 0, 1}, 2, "Hom sheaf"});
    assert(extTableRow(2, H, H) == extTableRow(H, H));
    assert(try (extTableRow(3, H, H); false) else true);
    assert(extTableRow(p, H) == {"O_x", "O(1H)", {0, 0, 1}, 1, "Serre duality"});
    assert(extTableRow(p, p) == {"O_x", "O_x", null, 0, "not computed"});
    assert(try (extTableRow(2, {p#0, p#1, p#2, true}, p); false) else true);
    assert(try (extTableRow(2, {H#0, H#1, {1, 1, 2}, H#3}, H); false) else true);

    K' = k3Surface(2, Seed => 7);
    H' = catalogueEntry(K', "O(1H)");
    assert(try (extTableRow(H, H'); false) else true);
    assert(try (extViaHom(H#1, H'#1); false) else true);
    assert(try (extDims(H#1, H'#1); false) else true);
///

TEST ///
    -- one invariant at a time agrees with the list
    K = k3Surface 2;
    names = sheafInvariantNames K;
    assert(#names == 15 and #sheafInvariantNames(K, Slow => true) == 22);
    assert(sheafInvariant(K, "h^i(M_H(-H))") == {"h^i(M_H(-H))", {0, 1, 15}, {0, 1, 15}});
    assert(apply(sheafInvariants K, first) == names);
///

TEST ///
    -- a batch description expands to tasks in the order given, with unique ids and a cost
    spec = new HashTable from {
        "surfaces" => {new HashTable from {"d" => 2}, new HashTable from {"d" => 3, "special_quadric" => true}},
        "tasks" => {
            new HashTable from {"kind" => "ext_pair", "sheaves" => {"O", "M_H", "O_x"}},
            new HashTable from {"kind" => "invariant", "names" => {"rank M_H"}},
            new HashTable from {"kind" => "synthetic", "items" => {new HashTable from {"name" => "idle"}}}}};
    tasks = expandBatch spec;
    assert(#tasks == 9 + 9 + 2 + 1);
    assert(#unique apply(tasks, t -> t#"id") == #tasks);
    t = first tasks;
    assert(t#"id" == "ext_pair/d2-p32003-s1/O/O" and t#"cost" == 1 and t#"set" == 0);
    assert(t#"surface"#"seed" == 1 and t#"surface"#"characteristic" == 32003);
    cost = id -> (first select(tasks, t -> t#"id" == id))#"cost";
    assert(cost "ext_pair/d2-p32003-s1/M_H/M_H" == 9);
    assert(cost "ext_pair/d2-p32003-s1/O_x/O_x" == 0);
    assert(cost "ext_pair/d3q-p32003-s1/M_H/O_x" == 4);
    assert(try (expandBatch new HashTable from {"tasks" => {new HashTable from {"kind" => "other"}}}; false) else true);
///

TEST ///
    -- tasks of each kind, with the three outcomes
    surface = new HashTable from {"d" => 2, "seed" => 1, "characteristic" => 32003, "special_quadric" => false};
    pair = (E, F) -> runTask new HashTable from {
        "kind" => "ext_pair", "surface" => surface, "source" => E, "target" => F};
    r = pair("O(1H)", "M_H");
    assert(r#"status" == "ok" and r#"value"#"dims" == {0, 1, 15} and r#"value"#"chi" == 14);
    assert(r#"predicted"#"chi" == 14 and r#"agrees" and r#"method" == "Hom sheaf");
    r = pair("I_x(1H)", "M_x");
    assert(r#"value"#"dims" == {0, 1, 10} and r#"method" == "Serre duality");
    r = pair("O_x", "I_x");
    assert(r#"status" == "unsupported" and r#"value" === null and r#"predicted"#"chi" == 1);
    r = runTask new HashTable from {"kind" => "invariant", "surface" => surface, "name" => "h^i(Q)"};
    assert(r#"status" == "ok" and r#"value" == {15, 1, 0});
    synthetic = (value, predicted) -> runTask new HashTable from {
        "kind" => "synthetic", "sleep_seconds" => 0, "allocate_mb" => 1, "fail" => false,
        "value" => value, "predicted" => predicted};
    assert((synthetic(null, null))#"status" == "ok");
    assert((synthetic(1, 2))#"status" == "mismatch");
///

TEST ///
    -- External kinds use the same registry as the runner without editing dispatcher code.
    descriptor = hashTable {
        "version" => 3,
        "requirements" => {"test-fixture"},
        "validate_set" => (s -> assert(s#"kind" == "example")),
        "validate_task" => (t -> assert(instance(t#"number", ZZ))),
        "validate_result" => (r -> assert(instance(r#"value", ZZ))),
        "expand" => ((i, s, models) -> {hashTable {
                    "kind" => "example", "id" => "example/1", "group" => "example",
                    "set" => i, "cost" => 0, "number" => 11
                    }}),
        "run" => (t -> hashTable {
                    "value" => t#"number" + 1, "predicted" => 12, "agrees" => true,
                    "method" => "example", "setup_seconds" => 0, "compute_seconds" => 0
                    })
        };
    registerTaskKind("example", descriptor);
    tasks = expandBatch hashTable {"tasks" => {hashTable {"kind" => "example"}}};
    t = first tasks;
    assert(t#"kind_version" == 3 and t#"requirements" == {"test-fixture"});
    assert((runTask t)#"value" == 12);
    assert(try (registerTaskKind("example", descriptor); false) else true);
    assert(try (runTask merge(t, hashTable {"kind_version" => 4}, (a,b) -> b); false) else true);
///
