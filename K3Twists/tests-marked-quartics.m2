TEST ///
    assert(k3Families() === {"complete_intersection", "quartic_with_conic", "quartic_with_line"});
    scan({("quartic_with_line", 1), ("quartic_with_conic", 2)}, (family, d) -> (
            spec := hashTable {"family" => family};
            K := realizeK3Surface k3Recipe spec;
            assert(char K#"field" == 32003);
            assert(degree K#"variety" == 4);
            assert(K#"lattice"#"gram" == matrix {{4, d}, {d, -2}});
            H := K#"polarization";
            C := markedCurveClass K;
            assert(divisorPairing(H, C) == d and divisorPairing(C, C) == -2);
            S := K#"ring";
            R := ambient S;
            q := map(S, R, gens S);
            I := ideal K#"equations";
            J := trim preimage(q, K#"markedIdeals"#"curve");
            assert(isSubset(I, J) and degree(R/J) == d);
            assert(dim(I + ideal flatten entries jacobian I) == 0);
            assert(dim(J + minors(2, jacobian J)) <= 0);
            assert(isSubset(K#"markedIdeals"#"curve", K#"point"));
            OC := markedCurveSheaf K;
            assert(cohomologyDims OC === {1, 0, 0});
            pin := markedQuarticSpec K;
            T := realizeK3Surface k3Recipe pin;
            assert(markedQuarticSpec T === pin);
            assert(cohomologyDims markedCurveSheaf T === {1, 0, 0});
            if d == 1 then (
                assert(extDims(OC, OC) === {1, 0, 1});
                TC := markedCurveSheaf T;
                assert(extDims(TC, TC) === {1, 0, 1});
                );
            ));
///

TEST ///
    -- Two lines on the same smooth Fermat quartic over ZZ/17.
    data := a -> (
        x := {{{1, 0, 0, 0}, 1}, {{0, 1, 0, 0}, -a}};
        y := {{{0, 0, 1, 0}, 1}};
        z := {{{0, 0, 0, 1}, 1}};
        hashTable {
            "equation" => apply(4, i -> {apply(4, j -> if i == j then 4 else 0), 1}),
            "curve" => {x, append(y, {{0, 0, 0, 1}, -2})},
            "point" => {x, y, z}
            }
        );
    mkSpec := a -> hashTable {"family" => "quartic_with_line", "characteristic" => 17, "model" => data a};
    sets := {
        hashTable {"kind" => "invariant", "names" => {"h^i(O_C)"}},
        hashTable {"kind" => "ext_pair", "sheaves" => {"O", "O(1H)"}}
        };
    tasks := expandBatch hashTable {"surfaces" => {mkSpec 2, mkSpec(-2)}, "tasks" => sets};
    lineTasks := select(tasks, task -> task#"kind" === "invariant");
    assert(#lineTasks == 2 and lineTasks#0#"id" =!= lineTasks#1#"id");
    assert(lineTasks#0#"surface"#"model"#"equation" === lineTasks#1#"surface"#"model"#"equation");
    assert(lineTasks#0#"surface"#"model"#"curve" =!= lineTasks#1#"surface"#"model"#"curve");
    scan(lineTasks, t -> (
            result := runTask t;
            assert(result#"status" === "ok" and result#"value" === {1, 0, 0});
            ));
    cross := first select(tasks, task -> task#"kind" === "ext_pair"
        and task#"source" === "O" and task#"target" === "O(1H)");
    assert((runTask cross)#"value"#"dims" === {4, 0, 0});
    -- The model is structurally valid, but the line on this record is not on the quartic.
    assert(try (realizeK3Surface k3Recipe mkSpec 1; false) else true);
    assert(try (k3Recipe hashTable {"family" => "quartic_with_line", "d" => 3}; false) else true);
    assert(try (k3Recipe hashTable {"family" => "quartic_with_conic", "model" => data 2}; false) else true);
///
