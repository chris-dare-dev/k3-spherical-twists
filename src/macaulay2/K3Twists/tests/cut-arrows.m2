TEST ///
    needsPackage "Complexes";
    R = QQ[u,v];
    k = R^1/ideal(u,v);
    soc = k ** R^{-1};
    A = complex(map(R^1/ideal(v,u^2), soc, {{u}}), Base => -1);
    B = (complex soc) ++ complex(k, Base => -1);
    f = map(B,A,hashTable {0 => id_soc});
    F = complex koszul matrix {{u,v}};
    -- Direct output truncation independently checks the signed input algorithm
    -- at interior cuts, beyond both endpoints, and on acyclic inputs/outputs.
    scan({f, id_A, 0*id_F, id_F, id_(complex R^0)}, g -> scan({1,-1}, direction -> (
        C := if direction == 1 then cone g else (cone g)[1];
        scan(-2..3, q -> (
            direct := homologicalCutInclusion(C,q);
            corrected := signedCutInclusion(C,g,direction,q);
            s := map(source corrected, source direct, i -> direct_i // corrected_i);
            assert(target corrected === C and certifiesCutSquare(direct,corrected,s,id_C));
            ))
        )));
    assert(try (signedCutInclusion(cone f,f,0,0); false) else true);
    assert(try (signedCutInclusion(cone f,f,-1,0); false) else true);
///

TEST ///
    needsPackage "Complexes";
    R = QQ[u,v];
    k = R^1/ideal(u,v);
    A = complex k;
    B = A ++ A;
    a = map(B,A,hashTable {0 => map(B_0,k,{{1},{0}})});
    b = map(B,A,hashTable {0 => map(B_0,k,{{0},{1}})});
    swap = map(B,B,hashTable {0 => map(B_0,B_0,{{0,1},{1,0}})});
    -- Both inclusions have source k and cokernel k. Fixing the target matters.
    assert(not certifiesCutSquare(a,b,id_A,id_B));
    assert(certifiesCutSquare(a,b,id_A,swap));
    assert(not certifiesCutSquare(a,b,id_B,swap));
    -- Both zero vertical maps commute, but their cones have bottom homology.
    Z = complex(R^0, Base => 0);
    z = map(A,Z,0);
    assert(not certifiesCutSquare(id_Z,id_A,z,z));
///

TEST ///
    K = k3Surface 2;
    S = sphericalObject structureObject K;
    positive = twistWord {twistStep(S,1)};
    negative = inverseTwistWord positive;
    point = catalogueObject(K, "O_x");
    rep = (realizeTwistImage(positive, point))#"representative";
    assert((realizeTwistImage(negative, rep))#"representative" === point);
    scan({-1,0,2}, n -> (
        E := shiftObject(catalogueObject(K,"I_x"),n);
        Y := realizeTwistImage(negative,E);
        assert(Y#"representative" === shiftObject(point,n-1));
        assert(Y#"complex" == (cone Y#"chainMap")[1]);
        ))
///
