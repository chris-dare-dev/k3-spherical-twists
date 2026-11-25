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

TEST ///
    needsPackage "Complexes";
    NS = markedDivisorLattice(QQ,{"C","F"},matrix{{-2,1},{1,0}});
    v = (a,b) -> divisorClass(NS,{a,b});
    wall = a -> curveWallMark(v(1,2),v(1,0),{v(a,0),4},{2,-1});
    S = QQ[s,n,Degrees=>{0,0}];
    p = ideal(s,n);
    eval = I -> map(complex(S^1/I),complex(S^1),hashTable {0=>map(S^1/I,S^1,{{1}})});
    -- Same evaluation on different lifts of the curve degree and in different strips.
    scan({{-1,-2,0,2},{-3,-2,0,1},{-1,-1,0,1},{-1,0,0,0},{-1,2,0,0}}, t -> (
        (a,b,c,m) := toSequence t;
        f := eval(p^2);
        cut := curveWallIdealCut(wall a,v(b,c),n,f);
        j := cut#"inclusion";
        g := cut#"projection";
        assert(cut#"curveSteps" == m and cut#"tailDivisor"#"coordinates" == {b+m,c});
        assert(target j == cone f and ann HH_0 source j == n^m*p^2);
        assert(isComplexMorphism j and isComplexMorphism g and g_1 == n^m*id_(S^1));
        comparison := map(target g,cone j,hashTable {1=>(id_(S^1) | g_1)});
        assert(certifiesCutSquare(comparison,id_(target g),comparison,id_(target g)));
        ));
    emptyEval = map(complex(S^0),complex(S^1),0);
    emptyCut = curveWallIdealCut(wall(-1),v(0,0),n,emptyEval);
    assert(HH_0 source emptyCut#"inclusion" == 0);
    offCurve = curveWallIdealCut(wall(-1),v(-2,0),1_S,eval p);
    assert(ann HH_0 source offCurve#"inclusion" == p);
    assert(try (wall 0; false) else true);
    assert(try (curveWallIdealCut(wall(-1),v(0,1),n,eval p); false) else true);
    assert(try (curveWallIdealCut(wall(-1),v(0,0),0_S,eval p); false) else true);
    assert(try (curveWallIdealCut(wall(-1),v(0,0),n,eval ideal n); false) else true);
    assert(try (curveWallIdealCut(wall(-1),v(0,0),n,0*(eval p)); false) else true);
///

TEST ///
    needsPackage "Complexes";
    S = QQ[s,n,Degrees=>{0,0}];
    T = S^1/ideal(n^2);
    V = S^1/ideal(s);
    E = complex(T ++ V);
    j = curveTorsionPreimage(E,n);
    assert(target j === E and isComplexMorphism j);
    assert(ann HH_0 source j == ideal(n^2) and ann HH_0 cone j == ideal(s));
    assert(HH_0 source curveTorsionPreimage(complex V,n) == 0);
    assert(HH_0 cone curveTorsionPreimage(complex T,n) == 0);
    F = complex(S^1,Base=>1);
    assert(curveTorsionPreimage(F,n) == id_F);
    assert(try (curveTorsionPreimage(complex(S^1,Base=>-1),n); false) else true);
///
