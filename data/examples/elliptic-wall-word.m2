-- T_K^{-1} T_L(k_x) on the Meinsma--Shinder elliptic K3, Example 3.13.
-- M2 --script data/examples/elliptic-wall-word.m2
path = prepend(currentFileDirectory | "../../src/macaulay2/",path);
needsPackage "K3Twists";
needsPackage "Complexes";

runWallWord = () -> (

    -- The point is on the zero section at t=2. In the Y=1 chart of the
    -- Weierstrass equation, s=t-2 and n=X/Y are parameters at this point.
    chart := QQ[local t,local a,local b];
    weierstrass := b-a^3-(t^12-t)*b^3;
    pointFibre := 2;
    atPoint := {t=>pointFibre,a=>0,b=>0};
    assert(sub(t^12-t,atPoint) != 0 and sub(weierstrass,atPoint) == 0
        and sub(diff(b,weierstrass),atPoint) == 1);

    -- Global coevaluation divided by its fixed section C. The binary syzygies
    -- identify the quotient on the whole base, including the fibre at infinity.
    baseRing := QQ[local u,local v];
    quadratics := matrix{{v^2,u*v,u^2}};
    relationsOnBase := matrix{{u,-v,0},{0,u,-v}};
    assert(relationsOnBase * transpose quadratics == 0);
    assert(minors(2,relationsOnBase) == (ideal(u,v))^2);
    numSections := numColumns quadratics;
    numQuotients := numRows relationsOnBase;

    -- Native complexes on the regular parameter chart, with line bundles
    -- trivialized. Their base changes to the completed local ring give the stalk
    -- tests. K, L and the exterior quotient have different global line classes.
    S := QQ[local s,local n,Degrees=>{0,0}];
    h := matrix{{s,n}};
    d := transpose matrix{{-n,s}};
    kPoint := S^1 / ideal(s,n);
    j := map(S^numSections,S^1,entries sub(transpose quadratics,{u=>s+pointFibre,v=>1_S}));
    qBase := map(S^numQuotients,S^numSections,entries sub(relationsOnBase,{u=>s+pointFibre,v=>1_S}));
    assert(h*d == 0 and qBase*j == 0 and coker qBase == 0);

    quasi := f -> certifiesCutSquare(f,id_(target f),f,id_(target f));
    -- First twist. The free model of I[1] maps to the retained evaluation cone.
    evaluation := map(complex kPoint,complex S^1,hashTable {0=>map(kPoint,S^1,{{1}})});
    firstCone := cone evaluation;
    idealShift := complex(d,Base=>1);
    toFirst := map(firstCone,idealShift,hashTable {1=>h});
    assert(quasi toFirst);

    -- In the global inclusion I_x L -> O, the fixed section has divisor 2C.
    -- Its saturation along C gives O and the quotient R. Take the actual
    -- boundary R -> I[1] and compare over the retained first twist.
    thickRow := n^2*h;
    assert(saturate(ideal thickRow,ideal n) == ideal(1_S));
    thick := complex {thickRow,d};
    boundary := map(idealShift,thick,hashTable {1=>id_(S^2),2=>id_(S^1)});
    firstCut := map(firstCone,thick,hashTable {1=>h});
    assert(certifiesCutSquare(boundary,firstCut,id_thick,toFirst));
    lineShift := complex(S^1,Base=>1);
    firstQuotient := map(lineShift,cone firstCut,hashTable {1=>matrix{{1,n^2}}});
    assert(quasi firstQuotient and ann HH_0 thick == ideal(n^2*s,n^3));

    -- Every ordinary homological cut has zero H_0 on the first output. Below
    -- and above its two chain degrees these cuts are already constant.
    scan(-1..2, i -> assert(HH_0 source signedCutInclusion(firstCone,evaluation,1,i) == 0));
    assert(HH_0 thick != 0);

    -- Second twist. Ordinary Hom has three sections and Ext^1 has one
    -- generator. The source identification is the same toFirst used above.
    ordinary := j*n*h;
    saturatedLine := saturate(image ordinary,ideal n);
    assert(saturatedLine == image j and ann(saturatedLine / image ordinary) == ideal(n*s,n^2));
    coTarget := complex(S^numSections,Base=>1) ++ complex(S^1,Base=>2);
    coevaluation := map(coTarget,idealShift,hashTable {1=>ordinary,2=>id_(S^1)});
    fibre := (cone coevaluation)[1];
    -- Cancel the unit of the higher component, retaining the comparison to
    -- the original fibre. The sign in degree zero is the Complexes fibre sign.
    reduced := complex ordinary;
    contract := map(reduced,fibre,hashTable {1=>(id_(S^2) | d),0=>-id_(S^numSections)});
    liftBack := map(fibre,reduced,hashTable {1=>(id_(S^2) || map(S^1,S^2,0)),0=>-id_(S^numSections)});
    assert(quasi contract and contract*liftBack == id_reduced);

    -- The saturation is the line spanned by j. Dividing by the ordinary image
    -- recovers the middle sheaf. Its defining ideal retains the embedded point.
    satLine := saturate(image ordinary,ideal n);
    assert(satLine == image j);
    middleSheaf := satLine / image ordinary;
    middleRow := ordinary // j;
    assert(j*middleRow == ordinary and middleRow == n*h);
    middleIdeal := ideal middleRow;
    assert(ann middleSheaf == middleIdeal and middleIdeal == ideal(n*s,n^2) and n % middleIdeal != 0);

    -- J is the inverse image of this saturated line. Compare its inclusion
    -- with the kernel of the degreewise surjection from the uncontracted fibre.
    J := complex middleRow;
    intoReduced := map(reduced,J,hashTable {0=>j,1=>id_(S^2)});
    intoFibre := liftBack*intoReduced;
    toOutside := map(complex(S^numQuotients),reduced,hashTable {0=>qBase})*contract;
    pullback := kernel toOutside;
    pullbackInclusion := map(fibre,pullback,i->inducedMap(fibre_i,pullback_i));
    toPullback := map(pullback,J,i->intoFibre_i // pullbackInclusion_i);
    assert(certifiesCutSquare(intoFibre,pullbackInclusion,toPullback,id_fibre));
    lastQuotient := map(target toOutside,cone intoFibre,hashTable {0=>toOutside_0});
    assert(quasi lastQuotient);

    -- Top inclusion K[1] -> J. Its cone maps onto M via the residue map.
    intoJ := map(J,lineShift,hashTable {1=>d});
    midModule := S^1/middleIdeal;
    toMiddle := map(complex midModule,cone intoJ,hashTable {0=>map(midModule,S^1,{{1}})});
    assert(quasi toMiddle);
    top := intoFibre*intoJ;
    upper := signedCutInclusion(fibre,coevaluation,-1,1);
    topComparison := map(source upper,lineShift,hashTable {1=>top_1 // upper_1});
    assert(certifiesCutSquare(top,upper,topComparison,id_fibre));
    -- The next cut includes nonzero torsion in degree zero. Ordinary truncation
    -- there either keeps the entire positive-rank H_0 or has zero H_0.
    assert(HH_0 J != 0 and ann HH_0 J == middleIdeal);
    scan(-1..3, i -> (
        U := source signedCutInclusion(fibre,coevaluation,-1,i);
        assert(if i <= 0 then ann HH_0 U == ideal(0_S) else HH_0 U == 0)
        ));

    -- Follow P -> M -> R through the first boundary and the full coevaluation.
    -- On M the ordinary component factors through its differential (a null
    -- homotopy). The higher component restricts to 1 modulo the Koszul boundaries.
    resPoint := complex {h,d};
    resMiddle := complex {middleRow,d};
    includePoint := map(resMiddle,resPoint,hashTable {0=>n*id_(S^1),1=>id_(S^2),2=>id_(S^1)});
    includeMiddle := map(thick,resMiddle,hashTable {0=>n*id_(S^1),1=>id_(S^2),2=>id_(S^1)});
    onMiddle := coevaluation*boundary*includeMiddle;
    onPoint := onMiddle*includePoint;
    assert(isComplexMorphism includePoint and isComplexMorphism includeMiddle);
    assert(onMiddle_1 == j*resMiddle.dd_1);
    -- A null homotopy on R would express every column of the transpose
    -- through the transpose of its first differential.
    assert(not isSubset(image transpose ordinary,image transpose thickRow));
    coboundaries := ideal transpose d;
    assert(coboundaries == ideal(s,n) and onPoint_2_(0,0) % coboundaries == 1);
    splitControl := map(coTarget,idealShift,hashTable {1=>ordinary});
    assert((splitControl*boundary*includeMiddle*includePoint)_2 == 0);

    -- The marked charge in Chern characters is -ch2 + beta.c + Re(z)*r
    -- + i*(H.c + Im(z)*r). The Mukai coordinate s is r + ch2.
    NS := markedDivisorLattice(QQ,{"C","F"},matrix{{-2,1},{1,0}});
    divisor := coords -> divisorClass(NS,coords);
    asMukai := w -> mukaiClass(w#0,divisor {w#1,w#2},w#3);
    coords := w -> {w#"rank"} | (w#"divisor")#"coordinates" | {w#"eulerComponent"};
    H := divisor {1,2};
    section := divisor {1,0};
    fourBeta := divisor {-1,0};
    z := {2,-1};
    curveCutoff := -1;
    hSquare := divisorPairing(H,H);
    halfSelfIntersection := -divisorPairing(section,section)/2;
    betaC := divisorPairing(fourBeta,section)/4;
    assert(hSquare > 0 and divisorPairing(H,section) == 0 and divisorPairing(H,fourBeta) == 0);
    assert(curveCutoff+halfSelfIntersection < betaC and betaC < curveCutoff+halfSelfIntersection+1);
    assert(z#0+(z#1)^2/hSquare > -divisorPairing(fourBeta,fourBeta)/32);
    charge := w -> (
        c := (asMukai w)#"divisor";
        {(1+z#0)*w#0-w#3+divisorPairing(fourBeta,c)/4,divisorPairing(H,c)+z#1*w#0}
        );
    add := (w,v) -> apply(w,v,(a,b)->a+b);
    times := (k,w) -> apply(w,a->k*a);
    O := {1,0,0,1};
    P := {0,0,0,1};
    line := (a,b) -> coords tensorByDivisor(asMukai O,divisor {a,b});
    D := line(-1,0);
    L := line(-2,0);
    K := line(-1,2);
    V := line(-1,3);
    E := coords mukaiReflection(asMukai P,asMukai L);
    Y := coords mukaiReflection(asMukai E,asMukai K);
    A := add(O,times(-1,D));
    B := add(P,times(-1,A));
    M := add(D,E);
    R := add(O,E);
    assert(M == add(P,add(times(numSections,A),times(numQuotients,B))) and R == add(M,A));
    assert(Y == add(times(-1,K),add(M,times(numQuotients,V))));

    -- A phase is (sheet, charge of the representative in the marked heart).
    -- On these lines the first tilt compares the H-slope with -Im(z).
    -- For an unshifted line the second tilt tests Hom to O_C(l), l <= k.
    -- Stability uses the geometric no-phase-one-subobject results in the
    -- guide. The charge by itself supplies no such test.
    heartRay := w -> (
        c := charge w;
        assert(c#1 > 0 or (c#1 == 0 and c#0 < 0));
        {0,c}
        );
    linePhase := (w,shift) -> (
        c := (asMukai w)#"divisor";
        hShift := if divisorPairing(H,c) <= -z#1 then 1 else 0;
        assert(hShift == 1 or divisorPairing(section,c) > curveCutoff);
        {shift-hShift,(heartRay times((-1)^hShift,w))#1}
        );
    above := (a,b) -> if a#0 != b#0 then a#0 > b#0 else (
        x := a#1; y := b#1;
        x#0*y#1-x#1*y#0 < 0
        );
    bounds := phases -> {
        fold((a,b)->if above(a,b) then b else a,phases),
        fold((a,b)->if above(a,b) then a else b,phases)
        };
    assert((heartRay A)#1 == {-1/2,0} and (heartRay B)#1 == {-1/2,0});
    pO := linePhase(O,1);
    pK := linePhase(K,0);
    pK1 := linePhase(K,1);
    pV := linePhase(V,0);
    assert((pO#1)#1 == 1 and (pK#1)#1 == 1 and (pV#1)#1 == 2);
    -- A rigid V with two positive-imaginary stable constituents would have
    -- a root w=(r,a,r+1,s) with (V,w)=-1. Rule out every parity class.
    scan(0..1,r -> scan(0..1,a -> scan(0..1,e -> (
        w := asMukai {r,a,r+1,e};
        assert((mukaiPairing(w,w)+2)%4 != 0 or (mukaiPairing(asMukai V,w)+1)%2 != 0)
        ))));
    -- Obtain the input windows by taking extrema over the twist triangles.
    -- The first source shift has leaves O[1], A and B. At the second step
    -- RHom contributes K and K[1]. Each extremum carries its sheet.
    firstWindow := bounds {heartRay P,heartRay A,heartRay B,pO};
    secondWindow := bounds (firstWindow | {pK,pK1});
    assert(above(heartRay R,pO) and above(pK1,heartRay M) and above(heartRay M,pV));
    -- Exact mass as (square-free radicand, rational coefficient).
    mass := factors -> (
        sums := new MutableHashTable;
        scan(factors,w -> (
            norm := sum(charge w,x -> lift((4*x)^2,ZZ));
            k := 1;
            i := 1;
            while i*i <= norm do (if norm % (i*i) == 0 then k = i; i = i+1);
            rad := norm // (k*k);
            sums#rad = (if sums#?rad then sums#rad else 0) + k/4;
            ));
        apply(sort keys sums,rad->{rad,sums#rad})
        );
    firstFactors := {R,times(-1,O)};
    secondFactors := {times(-1,K),M,times(numQuotients,V)};
    << "Input windows (sheet, charge in heart)  " << toString {firstWindow,secondWindow} << endl;
    << "Strict cuts for R, K[1] and J respectively  " << toString {pO,heartRay M,pV} << endl;
    << "First factor charges  " << toString apply(firstFactors,charge)
        << "   Mass terms  " << toString mass firstFactors << endl;
    << "Second factor charges  " << toString apply(secondFactors,charge)
        << "   Mass terms  " << toString mass secondFactors << endl;
    << "First cone gives R -> I[1] -> O[1]. Every ordinary cut has zero H_0." << endl;
    << "Inverse fibre gives K[1] -> J -> Y with quotients K[1], M_(2,x), V^2." << endl;
    << "At x the attaching class is 1. Removing the higher component gives 0." << endl;
    );
runWallWord();
