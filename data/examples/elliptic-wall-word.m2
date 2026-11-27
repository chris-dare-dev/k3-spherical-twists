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
    wall := curveWallMark(H,section,{fourBeta,4},z);
    curveCutoff := wall#"curveCutoff";
    charge := w -> (
        c := (asMukai w)#"divisor";
        {(1+z#0)*w#0-w#3+divisorPairing(fourBeta,c)/4,divisorPairing(H,c)+z#1*w#0}
        );
    add := (w,v) -> apply(w,v,(a,b)->a+b);
    times := (k,w) -> apply(w,a->k*a);
    O := {1,0,0,1};
    P := {0,0,0,1};
    line := (a,b) -> coords tensorByDivisor(asMukai O,divisor {a,b});
    L := line(-2,0);
    K := line(-1,2);

    -- On the elliptic surface K-L has fibre degree one. Its sections have
    -- fixed part C, and division by the section pulls back the full binary system.
    difference := apply((asMukai K)#"divisor"#"coordinates",(asMukai L)#"divisor"#"coordinates",(a,b)->a-b);
    assert(difference#0 == 1 and difference#1 >= 0);
    baseRing := QQ[local u,local v];
    quadratics := basis(difference#1,baseRing);
    relationsOnBase := transpose syz quadratics;
    assert(relationsOnBase * transpose quadratics == 0);
    assert(minors(numRows relationsOnBase,relationsOnBase) == (ideal(u,v))^(difference#1));
    relationDegrees := unique apply(select(flatten entries relationsOnBase,e -> e != 0),e -> first degree e);
    assert(#relationDegrees == 1);
    V := coords tensorByDivisor(asMukai K,divisor {0,first relationDegrees});
    numSections := numColumns quadratics;
    numQuotients := numRows relationsOnBase;
    -- Negative fibre degree kills H^2, so Riemann--Roch also gives H^1 = 0.
    assert(divisorPairing(divisor difference,divisor {0,1}) == 1);
    assert(2 + divisorPairing(divisor difference,divisor difference)//2 == numSections);

    -- Native complexes on the regular parameter chart, with line bundles
    -- trivialized. Their base changes to the completed local ring give the stalk
    -- tests. K, L and the exterior quotient have different global line classes.
    S := QQ[local s,local n,Degrees=>{0,0}];
    kPoint := S^1 / ideal(s,n);
    j := map(S^numSections,S^1,entries sub(transpose quadratics,{u=>s+pointFibre,v=>1_S}));
    qBase := map(S^numQuotients,S^numSections,entries sub(relationsOnBase,{u=>s+pointFibre,v=>1_S}));
    assert(qBase*j == 0 and coker qBase == 0);

    quasi := f -> certifiesCutSquare(f,id_(target f),f,id_(target f));
    evaluation := map(complex kPoint,complex S^1,hashTable {0=>map(kPoint,S^1,{{1}})});
    cut := curveWallIdealCut(wall,(asMukai L)#"divisor",n,evaluation);
    firstCut := cut#"inclusion";
    firstCone := target firstCut;
    tailProjection := cut#"projection";
    tailLine := coords tensorByDivisor(asMukai O,cut#"tailDivisor");
    -- Compare the computed boundary over the retained evaluation cone. Resolve
    -- its source using the kernel of the actual evaluation, in the same frame.
    h := gens ker evaluation_0;
    d := syz h;
    idealShift := complex(d,Base=>1);
    toFirst := map(firstCone,idealShift,hashTable {1=>h});
    assert(quasi toFirst);
    inKernel := h // firstCut_1;
    thickRow := (source firstCut).dd_1 * inKernel;
    thick := complex {thickRow,d};
    toCut := map(source firstCut,thick,hashTable {0=>id_(S^1),1=>inKernel});
    boundary := map(idealShift,thick,hashTable {1=>id_(S^2),2=>id_(S^1)});
    assert(certifiesCutSquare(boundary,firstCut,toCut,toFirst));
    lineShift := target tailProjection;
    firstQuotient := map(lineShift,cone firstCut,hashTable {1=>(id_(S^1) | tailProjection_1)});
    assert(quasi firstQuotient and ann HH_0 source firstCut == ideal(n^2*s,n^3));

    -- Every ordinary homological cut has zero H_0 on the first output. Below
    -- and above its two chain degrees these cuts are already constant.
    scan(-1..2, i -> assert(HH_0 source signedCutInclusion(firstCone,evaluation,1,i) == 0));
    assert(HH_0 thick != 0);

    -- Second twist. Ordinary Hom has three sections and Ext^1 has one
    -- generator. The source identification is the same toFirst used above.
    ordinary := j*n^(difference#0)*h;
    -- The global Ext^1(I,K) maps isomorphically to Ext^2(P,K). Its local
    -- generator is a lift of a generator in the dual of the point resolution.
    extAtPoint := coker transpose d;
    assert(numgens extAtPoint == 1 and ann extAtPoint == ideal(s,n));
    eta := map(S^1,source d,entries transpose gens extAtPoint);
    coTarget := complex(S^numSections,Base=>1) ++ complex(S^1,Base=>2);
    coevaluation := map(coTarget,idealShift,hashTable {1=>ordinary,2=>eta});
    fibre := (cone coevaluation)[1];
    -- Discover J on the raw fibre, before supplying an exterior quotient or
    -- choosing coordinates for its middle sheaf. Factor the top cut through J.
    intoFibre := curveTorsionPreimage(fibre,n);
    J := source intoFibre;
    (lo,hi) := concentration fibre;
    homologyDegrees := select(toList(lo..hi),i -> HH_i fibre != 0);
    assert(homologyDegrees == {0,1});
    upper := signedCutInclusion(fibre,coevaluation,-1,last homologyDegrees);
    intoJ := map(J,source upper,i -> upper_i // intoFibre_i);
    assert(isComplexMorphism intoJ and intoFibre*intoJ == upper);
    middle := cone intoJ;
    middleIdeal := ann HH_0 middle;
    assert(all(select(toList(0..(last concentration middle)),i -> i != 0),i -> HH_i middle == 0));
    assert(middleIdeal == ideal(n*s,n^2) and n % middleIdeal != 0);

    -- In the unit basis chosen by the dual resolution, cancel its free pair.
    -- Retain the comparison to
    -- the original fibre. The sign in degree zero is the Complexes fibre sign.
    reduced := complex ordinary;
    contract := map(reduced,fibre,hashTable {1=>(id_(S^2) | d),0=>-id_(S^numSections)});
    liftBack := map(fibre,reduced,hashTable {1=>(id_(S^2) || map(S^1,S^2,0)),0=>-id_(S^numSections)});
    assert(quasi contract and contract*liftBack == id_reduced);

    -- Identify the discovered arrows with free models and the global quotient.
    assert(saturate(image ordinary,ideal n) == image j);
    middleRow := ordinary // j;
    assert(j*middleRow == ordinary and ideal middleRow == middleIdeal);
    freeJ := complex middleRow;
    intoReduced := map(reduced,freeJ,hashTable {0=>j,1=>id_(S^2)});
    freeInclusion := liftBack*intoReduced;
    toJ := map(J,freeJ,i->freeInclusion_i // intoFibre_i);
    assert(certifiesCutSquare(freeInclusion,intoFibre,toJ,id_fibre));
    toOutside := map(complex(S^numQuotients),reduced,hashTable {0=>qBase})*contract;
    assert(toOutside*intoFibre == 0);
    lastQuotient := map(target toOutside,cone intoFibre,hashTable {0=>toOutside_0});
    assert(quasi lastQuotient);
    freeTop := map(freeJ,lineShift,hashTable {1=>d});
    top := freeInclusion*freeTop;
    topComparison := map(source upper,lineShift,hashTable {1=>top_1 // upper_1});
    assert(certifiesCutSquare(freeTop,intoJ,topComparison,toJ));
    midModule := S^1/middleIdeal;
    quotientMap := map(complex midModule,cone freeTop,hashTable {0=>map(midModule,S^1,1)});
    assert(quasi quotientMap);
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
    pointScalar := transpose(transpose middleRow // transpose h);
    middleScalar := transpose(transpose thickRow // transpose middleRow);
    includePoint := map(resMiddle,resPoint,hashTable {0=>pointScalar,1=>id_(S^2),2=>id_(S^1)});
    includeMiddle := map(thick,resMiddle,hashTable {0=>middleScalar,1=>id_(S^2),2=>id_(S^1)});
    onMiddle := coevaluation*boundary*includeMiddle;
    onPoint := onMiddle*includePoint;
    assert(isComplexMorphism includePoint and isComplexMorphism includeMiddle);
    assert(onMiddle_1 == j*resMiddle.dd_1);
    -- A null homotopy on R would express every column of the transpose
    -- through the transpose of its first differential.
    assert(not isSubset(image transpose ordinary,image transpose thickRow));
    coboundaries := ideal transpose d;
    assert(coboundaries == ideal(s,n) and onPoint_2_(0,0) % coboundaries == 1);
    -- Read the Yoneda two-extension straight from J. Lift the socle and its
    -- two relations, then express the remaining cycle modulo boundaries on
    -- the K axis. Reduction in the residue field removes the lift choices.
    attachingResidue := inclusion -> (
        U := source inclusion;
        lift0 := (-j*pointScalar) // inclusion_0;
        lift1 := (lift0*h) // U.dd_1;
        assert(inclusion_0*lift0 == -j*pointScalar and U.dd_1*lift1 == lift0*h);
        cycle := lift1*d;
        axis := (map(source h,S^1,0) || id_(S^1)) // inclusion_1;
        cycles := axis | U.dd_2;
        coefficients := cycle // cycles;
        assert(cycles*coefficients == cycle);
        coefficients_(0,0) % coboundaries
        );
    attachment := attachingResidue intoFibre;
    assert(attachment == onPoint_2_(0,0) % coboundaries);
    controls := apply({0_S,-1_S},e -> (
        f := map(coTarget,idealShift,hashTable {1=>ordinary,2=>e*eta});
        U := curveTorsionPreimage((cone f)[1],n);
        assert(ann HH_0 source U == middleIdeal);
        attachingResidue U
        ));
    assert(controls == {0_S,-1_S});

    E := coords mukaiReflection(asMukai P,asMukai L);
    Y := coords mukaiReflection(asMukai E,asMukai K);
    -- Dividing the ordinary Hom sections by their fixed part identifies the
    -- saturated line. The primitive relation degrees identify the outside line.
    D := coords tensorByDivisor(asMukai L,divisor {difference#0,0});
    -- D/I is an extension of D|_C by the finite-length L/I. Both are
    -- unshifted of imaginary charge zero by the marked curve cutoff.
    assert(divisorPairing((asMukai D)#"divisor",section) > curveCutoff);
    A := add(O,times(-1,line(-1,0)));
    B := add(P,times(-1,A));
    M := add(D,E);
    R := add(tailLine,E);
    assert(M == add(P,add(times(numSections,A),times(numQuotients,B))) and R == add(M,A));
    assert(Y == add(times(-1,K),add(M,times(numQuotients,V))));

    -- A phase is (sheet, charge of the representative in the marked heart).
    -- On these lines the first tilt compares the H-slope with -Im(z).
    -- For an unshifted line the second tilt tests Hom to O_C(l), l <= k.
    -- A line above the slope cutoff with curve degree > k is in the heart:
    -- a torsion sheaf or a shifted sheaf has no map into this unshifted line.
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
    assert(divisorPairing(section,cut#"tailDivisor") <= curveCutoff+2);
    pO := linePhase(tailLine,1);
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
    -- For the first input triangle, apply the same hull rule to L[1]
    -- (empty point quotient). The other end P has phase one in the marked heart.
    emptyEvaluation := map(complex(S^0),source evaluation,0);
    inputLineCut := curveWallIdealCut(wall,(asMukai L)#"divisor",n,emptyEvaluation);
    inputTail := coords tensorByDivisor(asMukai O,inputLineCut#"tailDivisor");
    firstWindow := bounds {linePhase(inputTail,1),heartRay P};
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
    firstFactors := {R,times(-1,tailLine)};
    secondFactors := {times(-1,K),M,times(numQuotients,V)};
    << "Marked curve cutoff, additions and residual line  " << toString {curveCutoff,cut#"curveSteps",cut#"tailDivisor"#"coordinates"} << endl;
    << "Input windows (sheet, charge in heart)  " << toString {firstWindow,secondWindow} << endl;
    << "Strict cuts for R, K[1] and J respectively  " << toString {pO,heartRay M,pV} << endl;
    << "First factor charges  " << toString apply(firstFactors,charge)
        << "   Mass terms  " << toString mass firstFactors << endl;
    << "Second factor charges  " << toString apply(secondFactors,charge)
        << "   Mass terms  " << toString mass secondFactors << endl;
    << "First cone gives R -> I[1] -> O[1]. Every ordinary cut has zero H_0." << endl;
    << "Inverse fibre gives K[1] -> J -> Y with quotients K[1], M_(2,x), V^2." << endl;
    << "Point restriction from the tower and from coevaluation  " << toString {attachment,onPoint_2_(0,0) % coboundaries} << endl;
    << "Split and sign-reversed attachments from the raw fibres  " << toString controls << endl;
    );
runWallWord();
