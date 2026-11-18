-- Construct a smooth quartic containing its marked rational curve.

generateMarkedQuartic = (recipe, curveDegree) -> (
    package := needsPackage "K3Surfaces";
    makeK3 := value(package.Dictionary#"K3");
    pointOn := value((needsPackage "Cremona").Dictionary#"point");
    setRandomSeed recipe#"parameters"#"seed";
    V := makeK3(3, curveDegree, -2, CoefficientRing => recipe#"field");
    equation := first flatten entries gens ideal V(1, 0);
    C := V#"curve";
    ({equation}, ideal pointOn C, ideal C)
    )

markedQuarticEquations = recipe -> (
    params := recipe#"parameters";
    if not params#?"model" then return generateMarkedQuartic(recipe, markedQuarticDegrees#(recipe#"family"));
    data := params#"model";
    x := getSymbol "x";
    R := (recipe#"field")(monoid[x_0..x_3]);
    ({quarticPolynomial(R, data#"equation")},
        ideal apply(data#"point", terms -> quarticPolynomial(R, terms)),
        ideal apply(data#"curve", terms -> quarticPolynomial(R, terms)))
    )

validateMarkedQuartic = (I, point, curve, curveDegree) -> (
    R := ring I;
    if numgens R != 4 or degrees I =!= {{4}} then error "expected a quartic in four homogeneous coordinates";
    if R =!= ring curve or R =!= ring point then error "markings must belong to the quartic ambient ring";
    if codim curve != 2 or degree(R/curve) != curveDegree then
        error "the marked curve has the wrong dimension or degree";
    if not isSubset(I, curve) then error "the marked curve is not contained in the quartic";
    if dim(curve + minors(2, jacobian curve)) > 0 then error "the marked curve is singular";
    if codim point != 3 or degree(R/point) != 1 or not isSubset(curve, point) then
        error "the marked point must be a rational point on the marked curve";
    )

requireMarkedCurve = K -> (
    markings := K#"markedIdeals";
    if not markings#?"curve" then error "the surface has no marked curve";
    markings#"curve"
    )

markedCurveClass = method()
markedCurveClass K3Surface := DivisorClass => K -> (
    requireMarkedCurve K;
    divisorClass(K#"lattice", {0, 1})
    )

markedCurveSheaf = method()
markedCurveSheaf K3Surface := CoherentSheaf => K ->
    cached(K, "O_C", () -> sheaf((K#"ring")^1 / requireMarkedCurve K))

markedQuarticSpec = method()
markedQuarticSpec K3Surface := HashTable => K -> (
    requireMarkedCurve K;
    S := K#"ring";
    R := ambient S;
    p := K#"characteristic";
    -- Pull both ideals back to the ambient ring. The surface equation is redundant
    -- in the preimages because the marked point and curve are contained in the surface.
    inclusion := map(S, R, gens S);
    data := hashTable {
        "equation" => quarticPolynomialData(first K#"equations", p),
        "curve" => quarticGeneratorsData(preimage(inclusion, K#"markedIdeals"#"curve"), p),
        "point" => quarticGeneratorsData(preimage(inclusion, K#"point"), p)
        };
    merge(K#"recipe"#"parameters", hashTable {"model" => data}, (a, b) -> b)
    )
