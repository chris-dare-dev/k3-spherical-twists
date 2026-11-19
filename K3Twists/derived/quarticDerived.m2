-- Bounded additional strategies certified by duality and exact sequences on a smooth quartic.

lineCoordinates = E -> (
    if not E#?"definition" then return null;
    D := E#"definition";
    if D#"kind" === "line_bundle" then return D#"coordinates";
    if D#"kind" =!= "catalogue" then return null;
    K := E#"surface";
    H := K#"polarization"#"coordinates";
    if D#"name" === "O" then return apply(H, i -> 0);
    if D#"name" === "O(1H)" then return H;
    if D#"name" === "O(-1H)" then return apply(H, h -> -h);
    null
    )

unshiftReference = E -> if instance(E, ShiftedK3Object) then (E#"object", E#"shift") else (E, 0)

hyperplaneQuotientReference = K -> (
    L := K#"lattice";
    H := K#"polarization";
    v := mukaiClass(3, divisorClass(L, apply(H#"coordinates", i -> 4*i)), 11);
    newObjectReference(K, hashTable {"kind" => "hyperplane_quotient", "name" => "Q"}, v)
    )

realizedDerived = (E, representative, C, strategy, evidence, fields) -> (
    if numericalClass E =!= numericalClass representative then error "derived realization and reflection disagree";
    if not isWellDefined C then error "invalid realized complex";
    new TwistRealization from merge(hashTable {
        "status" => "realized", "symbolic" => E, "reason" => null, "complex" => C,
        "representative" => representative, "strategy" => strategy,
        "homologicalToCohomological" => "i -> -i", "hypotheses" => evidence
        }, fields, (a,b) -> b)
    )

degreeZeroCone = (f, shift) -> (
    F := complex source f;
    G := complex target f;
    u := map(G, F, i -> f);
    C := if shift == 0 then cone u else complex({if shift % 2 == 0 then f else -f}, Base => shift);
    (u, C)
    )

quarticCoevaluation = (E, input, shift) -> (
    K := E#"surface";
    X := K#"variety";
    R := K#"ring";
    H := (OO_X^1)(1);
    if cohomologyDims H =!= {4, 0, 0} then error "derived Hom to O(H) must be concentrated in degree zero";
    -- The four coordinates and their dual basis give the two maps in the evaluation sequence.
    f := map(R^{4 : 1}, R^1, transpose vars R);
    (u, C) := degreeZeroCone(f, shift - 1);
    if sheaf HH_shift C != 0 or sheaf HH_(shift - 1) C != quotientBundle K then
        error "coevaluation does not give the hyperplane quotient";
    realizedDerived(E, shiftObject(hyperplaneQuotientReference K, shift - 1), C,
        "quartic-degree-zero-coevaluation", {"smooth quartic K3", "spherical hyperplane line bundle",
            "RHom(O,O(H)) concentrated in degree zero", "dual coordinate basis and quotient sequence"},
        hashTable {"direction" => -1, "chainMap" => u, "coevaluation" => f, "relativeShift" => -1,
            "source" => input, "derivedHomDegrees" => {{0,4}}})
    )

quarticQuotientEvaluation = (E, shift) -> (
    K := E#"surface";
    R := K#"ring";
    Q := quotientBundle K;
    if cohomologyDims(Q(-1)) =!= {4, 0, 0} then error "derived Hom from O(H) must be concentrated in degree zero";
    G := R^{4 : 1};
    f := map(module Q, G, id_G);
    inclusion := map(G, R^1, transpose vars R);
    if f * inclusion != 0 or kernel f != image inclusion then error "quotient evaluation is not exact";
    (u, C) := degreeZeroCone(f, shift);
    realizedDerived(E, shiftObject(structureObject K, shift + 1), C,
        "quartic-quotient-evaluation", {"smooth quartic K3", "spherical hyperplane line bundle",
            "dual coordinate sequence and K3 Serre duality", "RHom(O(H),Q) concentrated in degree zero"},
        hashTable {"direction" => 1, "chainMap" => u, "evaluation" => f,
            "kernelInclusion" => inclusion, "relativeShift" => 1, "derivedHomDegrees" => {{0,4}}})
    )

-- Three squared projection parameters give a short Koszul resolution when the
-- affine grid contains a point off the quartic. The four squares also cut out
-- only the vertex of the affine cone, including over the small prime fields.
quarticEvaluationIdeal = K -> (
    R := K#"ring";
    f := first K#"equations";
    coordinates := gens ring f;
    scalars := toList(0..min(4, char R - 1));
    grid := flatten flatten apply(scalars, a -> apply(scalars, b -> apply(scalars, c -> {1,a,b,c})));
    centers := select(1, grid, p -> sub(f, apply(coordinates, p, (x,t) -> x => t)) != 0);
    x := gens R;
    if #centers == 0 then return ideal apply(x, t -> t^2);
    p := first centers;
    ideal apply(1..3, i -> (x#i - p#i*x#0)^2)
    )

quarticHigherEvaluation = (E, input, shift) -> (
    K := E#"surface";
    R := K#"ring";
    kk := K#"field";
    O := structureObject K;
    ext := extObservation(O, input);
    dimensions := apply(3, i -> {i, observedDimension(ext, i)});
    if dimensions =!= {{0,0},{1,0},{2,4}} then error "expected Ext concentrated in degree two";

    -- For this quartic the graded canonical module is R. Graded local duality
    -- identifies Ext^2(J,R) with the graded dual of R/J for this vertex ideal J.
    -- The map to H^2(O_X(*)) is dual to R -> R/J, an isomorphism in degrees 0 and 1.
    J := module quarticEvaluationIdeal K;
    aug := resolutionMap(complex J, LengthLimit => 3);
    F := source aug;
    next := Hom(F.dd_3, R^1);
    classes := kernel next / image Hom(F.dd_2, R^1);
    frame := basis(-1, classes);
    trace := basis(0, classes);
    if numColumns frame != 4 or numColumns trace != 1 then error "unexpected graded Ext basis dimensions";

    -- Multiplication by x_i gives the cup product with its coordinate section.
    -- Use the chosen nonzero class of H^2(O) as the trace generator.
    serrePairing := columns -> matrix(kk, apply(gens R, x -> (
        row := (x * columns) // trace;
        if trace * row != x * columns then error "could not express the cup product in the trace basis";
        first entries sub(row, kk)
        )));
    pairing := serrePairing frame;
    if rank pairing != 4 then error "the coordinate sections do not give a perfect pairing";
    dualFrame := frame * map(source frame, source frame, sub(pairing^(-1), R));
    pairing = serrePairing dualFrame;
    if pairing != id_(kk^4) then error "the evaluation classes are not Serre dual to the coordinates";

    lifts := map(source next, source dualFrame, ambient dualFrame);
    evaluations := apply(4, i -> homomorphism(lifts_i));
    truncated := complex(canonicalTruncation(F, 0, 2), Base => -2);
    D := directSum toList(4 : truncated);
    L := R^{-1};
    f := map(L, D_0, fold((a,b) -> a | b, evaluations));
    if not isHomogeneous f or not isWellDefined f then
        error "degree-two evaluation must preserve the grading and descend to the finite model";
    u := map(complex L, D, hashTable {0 => f}, Degree => 0);
    C := cone u;

    oneAugmentation := map(complex(R^1, Base => -2), truncated,
        hashTable {-2 => inducedMap(R^1, J) * aug_0}, Degree => 0);
    if not isIsomorphism sheaf homology(-2, oneAugmentation)
        or not all({-1,0}, i -> HH_i truncated == 0) then
        error "the finite model does not resolve O in degree two";
    augmentation := directSum toList(4 : oneAugmentation);

    -- The cone triangle gives O(-H) in degree zero and O^4 in degree one.
    v := mukaiClass input;
    coneClass := mukaiClass(v#"rank" - 4, v#"divisor", v#"eulerComponent" - 4);
    representative := objectReference(K, "T_O(O(-H))", coneClass);
    realizedDerived(E, shiftObject(representative, shift), C[-shift],
        "quartic-degree-two-evaluation", {"smooth quartic K3", "certified O generator",
            "graded local duality at the irrelevant ideal", "Serre-dual coordinate evaluation"},
        hashTable {"direction" => 1, "shift" => shift, "chainMap" => u, "evaluation" => f,
            "derivedHomDegrees" => {{2,4}}, "extDimensions" => dimensions, "serrePairing" => pairing,
            "sourceAugmentation" => augmentation, "traceCocycle" => homomorphism map(source next, source trace, ambient trace)})
    )

-- Split the identity summand in the derived category. This comparison is independent of a lift
-- of the degree-two class. The surviving one-term complex represents the actual cone.
quarticSelfEvaluation = E -> (
    K := E#"surface";
    (input, startShift) := unshiftReference E#"start";
    D := lineCoordinates input;
    H := K#"polarization"#"coordinates";
    if D =!= H and D =!= apply(H, i -> 0) then return null;
    steps := {};
    cursor := E;
    while instance(cursor, SymbolicTwistImage) do (
        signedStep := cursor#"step";
        if not certifiedStep signedStep or lineCoordinates stepObject signedStep =!= D then return null;
        steps = prepend(signedStep#"direction", steps);
        cursor = cursor#"prefix";
        );
    shift := startShift - sum steps;
    X := K#"variety";
    if cohomologyDims (OO_X^1) =!= {1,0,1} then error "unexpected spherical self-Ext for a line bundle";
    R := K#"ring";
    M := if D === H then R^{1} else R^1;
    C := complex({M}, Base => shift);
    realizedDerived(E, shiftObject(input, shift), C,
        "quartic-spherical-self-split", {"smooth quartic K3", "spherical line bundle O or O(H)",
            "RHom(S,S) from RΓ(O)", "Serre trace in degree two", "identity summand split in the derived category"},
        hashTable {"directions" => steps, "shift" => shift, "derivedHomDegrees" => {{0,1},{2,1}},
            "comparison" => "triangular change of basis eliminates the degree-two off-diagonal component"})
    )

realizeQuarticDerived = E -> (
    self := quarticSelfEvaluation E;
    if self =!= null then return self;
    if E#"length" != 1 then return null;
    signedStep := E#"step";
    K := E#"surface";
    H := K#"polarization"#"coordinates";
    if not certifiedStep signedStep then return null;
    generator := lineCoordinates stepObject signedStep;
    (input, shift) := unshiftReference E#"start";
    D := lineCoordinates input;
    zero := apply(H, i -> 0);
    if signedStep#"direction" == 1 and generator === zero and D === apply(H, h -> -h) then
        return quarticHigherEvaluation(E, input, shift);
    if generator =!= H then return null;
    if signedStep#"direction" == -1 and D === zero then
        return quarticCoevaluation(E, input, shift);
    if signedStep#"direction" == 1 and input === hyperplaneQuotientReference K then
        return quarticQuotientEvaluation(E, shift);
    null
    )
