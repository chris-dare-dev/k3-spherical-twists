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
    if not certifiedStep signedStep or lineCoordinates stepObject signedStep =!= H then return null;
    (input, shift) := unshiftReference E#"start";
    if signedStep#"direction" == -1 and lineCoordinates input === apply(H, i -> 0) then
        return quarticCoevaluation(E, input, shift);
    if signedStep#"direction" == 1 and input === hyperplaneQuotientReference K then
        return quarticQuotientEvaluation(E, shift);
    null
    )
