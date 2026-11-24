-- Forward twists about O on a smooth quartic with evaluation concentrated in degree zero.

TwistRealization = new Type of HashTable

unavailableTwist = (E, reason) -> new TwistRealization from {
    "status" => "unsupported", "symbolic" => E, "reason" => reason
    }

isSphericalStructure = signedStep -> (
    if not verifiedEvidence stepEvidence signedStep then return false;
    S := stepObject signedStep;
    if not S#?"definition" then return false;
    desc := S#"definition";
    (desc#"kind" === "line_bundle" and all(desc#"coordinates", i -> i == 0))
        or (desc#"kind" === "catalogue" and desc#"name" === "O")
    )

quarticEvaluationTarget = (E, K) -> (
    if not E#?"definition" then return null;
    desc := E#"definition";
    if desc#"kind" === "catalogue" then (
        if desc#"name" === "O_x" then return "point";
        if desc#"name" === "O(1H)" then return "hyperplane"
        );
    if desc#"kind" === "line_bundle" and desc#"coordinates" === K#"polarization"#"coordinates"
        then return "hyperplane";
    null
    )

realizeTwistImage = method()
realizeTwistImage(SphericalTwistWord, K3ObjectReference) := TwistRealization => (W, E) ->
    realizeTwistImage applyReferenceWord(W, E, false, false)

realizeTwistImage K3ObjectReference := TwistRealization => E -> (
    if not instance(E, SymbolicTwistImage) then return unavailableTwist(E, "expected a symbolic twist image");
    K := E#"surface";
    X := K#"variety";
    if not X.cache#?(symbol k3Model) or degree X != 4 then
        return unavailableTwist(E, "requires a certified smooth quartic K3");
    measured := elapsedTiming ({realizeQuarticDerived E});
    derived := first measured#1;
    if derived =!= null then return new TwistRealization from merge(derived,
        hashTable {"realizationSeconds" => measured#0}, (a,b) -> b);
    if E#"length" != 1 then return unavailableTwist(E, "a longer word requires derived evaluation");
    signedStep := E#"step";
    if signedStep#"direction" != 1 then return unavailableTwist(E, "inverse twists require coevaluation");
    if not isSphericalStructure signedStep then return unavailableTwist(E, "requires a certified structure sheaf generator");
    targetName := quarticEvaluationTarget(E#"start", K);
    if targetName === null then return unavailableTwist(E, "requires O_x or the hyperplane line bundle");
    R := K#"ring";
    isPoint := targetName === "point";
    F := if isPoint then pointSheaf K else (OO_X^1)(1);
    expected := if isPoint then 1 else 4;
    if cohomologyDims F =!= {expected, 0, 0} then
        return unavailableTwist(E, "derived Hom must be concentrated in degree zero");
    -- Constants evaluate at the marked point. The coordinates form a basis of H^0(O(H)).
    evaluation := if isPoint then map(module F, R^1, {{1_R}})
        else map(R^{1}, R^4, vars R);
    (chainMap, C) := degreeZeroCone(evaluation, 0);
    if sheaf HH_0 C != 0 then error "the evaluation must be surjective after sheafification";
    representative := shiftObject(catalogueObject(K, if isPoint then "I_x" else "M_H"), 1);
    realizedDerived(E, representative, C, "quartic-degree-zero-evaluation",
        {"smooth quartic K3", "certified O generator", "RHom concentrated in degree zero",
            "surjective evaluation of sheaves"},
        hashTable {"evaluation" => evaluation, "chainMap" => chainMap, "direction" => 1})
    )

realizedHomology = method()
realizedHomology(TwistRealization, ZZ) := CoherentSheaf => (R, i) -> (
    if R#"status" =!= "realized" then error R#"reason";
    sheaf HH_(-i) (R#"complex")
    )

numericalClass TwistRealization := VarietyNumericalClass => R -> numericalClass R#"symbolic"
mukaiClass TwistRealization := MukaiClass => R -> mukaiClass R#"symbolic"
net TwistRealization := R -> net (
    if R#"status" === "realized" then "realized twist (" | R#"strategy" | ")"
    else "twist realization unsupported: " | R#"reason")
