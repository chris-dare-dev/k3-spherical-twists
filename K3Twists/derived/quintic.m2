-- Quintic operations use the common reference, word, observation and complex interfaces.

QuinticObjectReference = new Type of VarietyObjectReference
ShiftedQuinticObject = new Type of QuinticObjectReference
SymbolicQuinticTwistImage = new Type of QuinticObjectReference
protect symbol quinticReference

pointSheaf QuinticThreefold := CoherentSheaf => Y ->
    cached(Y, "O_x", () -> sheaf ((Y#"ring")^1 / Y#"point"))

pointIdealSheaf QuinticThreefold := CoherentSheaf => Y ->
    cached(Y, "I_x", () -> sheaf module Y#"point")

quinticCoordinates = hashTable {"O" => {1,0}, "O_x" => {0,1}, "I_x" => {1,-1}}

catalogueObject(QuinticThreefold, String) := QuinticObjectReference => (Y, name) -> (
    if not quinticCoordinates#?name then error "unknown quintic object";
    cached(Y, (symbol quinticReference, name), () -> new QuinticObjectReference from {
            "surface" => Y, "definition" => hashTable {"kind" => "catalogue", "name" => name},
            "numericalClass" => quinticClass(Y, quinticCoordinates#name), "evidence" => {},
            symbol objectIdentity => new MutableHashTable
            })
    )

structureObject QuinticThreefold := QuinticObjectReference => Y -> catalogueObject(Y, "O")

numericalClass QuinticObjectReference := QuinticNumericalClass => E -> E#"numericalClass"
shiftObject(QuinticObjectReference, ZZ) := QuinticObjectReference => (E,n) -> shiftReference(ShiftedQuinticObject, E, n)
shiftObject(ShiftedQuinticObject, ZZ) := QuinticObjectReference => (E,n) -> shiftObject(E#"object", E#"shift" + n)
symbolicImageType QuinticObjectReference := E -> SymbolicQuinticTwistImage
applyWord(SphericalTwistWord, QuinticObjectReference) := QuinticObjectReference => opts -> (W,E) ->
    applyReferenceWord(W, E, opts.VerifiedOnly, true)

quinticReferenceTerm = E -> (
    if instance(E, ShiftedQuinticObject) then return (E#"object", E#"shift");
    (E,0)
    )

isQuinticNamed = (E, name) -> E#?"definition" and E#"definition"#"name" === name

quinticSheaf = E -> (
    if not E#?"definition" then return null;
    Y := E#"surface";
    X := Y#"variety";
    name := E#"definition"#"name";
    if name === "O" then OO_X^1
    else if name === "O_x" then pointSheaf Y
    else pointIdealSheaf Y
    )

sphericalObject QuinticObjectReference := SphericalTwistGenerator => E -> (
    (F, shift) := quinticReferenceTerm E;
    if not isQuinticNamed(F, "O") then error "the quintic strategy certifies only the structure sheaf and its shifts";
    Y := E#"surface";
    X := Y#"variety";
    dims := apply(4, i -> rank HH^i(OO_X^1));
    if dims =!= {1,0,0,1} then error "quintic structure sheaf does not have spherical self-Ext";
    new SphericalTwistGenerator from {
        "object" => E, "surface" => Y, "dimension" => serreShift Y,
        "evidence" => hashTable {"kind" => "theorem", "object" => E, "selfExt" => dims,
            "reason" => "structure sheaf cohomology and threefold Serre duality with trivial canonical bundle"}
        }
    )

cohomologyObservation QuinticObjectReference := DegreeObservation => opts -> E -> (
    (F, shift) := quinticReferenceTerm E;
    observeCohomology(E, quinticSheaf F, shift, opts.Degrees)
    )

extObservation(QuinticObjectReference, QuinticObjectReference) := DegreeObservation => opts -> (E,F) -> (
    requireObjectModel(E#"surface", F#"surface");
    requireDegrees opts.Degrees;
    (A, a) := quinticReferenceTerm E;
    (B, b) := quinticReferenceTerm F;
    offset := a-b;
    n := serreShift E#"surface";
    range := {offset, offset+n};
    if isQuinticNamed(A, "O") and B#?"definition" then
        return measureDegrees("ext", {E,F}, "quintic structure source via sheaf cohomology", range,
            opts.Degrees, i -> rank HH^(i-offset)(quinticSheaf B));
    if isQuinticNamed(A, "O_x") and isQuinticNamed(B, "O") then
        return measureDegrees("ext", {E,F}, "threefold Serre duality with trivial canonical bundle", range,
            opts.Degrees, i -> rank HH^(n+offset-i)(quinticSheaf A));
    unsupportedObservation("ext", {E,F}, "quintic Ext requires a structure source or the marked point to structure pair")
    )

realizeTwistImage QuinticObjectReference := TwistRealization => E -> (
    if not instance(E, SymbolicQuinticTwistImage) then return unavailableTwist(E, "expected a symbolic quintic twist image");
    signedStep := E#"step";
    if E#"length" != 1 or signedStep#"direction" != 1 or not certifiedStep signedStep then
        return unavailableTwist(E, "quintic realization requires a single certified forward twist");
    if not isQuinticNamed(stepObject signedStep, "O") or not isQuinticNamed(E#"start", "O_x") then
        return unavailableTwist(E, "quintic realization requires the structure generator and marked point target");
    Y := E#"surface";
    R := Y#"ring";
    P := pointSheaf Y;
    if apply(4, i -> rank HH^i(P)) =!= {1,0,0,0} then error "marked point evaluation must be concentrated in degree zero";
    f := map(module P, R^1, {{1_R}});
    (u, C) := degreeZeroCone(f, 0);
    if sheaf HH_0 C != 0 then error "quintic point evaluation must be surjective";
    realizedDerived(E, shiftObject(catalogueObject(Y, "I_x"), 1), C, "quintic-point-evaluation",
        {"smooth quintic with trivial canonical bundle", "certified spherical structure sheaf",
            "marked rational point", "RHom concentrated in degree zero"},
        hashTable {"direction" => 1, "evaluation" => f, "chainMap" => u, "derivedHomDegrees" => {{0,1}}})
    )

net QuinticObjectReference := E -> net ("quintic object " | E#"definition"#"name")
net ShiftedQuinticObject := E -> net E#"object" | "[" | net E#"shift" | "]"
net SymbolicQuinticTwistImage := E -> net ("symbolic quintic twist image (" | toString E#"length" | " steps)")
