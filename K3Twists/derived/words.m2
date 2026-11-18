-- Signed words act in list order. The numerical action is a Mukai reflection in both directions.

SphericalTwistStep = new Type of HashTable
SphericalTwistStep.synonym = "signed spherical twist step"
SphericalTwistWord = new Type of HashTable
SphericalTwistWord.synonym = "spherical twist word"
SymbolicTwistImage = new Type of K3ObjectReference
SymbolicTwistImage.synonym = "symbolic twist image"
protect symbol twistPrefix

twistStep = method()
twistStep(SphericalTwistGenerator, ZZ) := SphericalTwistStep => (S, direction) -> (
    if not member(direction, {-1, 1}) then error "a twist direction must be 1 or -1";
    new SphericalTwistStep from {"generator" => S, "direction" => direction}
    )

stepGenerator = signedStep -> signedStep#"generator"
stepEvidence = signedStep -> (stepGenerator signedStep)#"evidence"
stepObject = signedStep -> (stepGenerator signedStep)#"object"
stepSurface = signedStep -> (stepGenerator signedStep)#"surface"

twistWord = method()
twistWord List := SphericalTwistWord => steps -> (
    if not all(steps, signedStep -> instance(signedStep, SphericalTwistStep)) then error "expected signed twist steps";
    K := if #steps == 0 then null else stepSurface first steps;
    scan(steps, signedStep -> requireObjectModel(K, stepSurface signedStep));
    new SphericalTwistWord from {"surface" => K, "steps" => steps}
    )

composeTwistWords = method()
composeTwistWords(SphericalTwistWord, SphericalTwistWord) := SphericalTwistWord => (a, b) ->
    twistWord (a#"steps" | b#"steps")

inverseTwistWord = method()
inverseTwistWord SphericalTwistWord := SphericalTwistWord => W ->
    twistWord apply(reverse W#"steps", signedStep -> twistStep(stepGenerator signedStep, -signedStep#"direction"))

-- The generator is validated once. Reflection uses integer arithmetic in all marked coordinates.
reflectMukaiClass = (v, s) -> (
    coefficient := mukaiPairing(v, s);
    (r, c, e) := classCoordinates v;
    (rs, cs, es) := classCoordinates s;
    L := (v#"divisor")#"lattice";
    mukaiClass(r + coefficient * rs, divisorClass(L, apply(c, cs, (a,b) -> a + coefficient * b)),
        e + coefficient * es)
    )

mukaiReflection = method()
mukaiReflection(MukaiClass, MukaiClass) := MukaiClass => (v, s) -> (
    if mukaiPairing(s, s) != -2 then error "a K3 spherical class must have Mukai square -2";
    reflectMukaiClass(v, s)
    )

verifiedEvidence = evidence -> member(evidence#"kind", {"checked", "theorem"})

requireVerifiedEvidence = evidence -> (
    if not all(evidence, verifiedEvidence) then error "VerifiedOnly requires checked or theorem-backed sphericality"
    )

applyWordToClass = method(Options => {VerifiedOnly => false})
applyWordToClass(SphericalTwistWord, MukaiClass) := MukaiClass => opts -> (W, v) -> (
    if opts.VerifiedOnly then requireVerifiedEvidence apply(W#"steps", stepEvidence);
    current := v;
    scan(W#"steps", signedStep -> current = reflectMukaiClass(current, (stepObject signedStep)#"mukaiClass"));
    current
    )

certifiedStep = signedStep -> verifiedEvidence stepEvidence signedStep

inverseNeighbours = (a,b) -> (
    a#"direction" == -b#"direction" and certifiedStep a and certifiedStep b
        and (stepObject a)#(symbol objectIdentity) === (stepObject b)#(symbol objectIdentity)
    )

extendTwistImage = (E, signedStep) -> (
    if instance(E, SymbolicTwistImage) and inverseNeighbours(E#"step", signedStep) then return E#"prefix";
    K := E#"surface";
    S := stepObject signedStep;
    evidence := stepEvidence signedStep;
    key := (symbol twistPrefix, E#(symbol objectIdentity), S#(symbol objectIdentity),
        signedStep#"direction", evidence#"kind", evidence#"reason", evidence#"selfExt");
    cached(K, key, () -> (
            isPrefix := instance(E, SymbolicTwistImage);
            new SymbolicTwistImage from {
                "surface" => K,
                "start" => if isPrefix then E#"start" else E,
                "prefix" => E,
                "step" => signedStep,
                "length" => if isPrefix then E#"length" + 1 else 1,
                "mukaiClass" => reflectMukaiClass(E#"mukaiClass", S#"mukaiClass"),
                "evidence" => unique (E#"evidence" | {evidence}),
                symbol objectIdentity => new MutableHashTable
                }
            ))
    )

applyWord = method(Options => {VerifiedOnly => false})
applyWord(SphericalTwistWord, K3ObjectReference) := K3ObjectReference => opts -> (W, E) -> (
    if W#"surface" =!= null then requireObjectModel(W#"surface", E#"surface");
    if opts.VerifiedOnly then requireVerifiedEvidence (E#"evidence" | apply(W#"steps", stepEvidence));
    current := E;
    scan(W#"steps", signedStep -> current = extendTwistImage(current, signedStep));
    current
    )

net SphericalTwistStep := signedStep -> net (if signedStep#"direction" == 1 then "T" else "T^(-1)") | "_(" | net stepObject signedStep | ")"
net SphericalTwistWord := W -> net ("twist word (" | toString #(W#"steps") | " steps)")
net SymbolicTwistImage := E -> net ("symbolic twist image (" | toString E#"length" | " steps)")
