-- This study checkpoints one evaluation cone and measures its sheaf homology twice.

quarticPrefixActions = {"model", "realize", "cohomology", "ext"}
quarticPrefixPrediction = H -> (
    checkFields(H, "quartic prediction", {
        ("name", isString), ("version", isString), ("hypotheses", isStringList), ("dimensions", x -> instance(x, List))
        }, {});
    if not all(H#"dimensions", row -> instance(row, List) and #row == 2 and instance(row#0, ZZ)
            and isNonnegativeInteger row#1)
        or #unique apply(H#"dimensions", first) != #H#"dimensions" then
        error "prediction dimensions must be unique integer degree and dimension pairs"
    )

quarticPrefixDefinition = t -> (
    action := t#"action";
    if not member(action, quarticPrefixActions) then error "unknown quartic prefix action";
    if member(action, {"cohomology", "ext"}) then (
        if not t#?"prediction" then error "quartic observation requires a prediction";
        quarticPrefixPrediction t#"prediction"
        )
    else if t#?"prediction" then error "only quartic observations take predictions"
    )

nonzeroDegreePairs = rows -> select(sort rows, row -> row#1 != 0)

expandQuarticPrefix = (i, spec, surfaces) -> (
    if #surfaces != 1 or not markedQuarticDegrees#?(opt(first surfaces, "family", "")) then
        error "quartic prefix study requires one marked quartic";
    fields := hashTable {
        "id" => "quartic_prefix/" | spec#"action", "kind" => "quartic_prefix", "set" => i,
        "group" => "marked quartic prefix", "cost" => 1, "surface" => first surfaces, "action" => spec#"action"
        };
    if not spec#?"prediction" then return {fields};
    p := spec#"prediction";
    {merge(fields, hashTable {"prediction" => p, "comparison" => "fields",
        "predicted" => hashTable {"nonzero_dimensions" => nonzeroDegreePairs p#"dimensions"}}, (a,b) -> b)}
    )

prefixResult = (valueData, prediction, agrees, strategy, evidence, outputs, seconds) -> hashTable {
    "value" => valueData, "predicted" => prediction, "agrees" => agrees,
    "method" => strategy, "evidence" => evidence, "artifacts" => outputs,
    "setup_seconds" => 0, "compute_seconds" => seconds
    }

prefixMukai = v -> {v#"rank", v#"divisor"#"coordinates", v#"eulerComponent"}

runQuarticPrefix = t -> (
    action := t#"action";
    if action === "model" then (
        (modelSeconds, model) := timed(() -> k3ModelArtifact surfaceFromSpec t#"surface");
        return prefixResult(hashTable {"family" => model#"payload"#"parameters"#"family"}, null, null,
            "validated marked quartic", hashTable {}, hashTable {"model" => model}, modelSeconds)
        );
    if not t#?"inputs" or not t#"inputs"#?"surface" then error "quartic prefix requires the surface input";
    modelInput := t#"inputs"#"surface";
    (seconds, answer) := timed(() -> (
        K := loadK3ModelArtifact(modelInput#"data", modelInput#"digest");
        if action === "realize" then (
            E := lineBundleObject(K, K#"polarization");
            W := twistWord {twistStep(sphericalObject structureObject K, 1)};
            R := realizeTwistImage applyWord(W, E);
            if R#"status" =!= "realized" then return (null, null, null,
                "quartic-degree-zero-evaluation", hashTable {"reason" => R#"reason"}, hashTable {});
            coneData := gradedComplexArtifact(K, R#"complex", modelInput#"digest");
            coneEvidence := hashTable {"direction" => R#"direction", "hypotheses" => R#"hypotheses",
                "homological_to_cohomological" => R#"homologicalToCohomological", "shift" => 1};
            return (hashTable {"class" => prefixMukai mukaiClass R, "shift" => 1}, null, null,
                R#"strategy", coneEvidence, hashTable {"cone" => coneData})
            );
        if not t#"inputs"#?"prefix" then error "quartic observation requires its prefix input";
        C := loadGradedComplex(K, t#"inputs"#"prefix"#"data");
        if concentration C =!= (0,1) or sheaf HH_0 C != 0 then error "expected a quartic evaluation cone";
        F := sheaf HH_1 C;
        X := K#"variety";
        O := if action === "cohomology" then cohomologyObservation(F, 1)
            else extObservation(F, OO_X^1, 1, 0);
        p := t#"prediction";
        expected := hashTable apply(p#"dimensions", row -> row#0 => row#1);
        P := observationPrediction(p#"name", p#"version", p#"hypotheses", (action, expected), Full => true);
        decision := checkObservation(O, P);
        if not member(decision#"status", {"match", "mismatch"}) then error "quartic observation is incomplete";
        values := apply(sort keys O#"dimensions", i -> {i, observedDimension(O, i)});
        evidence := hashTable {"convention" => O#"convention", "support" => O#"support",
            "complete" => O#"complete", "shift" => 1};
        (hashTable {"dimensions" => values, "nonzero_dimensions" => nonzeroDegreePairs values}, t#"predicted", decision#"status" === "match",
            O#"method", evidence, hashTable {})
        ));
    prefixResult(answer#0, answer#1, answer#2, answer#3, answer#4, answer#5, seconds)
    )

registerTaskKind("quartic_prefix", hashTable {
    "version" => 1, "requirements" => {"smooth-marked-quartic", "dependency-graph-v1"},
    "validate_set" => (s -> (
        checkFields(s, "quartic prefix", taskKindField | {("action", isString)},
            {("prediction", x -> instance(x, HashTable))});
        quarticPrefixDefinition s
        )),
    "validate_task" => (t -> (
        checkTaskFields(t, {("action", isString), ("surface", x -> instance(x, HashTable))},
            {("prediction", x -> instance(x, HashTable))});
        quarticPrefixDefinition t
        )),
    "validate_result" => (r -> if r#"value" =!= null and not instance(r#"value", HashTable) then
        error "invalid quartic prefix result"),
    "expand" => expandQuarticPrefix, "run" => runQuarticPrefix
    });
