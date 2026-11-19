-- Checkpoint a quartic evaluation cone and observe the reloaded complex.

quarticPrefixObservations = {"cohomology", "ext", "hypercohomology"}
quarticPrefixActions = {"model", "realize", "inverse"} | quarticPrefixObservations
quarticPrefixTargets = {"O(1H)", "O_x", "O(-1H)"}
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
    if t#?"target" and (action =!= "realize" or not member(t#"target", quarticPrefixTargets)) then
        error "quartic realization target must be O(1H), O_x or O(-1H)";
    if opt(t, "checkpoint_maps", false) and (action =!= "realize" or opt(t, "target", "") =!= "O(-1H)") then
        error "map checkpoints require the O(-1H) realization";
    if member(action, quarticPrefixObservations) then (
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
    if spec#"action" === "realize" then fields = merge(fields,
        hashTable {"target" => opt(spec, "target", "O(1H)")}, (a,b) -> b);
    if opt(spec, "checkpoint_maps", false) then fields = merge(fields,
        hashTable {"checkpoint_maps" => true}, (a,b) -> b);
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

quarticForwardOutputs = (K, realization, model) -> (
    u := realization#"chainMap";
    a := realization#"sourceAugmentation";
    hashTable {
        "evaluation_source" => gradedComplexArtifact(K, source u, model),
        "evaluation_target" => gradedComplexArtifact(K, target u, model),
        "augmentation_target" => gradedComplexArtifact(K, target a, model),
        "evaluation" => stagedGradedChainMap(K, u, model, "evaluation_source", "evaluation_target"),
        "augmentation" => stagedGradedChainMap(K, a, model, "evaluation_source", "augmentation_target")
        }
    )

quarticInverseFromCheckpoint = (K, inputs, prefixData, model) -> (
    required := {"evaluation_source", "evaluation_target", "augmentation_target", "evaluation", "augmentation"};
    if not all(required, name -> inputs#?name) then error "inverse cancellation requires the saved forward maps";
    loadEndpoint := name -> (
        endpoint := inputs#name;
        (loadGradedComplex(K, endpoint#"data"), endpoint#"digest")
        );
    D := loadEndpoint "evaluation_source";
    L := loadEndpoint "evaluation_target";
    O := loadEndpoint "augmentation_target";
    u := loadGradedChainMap(K, inputs#"evaluation"#"data", D, L);
    a := loadGradedChainMap(K, inputs#"augmentation"#"data", D, O);
    -- Rebuild the cone's canonical maps from the saved evaluation and check the exact
    -- graded presentation observed by the other consumer of this checkpoint.
    C := cone u;
    if gradedComplexArtifact(K, C, model) =!= prefixData then
        error "saved evaluation does not reconstruct the saved forward cone";
    (B, coevaluation, comparison, pairingRank) := quarticInverseComparison(K, C, u, a, 0);
    valueData := hashTable {"class" => prefixMukai mukaiClass catalogueObject(K, "O(-1H)"),
        "sheaf_quasi_isomorphism" => true, "serre_pairing_rank" => pairingRank};
    (valueData, hashTable {"sheaf_quasi_isomorphism" => true}, true,
        "quartic-degree-two-inverse-cancellation",
        hashTable {"comparison" => "sheaf quasi-isomorphism with O(-H)", "directions" => {1,-1}},
        hashTable {})
    )

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
            targetName := opt(t, "target", "O(1H)");
            E := catalogueObject(K, targetName);
            W := twistWord {twistStep(sphericalObject structureObject K, 1)};
            R := realizeTwistImage applyWord(W, E);
            if R#"status" =!= "realized" then return (null, null, null,
                "quartic evaluation", hashTable {"reason" => R#"reason"}, hashTable {});
            coneData := gradedComplexArtifact(K, R#"complex", modelInput#"digest");
            shift := opt(R, "shift", 1);
            coneEvidence := hashTable {"direction" => R#"direction", "hypotheses" => R#"hypotheses",
                "homological_to_cohomological" => R#"homologicalToCohomological", "shift" => shift};
            outputs := hashTable {"cone" => coneData};
            if opt(t, "checkpoint_maps", false) then outputs = merge(outputs,
                quarticForwardOutputs(K, R, modelInput#"digest"), (a,b) -> b);
            return (hashTable {"class" => prefixMukai mukaiClass R, "shift" => shift}, null, null,
                R#"strategy", coneEvidence, outputs)
            );
        if not t#"inputs"#?"prefix" then error "quartic observation requires its prefix input";
        prefixData := t#"inputs"#"prefix"#"data";
        if action === "inverse" then return quarticInverseFromCheckpoint(K, t#"inputs", prefixData, modelInput#"digest");
        C := loadGradedComplex(K, prefixData);
        O := if action === "hypercohomology" then hypercohomologyObservation(K, C) else (
            if concentration C =!= (0,1) or sheaf HH_0 C != 0 then error "expected a quartic evaluation cone";
            F := sheaf HH_1 C;
            X := K#"variety";
            if action === "cohomology" then cohomologyObservation(F, 1)
            else extObservation(F, OO_X^1, 1, 0)
            );
        p := t#"prediction";
        expected := hashTable apply(p#"dimensions", row -> row#0 => row#1);
        P := observationPrediction(p#"name", p#"version", p#"hypotheses", (action, expected), Full => true);
        decision := checkObservation(O, P);
        if not member(decision#"status", {"match", "mismatch"}) then error "quartic observation is incomplete";
        values := apply(sort keys O#"dimensions", i -> {i, observedDimension(O, i)});
        evidence := hashTable ({"convention" => O#"convention", "support" => O#"support",
            "complete" => O#"complete"} | if action === "hypercohomology" then {} else {"shift" => 1});
        (hashTable {"dimensions" => values, "nonzero_dimensions" => nonzeroDegreePairs values}, t#"predicted", decision#"status" === "match",
            O#"method", evidence, hashTable {})
        ));
    prefixResult(answer#0, answer#1, answer#2, answer#3, answer#4, answer#5, seconds)
    )

registerTaskKind("quartic_prefix", hashTable {
    "version" => 1, "requirements" => {"smooth-marked-quartic", "dependency-graph-v1"},
    "validate_set" => (s -> (
        checkFields(s, "quartic prefix", taskKindField | {("action", isString)},
            {("prediction", x -> instance(x, HashTable)), ("target", isString), ("checkpoint_maps", isBoolean)});
        quarticPrefixDefinition s
        )),
    "validate_task" => (t -> (
        checkTaskFields(t, {("action", isString), ("surface", x -> instance(x, HashTable))},
            {("prediction", x -> instance(x, HashTable)), ("target", isString), ("checkpoint_maps", isBoolean)});
        quarticPrefixDefinition t
        )),
    "validate_result" => (r -> if r#"value" =!= null and not instance(r#"value", HashTable) then
        error "invalid quartic prefix result"),
    "expand" => expandQuarticPrefix, "run" => runQuarticPrefix
    });
