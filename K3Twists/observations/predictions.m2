-- Predictions preserve their name, version, hypotheses and exact comparison scope.

ObservationPrediction = new Type of HashTable
ObservationCheck = new Type of HashTable

observationPrediction = method(Options => {Full => false})
observationPrediction(String, String, List, Sequence) := ObservationPrediction => opts ->
    (name, revision, hypotheses, comparison) -> (
    if #comparison != 2 or not instance(comparison#0, String) then
        error "expected a pair of quantity and expected value";
    (quantity, expected) := comparison;
    if #name == 0 or #revision == 0 then error "prediction name and revision must be nonempty";
    if not all(hypotheses, h -> instance(h, String)) then error "prediction hypotheses must be strings";
    if not member(quantity, {"cohomology", "ext"}) then error "unknown prediction quantity";
    scope := if instance(expected, ZZ) then (
        if opts.Full then error "Full is only available for a degree table";
        "euler"
        ) else (
        if not instance(expected, HashTable) then error "expected an integer Euler value or a degree table";
        if not all(keys expected, i -> instance(i, ZZ) and instance(expected#i, ZZ) and expected#i >= 0)
            then error "a degree table maps integer degrees to nonnegative integers";
        if opts.Full then "full" else "selected"
        );
    new ObservationPrediction from {
        "name" => name, "version" => revision, "hypotheses" => hypotheses,
        "quantity" => quantity, "scope" => scope, "expected" => expected
        }
    )

observationEuler = obs -> sum apply(pairs obs#"dimensions", (i, d) -> if i % 2 == 0 then d else -d)

checkObservation = method()
checkObservation(DegreeObservation, ObservationPrediction) := ObservationCheck => (obs, prediction) -> (
    if obs#"quantity" =!= prediction#"quantity" then error "prediction and observation quantities differ";
    fields := hashTable {"observation" => obs, "prediction" => prediction, "scope" => prediction#"scope"};
    makeCheck := (status, expected, measured) -> new ObservationCheck from merge(fields, hashTable {
        "status" => status, "expected" => expected, "measured" => measured
        }, (a, b) -> b);
    expected := prediction#"expected";
    if obs#"status" === "unsupported" then return makeCheck("unsupported", expected, null);
    scope := prediction#"scope";
    if scope === "euler" then (
        if not obs#"complete" then return makeCheck("inconclusive", expected, null);
        actual := observationEuler obs;
        return makeCheck(if actual == expected then "match" else "mismatch", expected, actual)
        );
    degreesToCheck := if scope === "full" then sort unique ((keys expected) | (keys obs#"dimensions"))
        else sort keys expected;
    measured := hashTable apply(degreesToCheck, i -> i => observedDimension(obs, i));
    normalized := hashTable apply(degreesToCheck, i -> i => (if expected#?i then expected#i else 0));
    status := if any(degreesToCheck, i -> measured#i =!= null and measured#i != normalized#i) then "mismatch"
        else if (scope === "full" and not obs#"complete") or any(values measured, x -> x === null) then "inconclusive"
        else "match";
    makeCheck(status, normalized, measured)
    )

net DegreeObservation := obs -> net (
    if obs#"status" === "unsupported" then obs#"quantity" | " unsupported: " | obs#"reason"
    else concatenate(obs#"quantity", " in cohomological degrees ", toString obs#"dimensions",
        if obs#"complete" then " (complete)" else " (partial)"))
net ObservationPrediction := p -> net (p#"name" | " v" | p#"version" | " (" | p#"scope" | ")")
net ObservationCheck := c -> stack {
    net c#"prediction" | " " | net c#"status",
    "expected " | toString c#"expected",
    "measured " | toString c#"measured"
    }
