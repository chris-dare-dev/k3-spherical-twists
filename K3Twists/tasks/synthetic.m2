-- Kind "synthetic": no mathematics; holds memory, sleeps or fails, to exercise the limits of a run ---

expandSynthetic = (i, set, surfaces) -> apply(set#"items", item -> new HashTable from {
        "id" => "synthetic/" | item#"name",
        "kind" => "synthetic",
        "comparison" => "equals",
        "set" => i,
        "group" => "synthetic",
        "cost" => opt(item, "cost", 0),
        "sleep_seconds" => opt(item, "sleep_seconds", 0),
        "allocate_mb" => opt(item, "allocate_mb", 0),
        "fail" => opt(item, "fail", false),
        "value" => opt(item, "value", null),
        "predicted" => opt(item, "predicted", null)
        })

runSynthetic = task -> (
    if task#"fail" then error "synthetic task asked to fail";
    (compute, held) := timed(() -> (
            -- a mutable list of 131072 pointers takes one megabyte
            blocks := apply(task#"allocate_mb", j -> new MutableList from (131072 : j));
            if task#"sleep_seconds" > 0 then sleep task#"sleep_seconds";
            #blocks));
    value := if task#"value" === null then held else task#"value";
    new HashTable from {
        "value" => value,
        "predicted" => task#"predicted",
        "agrees" => if task#"predicted" === null then null else value === task#"predicted",
        "method" => "synthetic",
        "setup_seconds" => 0.,
        "compute_seconds" => compute
        }
    )

syntheticParameters = {
    ("sleep_seconds", isNonnegativeNumber), ("allocate_mb", isNonnegativeInteger),
    ("fail", isBoolean), ("value", isAnything), ("predicted", isAnything)
    }

registerTaskKind("synthetic", hashTable {
    "version" => 1,
    "requirements" => {},
    "validate_set" => (s -> (
            checkFields(s, "synthetic set", taskKindField | {("items", x -> instance(x, List))}, {});
            scan(s#"items", item -> checkFields(
                    item, "synthetic item", {("name", isString)},
                    {("cost", nullable isNonnegativeNumber)}
                    | apply(syntheticParameters, (name, test) -> (name, nullable test))
                    )))),
    "validate_task" => (t -> checkTaskFields(t, take(syntheticParameters, 4), {})),
    "validate_result" => (r -> null),
    "expand" => expandSynthetic,
    "run" => runSynthetic
    });
