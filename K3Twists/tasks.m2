-- Batches and tasks.  A batch description and a task are hash tables with string keys, the form in
-- which they are read from and written to JSON.  expandBatch turns a description into tasks; runTask
-- computes one task.  Neither reads or writes files: the runner script does that.

opt = (h, key, default) -> if h#?key and h#key =!= null then h#key else default

timed = f -> (r := elapsedTiming f(); (r#0, r#1))

-- Surfaces ---------------------------------------------------------------------------------------

surfaceSpec = normalizeK3SurfaceSpec

surfaceLabel = s -> (
    original := concatenate(
        "d", toString s#"d", if s#"special_quadric" then "q" else "",
        "-p", toString s#"characteristic", "-s", toString s#"seed");
    if not s#?"family" then return original;
    label := s#"family" | "-" | original;
    if s#?"model" then (
        model := s#"model";
        label = label | "-m" | toString hash {model#"equation", model#"curve", model#"point"};
        );
    label
    )

surfaceFromSpec = s -> realizeK3Surface k3Recipe s

-- The built-in kinds use JSON field schemas. A schema is a list of (name, predicate) pairs.
isString = x -> instance(x, String) and #x > 0
isStringList = x -> instance(x, List) and all(x, isString)
isBoolean = x -> instance(x, Boolean)
isNonnegativeNumber = x -> (instance(x, ZZ) or instance(x, RR)) and x >= 0
isNonnegativeInteger = x -> instance(x, ZZ) and x >= 0
isAnything = x -> true
nullable = test -> x -> x === null or test x

checkFields = (h, label, required, optional) -> (
    if not instance(h, HashTable) then error(label | " must be an object");
    scan(required, (key, test) -> (
        if not h#?key then error(label | " is missing " | key);
        if not test h#key then error(label | " has invalid " | key)));
    scan(optional, (key, test) -> (
        if h#?key and not test h#key then error(label | " has invalid " | key)));
    allowed := apply(required | optional, first);
    scan(keys h, key -> if not member(key, allowed) then error(label | " has unknown field " | toString key));
    )

checkSurfaceSpec = s -> (
    if not instance(s, HashTable) then error "surface must be an object";
    surfaceSpec s
    )

taskKindField = {("kind", isString)}
taskCommonFields = {
    ("id", isString), ("group", isString), ("set", isNonnegativeInteger),
    ("cost", isNonnegativeNumber), ("kind_version", isNonnegativeInteger),
    ("requirements", isStringList), ("comparison", s -> member(s, {"equals", "fields"})),
    ("predicted", isAnything)
    }
checkTaskFields = (task, required, optional) ->
    checkFields(task, task#"kind" | " task", taskKindField | required, taskCommonFields | optional)

taskKinds = new MutableHashTable

registerTaskKind = method()
registerTaskKind(String, HashTable) := (name, spec) -> (
    if #name == 0 then error "task kind name must be nonempty";
    if taskKinds#?name then error("task kind already registered: " | name);
    checkFields(spec, name | " kind", {
            ("version", x -> isNonnegativeInteger x and x > 0),
            ("requirements", isStringList),
            ("validate_set", x -> instance(x, Function)),
            ("validate_task", x -> instance(x, Function)),
            ("validate_result", x -> instance(x, Function)),
            ("expand", x -> instance(x, Function)),
            ("run", x -> instance(x, Function))
            }, {});
    taskKinds#name = spec;
    )

taskKindOf = h -> (
    if not instance(h, HashTable) or not h#?"kind" or not isString h#"kind" or not taskKinds#?(h#"kind") then
        error("expected kind to be one of " | demark(", ", sort keys taskKinds));
    taskKinds#(h#"kind")
    )

-- The tasks of a batch description {"surfaces" => {...}, "tasks" => {...}}, in the order given.
expandBatch = method()
expandBatch HashTable := List => spec -> (
    checkFields(spec, "batch", {}, {
            ("surfaces", nullable(x -> instance(x, List))), ("tasks", nullable(x -> instance(x, List)))
            });
    surfaces := apply(opt(spec, "surfaces", {}), checkSurfaceSpec);
    sets := opt(spec, "tasks", {});
    tasks := flatten apply(#sets, i -> (
            kind := taskKindOf sets#i;
            (kind#"validate_set")(sets#i);
            apply((kind#"expand")(i, sets#i, surfaces), task -> (
                    (kind#"validate_task") task;
                    merge(task, hashTable {
                            "kind_version" => kind#"version", "requirements" => kind#"requirements"
                            }, (a, b) -> b)
                    ))
            ));
    ids := apply(tasks, t -> t#"id");
    if #unique ids != #ids then error "two tasks of the batch have the same id";
    tasks
    )

-- A result includes the observation, optional prediction, decision and diagnostic timing.
runTask = method()
runTask HashTable := HashTable => task -> (
    kind := taskKindOf task;
    (kind#"validate_task") task;
    if task#?"kind_version" and task#"kind_version" =!= kind#"version" then error "unsupported task kind version";
    if task#?"requirements" and task#"requirements" =!= kind#"requirements" then error "task requirements changed";
    out := (kind#"run") task;
    checkFields(out, "task result", {
            ("value", isAnything), ("predicted", isAnything), ("agrees", nullable isBoolean),
            ("method", isString), ("setup_seconds", isNonnegativeNumber), ("compute_seconds", isNonnegativeNumber)
            }, {("outputs", x -> instance(x, List))});
    scan(opt(out, "outputs", {}), reference -> checkFields(reference, "output reference", {
                ("name", isString), ("media_type", isString), ("digest", isString)
                }, {}));
    if out#"value" === null and out#"agrees" =!= null then error "unsupported result must have null agrees";
    (kind#"validate_result") out;
    status := if out#"value" === null then "unsupported"
        else if out#"agrees" === false then "mismatch"
        else "ok";
    merge(out, hashTable {"status" => status}, (a, b) -> b)
    )
