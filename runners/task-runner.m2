-- File protocol v2: M2 --script task-runner.m2 protocol-v2 request.json response.json.
-- Legacy protocol v1: M2 --script task-runner.m2 (expand|run) '<JSON>'.
path = prepend(currentFileDirectory | "../", path);
needsPackage "K3Twists";
needsPackage "JSON";

-- Encode recursively because real numbers nested in JSON objects need a leading zero too.
wireJSON = x -> (
    if instance(x, RR) then (
        number := replace("^(-?)\\.", "\\10.", format(0, x));
        if match("^-?[0-9]+$", number) then number | ".0" else number
        )
    else if instance(x, HashTable) then (
        "{" | demark(",", apply(keys x, k -> toJSON k | ":" | wireJSON x#k)) | "}"
        )
    else if instance(x, List) then "[" | demark(",", apply(x, wireJSON)) | "]"
    else toJSON x
    );

fromNil = x -> (
    if x === nil then null
    else if instance(x, HashTable) then applyValues(x, fromNil)
    else if instance(x, List) then apply(x, fromNil)
    else x
    );

requestObject = document -> (
    -- JSON's parser accepts a valid prefix. Check that the file contains exactly one object.
    depth := 0;
    started := false;
    quoted := false;
    escaped := false;
    scan(characters document, ch -> (
        if quoted then (
            if escaped then escaped = false
            else if ch === "\\" then escaped = true
            else if ch === "\"" then quoted = false
            )
        else if depth == 0 then (
            if not member(ch, {" ", "\t", "\r", "\n"}) then (
                if started or ch =!= "{" then error "expected exactly one request object";
                started = true;
                depth = 1;
                )
            )
        else if ch === "\"" then quoted = true
        else if member(ch, {"{", "["}) then depth = depth + 1
        else if member(ch, {"}", "]"}) then depth = depth - 1
        ));
    if not started or depth != 0 then error "incomplete request object";
    request := fromNil fromJSON document;
    if not instance(request, HashTable) then error "expected one request object";
    request
    );

emit = (tag, h) -> stdio << tag << " " << wireJSON h << endl << flush;
versions = hashTable {
    "m2_version" => version#"VERSION",
    "package" => "K3Twists " | K3Twists.Options.Version
    };

wireTask = t -> (
    if not instance(t, HashTable) then error "run payload must be a task object";
    scan({"id", "kind", "group"}, k -> if not t#?k or not instance(t#k, String) or #t#k == 0 then
            error("task requires a string field " | k));
    scan({"set", "kind_version"}, k -> if not t#?k or not instance(t#k, ZZ) or t#k < 0 then
            error("task requires a nonnegative integer field " | k));
    if t#"kind_version" == 0 then error "task kind_version must be positive";
    if not t#?"cost" or not (instance(t#"cost", ZZ) or instance(t#"cost", RR)) or t#"cost" < 0 then
        error "task requires a nonnegative cost";
    if not t#?"requirements" or not instance(t#"requirements", List)
        or not all(t#"requirements", v -> instance(v, String)) then error "task requires a list of requirements";
    t
    );

fileProtocol = (source, destination) -> (
    header := hashTable {
        "version" => 2, "operation_version" => 1,
        "operation" => null, "request_id" => null
        };
    respond := (kind, payload, outputs) -> destination << wireJSON merge(header, hashTable {
            "type" => kind, "payload" => payload, "outputs" => outputs
            }, (a,b) -> b) << endl << close;
    failed := (code, message) -> respond("failure", hashTable {"code" => code, "message" => message}, {});
    -- On this M2 version the uncaught exception carries its message on the diagnostic channel.
    -- Leave a structured failure for an exception, and replace it on successful completion.
    failed("invalid_request", "the request could not be decoded");
    request := requestObject get source;
    for key in {"operation", "request_id"} do if request#?key then
        header = merge(header, hashTable {key => request#key}, (a,b) -> b);
    failed("invalid_request", "the request envelope is invalid");
    if not request#?"version" or request#"version" =!= 2 then error "unsupported protocol version";
    if not request#?"operation_version" or request#"operation_version" =!= 1 then
        error "unsupported operation version";
    if not instance(header#"request_id", String) or #header#"request_id" == 0 then error "missing request ID";
    operation := header#"operation";
    if not member(operation, {"expand", "run"}) then error "unknown operation";
    if not request#?"payload" or not instance(request#"payload", HashTable) then
        error "request requires an object payload";
    if sort keys request =!= {"operation", "operation_version", "payload", "request_id", "version"} then
        error "unknown request field";
    failed("operation_failed", "the runner could not complete the operation");
    payload := request#"payload";
    if operation === "expand" then (
        tasks := apply(expandBatch payload, wireTask);
        respond("expansion", hashTable {"tasks" => tasks, "count" => #tasks, "versions" => versions}, {})
        )
    else (
        result := runTask wireTask payload;
        outputs := if result#?"outputs" then result#"outputs" else {};
        fields := hashTable apply(select(keys result, k -> k =!= "outputs"), k -> k => result#k);
        respond("result", fields, outputs)
        )
    );

args = drop(scriptCommandLine, 1);
if #args == 3 and args#0 === "protocol-v2" then fileProtocol(args#1, args#2) else (
    if #args != 2 or not member(args#0, {"expand", "run"}) then (
        stderr << "usage: M2 --script task-runner.m2 protocol-v2 REQUEST RESPONSE | (expand|run) '<JSON>'" << endl;
        exit 2
        );
    request = fromNil fromJSON args#1;
    if args#0 == "run" then emit("@result", runTask request)
    else (
        tasks = expandBatch request;
        scan(tasks, t -> emit("@task", t));
        emit("@meta", merge(versions, hashTable {"tasks" => #tasks}, (a,b) -> b))
        )
    );
