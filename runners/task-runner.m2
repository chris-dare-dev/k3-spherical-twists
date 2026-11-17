-- The entry point the batch scheduler calls.  One process expands a batch or computes one task.
--   M2 --script runners/task-runner.m2 expand '<batch description as JSON>'
--   M2 --script runners/task-runner.m2 run '<task as JSON>'
-- "expand" prints one line "@task <JSON>" per task and a last line "@meta <JSON>" with the number of
-- tasks and the versions in use.  "run" prints one line "@result <JSON>".  An error ends the process
-- with a non-zero status and the message on the standard error.
path = prepend(currentFileDirectory | "../", path);
needsPackage "K3Twists";
needsPackage "JSON";

-- The JSON package writes 0.5 as .5, which is not JSON, and reads null as the symbol nil.
toJSON RR := o -> x -> replace("^(-?)\\.", "\\10.", toString x);
fromNil = x -> (
    if x === nil then null
    else if instance(x, HashTable) then applyValues(x, fromNil)
    else if instance(x, List) then apply(x, fromNil)
    else x
    );

emit = (tag, h) -> stdio << tag << " " << toJSON h << endl << flush;

args = drop(scriptCommandLine, 1);
if #args != 2 or not member(args#0, {"expand", "run"}) then (
    stderr << "usage: M2 --script task-runner.m2 (expand|run) '<JSON>'" << endl;
    exit 2;
    );
request = fromNil fromJSON args#1;

if args#0 == "run" then emit("@result", runTask request);

if args#0 == "expand" then (
    tasks = expandBatch request;
    scan(tasks, t -> emit("@task", t));
    emit("@meta", new HashTable from {
            "tasks" => #tasks,
            "m2_version" => version#"VERSION",
            "package" => "K3Twists " | K3Twists.Options.Version
            });
    );
