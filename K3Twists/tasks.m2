-- Batches and tasks.  A batch description and a task are hash tables with string keys, the form in
-- which they are read from and written to JSON.  expandBatch turns a description into tasks; runTask
-- computes one task.  Neither reads or writes files: the runner script does that.

opt = (h, key, default) -> if h#?key and h#key =!= null then h#key else default

timed = f -> (r := elapsedTiming f(); (r#0, r#1))

-- Surfaces ---------------------------------------------------------------------------------------

surfaceSpec = s -> new HashTable from {
    "d" => s#"d",
    "seed" => opt(s, "seed", 1),
    "characteristic" => opt(s, "characteristic", 32003),
    "special_quadric" => opt(s, "special_quadric", false)
    }

surfaceLabel = s -> concatenate(
    "d", toString s#"d", if s#"special_quadric" then "q" else "",
    "-p", toString s#"characteristic", "-s", toString s#"seed")

surfaceFromSpec = s -> k3Surface(s#"d", Seed => s#"seed", Characteristic => s#"characteristic",
    SpecialQuadric => s#"special_quadric")

-- Kind "ext_pair": Ext^i(E, F) for two sheaves of the catalogue ------------------------------------

-- A hint for ordering tasks and choosing limits: the rank of the sheaf Hom(E, F), a sheaf of rank 0
-- counted as rank 1; 0 when nothing is computed.  c and e are rows of catalogueClasses.
extPairCost = (c, e) -> (
    if extMethod(c#2, c#1#0, e#2, e#1#0) == "not computed" then 0
    else max(c#1#0, 1) * max(e#1#0, 1)
    )

expandExtPairs = (i, set, surfaces) -> flatten apply(surfaces, s -> (
        classes := catalogueClasses surfaceFromSpec s;
        chosen := key -> (
            want := opt(set, key, opt(set, "sheaves", "all"));
            if want === "all" then classes
            else apply(want, name -> (
                    found := select(classes, c -> c#0 == name);
                    if #found == 0 then error("no sheaf named " | name | " on " | surfaceLabel s);
                    first found))
            );
        flatten apply(chosen "sources", c -> apply(chosen "targets", e -> new HashTable from {
                    "id" => concatenate("ext_pair/", surfaceLabel s, "/", c#0, "/", e#0),
                    "kind" => "ext_pair",
                    "comparison" => "fields",
                    "set" => i,
                    "group" => "ext_pair " | surfaceLabel s,
                    "cost" => extPairCost(c, e),
                    "predicted" => new HashTable from {"chi" => -mukaiPairing(s#"d", c#1, e#1)},
                    "surface" => s,
                    "source" => c#0,
                    "target" => e#0
                    }))
        ))

runExtPair = task -> (
    s := task#"surface";
    (setup, entries) := timed(() -> (
            K := surfaceFromSpec s;
            {catalogueEntry(K, task#"source"), catalogueEntry(K, task#"target")}));
    (compute, row) := timed(() -> extTableRow(s#"d", entries#0, entries#1));
    dims := row#2;
    chi := if dims === null then null else dims#0 - dims#1 + dims#2;
    new HashTable from {
        "value" => if dims === null then null else new HashTable from {"dims" => dims, "chi" => chi},
        "predicted" => new HashTable from {"chi" => row#3},
        "agrees" => if dims === null then null else chi == row#3,
        "method" => row#4,
        "setup_seconds" => setup,
        "compute_seconds" => compute
        }
    )

-- Kind "invariant": one entry of sheafInvariants ---------------------------------------------------

expandInvariants = (i, set, surfaces) -> flatten apply(surfaces, s -> (
        K := surfaceFromSpec s;
        fast := sheafInvariantNames K;
        every := sheafInvariantNames(K, Slow => true);
        predicted := hashTable apply(invariantSpecs(K, true), spec -> spec#0 => spec#2);
        want := opt(set, "names", "fast");
        names := if want === "fast" then fast
            else if want === "slow" then select(every, name -> not member(name, fast))
            else if want === "all" then every
            else (
                scan(want, name -> if not member(name, every) then error("no invariant named " | name));
                want);
        apply(names, name -> new HashTable from {
                "id" => concatenate("invariant/", surfaceLabel s, "/", name),
                "kind" => "invariant",
                "comparison" => "equals",
                "set" => i,
                "group" => "invariant " | surfaceLabel s,
                "cost" => if member(name, fast) then 1 else 50,
                "predicted" => predicted#name,
                "surface" => s,
                "name" => name
                })
        ))

runInvariant = task -> (
    (setup, K) := timed(() -> surfaceFromSpec task#"surface");
    (compute, row) := timed(() -> sheafInvariant(K, task#"name"));
    new HashTable from {
        "value" => row#1,
        "predicted" => row#2,
        "agrees" => row#1 === row#2,
        "method" => "direct",
        "setup_seconds" => setup,
        "compute_seconds" => compute
        }
    )

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

-- Dispatch ---------------------------------------------------------------------------------------

taskKinds = new HashTable from {
    "ext_pair" => (expandExtPairs, runExtPair),
    "invariant" => (expandInvariants, runInvariant),
    "synthetic" => (expandSynthetic, runSynthetic)
    }

kindOf = h -> (
    if not h#?"kind" or not taskKinds#?(h#"kind") then error(
        "expected \"kind\" to be one of " | demark(", ", sort keys taskKinds));
    h#"kind"
    )

-- The tasks of a batch description {"surfaces" => {...}, "tasks" => {...}}, in the order given.
expandBatch = method()
expandBatch HashTable := List => spec -> (
    surfaces := apply(opt(spec, "surfaces", {}), surfaceSpec);
    sets := opt(spec, "tasks", {});
    tasks := flatten apply(#sets, i -> (taskKinds#(kindOf sets#i))#0 (i, sets#i, surfaces));
    ids := apply(tasks, t -> t#"id");
    if #unique ids != #ids then error "two tasks of the batch have the same id";
    tasks
    )

-- The outcome of one task: "status" is "ok" when a value was computed and agrees with the predicted
-- one or has none to agree with, "mismatch" when it differs, "unsupported" when there is no method.
runTask = method()
runTask HashTable := HashTable => task -> (
    out := (taskKinds#(kindOf task))#1 task;
    status := if out#"value" === null then "unsupported"
        else if out#"agrees" === false then "mismatch"
        else "ok";
    merge(out, new HashTable from {"status" => status}, (a, b) -> b)
    )
