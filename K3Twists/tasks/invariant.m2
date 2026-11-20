-- Kind "invariant": one entry of sheafInvariants ---------------------------------------------------

expandInvariants = (i, set, surfaces) -> flatten apply(surfaces, s -> (
        label := surfaceLabel s;
        n := s#"d" + 2;
        marked := s#?"family";
        fast := apply(invariantSpecsFor(n, false, marked, null), first);
        specs := invariantSpecsFor(n, true, marked, null);
        every := apply(specs, first);
        predicted := hashTable apply(specs, spec -> spec#0 => spec#2);
        want := opt(set, "names", "fast");
        names := if want === "fast" then fast
            else if want === "slow" then select(every, name -> not member(name, fast))
            else if want === "all" then every
            else (
                scan(want, name -> if not member(name, every) then error("no invariant named " | name));
                want);
        control := opt(set, "control", hashTable {});
        scan(keys control, name -> if not member(name, names) then error("control names an unselected invariant: " | name));
        apply(names, name -> new HashTable from {
                "id" => concatenate("invariant/", label, "/", name, if control#?name then "!control" else ""),
                "kind" => "invariant",
                "comparison" => "equals",
                "set" => i,
                "group" => "invariant " | label,
                "cost" => if member(name, fast) then 1 else 50,
                "predicted" => opt(control, name, predicted#name),
                "surface" => s,
                "name" => name
                })
        ))

runInvariant = task -> (
    (setup, K) := timed(() -> surfaceFromSpec checkSurfaceSpec task#"surface");
    (compute, row) := timed(() -> sheafInvariant(K, task#"name"));
    predicted := opt(task, "predicted", row#2);
    new HashTable from {
        "value" => row#1,
        "predicted" => predicted,
        "agrees" => row#1 === predicted,
        "method" => "direct",
        "setup_seconds" => setup,
        "compute_seconds" => compute
        }
    )

invariantSelector = x -> member(x, {"fast", "slow", "all"}) or isStringList x
invariantValue = x -> isNonnegativeInteger x or (instance(x, List) and all(x, isNonnegativeInteger))

registerTaskKind("invariant", hashTable {
    "version" => 1,
    "requirements" => {"smooth-complete-intersection"},
    "validate_set" => (s -> checkFields(s, "invariant set", taskKindField, {
                ("names", nullable invariantSelector),
                ("control", c -> instance(c, HashTable) and all(values c, invariantValue))
                })),
    "validate_task" => (t -> checkTaskFields(t, {
                ("surface", x -> instance(x, HashTable)), ("name", isString)
                }, {})),
    "validate_result" => (r -> (
            if not invariantValue r#"value" or not invariantValue r#"predicted" then error "invalid invariant result")),
    "expand" => expandInvariants,
    "run" => runInvariant
    });
