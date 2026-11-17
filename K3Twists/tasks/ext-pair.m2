-- Kind "ext_pair": Ext^i(E, F) for two sheaves of the catalogue ------------------------------------

-- A hint for ordering tasks and choosing limits: the rank of the sheaf Hom(E, F), a sheaf of rank 0
-- counted as rank 1; 0 when nothing is computed.  c and e are rows of catalogueClasses.
extPairCost = (c, e) -> (
    if extMethod(c#2, c#1#0, e#2, e#1#0) == "not computed" then 0
    else max(c#1#0, 1) * max(e#1#0, 1)
    )

expandExtPairs = (i, set, surfaces) -> flatten apply(surfaces, s -> (
        d := s#"d";
        classes := apply(catalogueSpecsFor(d, s#"special_quadric", null), row -> take(row, 3));
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
                    "predicted" => new HashTable from {"chi" => -mukaiPairing(d, c#1, e#1)},
                    "surface" => s,
                    "source" => c#0,
                    "target" => e#0
                    }))
        ))

runExtPair = task -> (
    s := checkSurfaceSpec task#"surface";
    (setup, entries) := timed(() -> (
            K := surfaceFromSpec s;
            {catalogueEntry(K, task#"source"), catalogueEntry(K, task#"target")}));
    (compute, row) := timed(() -> extTableRow(entries#0, entries#1));
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

extSelector = x -> x === "all" or isStringList x
extPrediction = x -> instance(x, HashTable) and x#?"chi" and instance(x#"chi", ZZ)
extValue = x -> (
    extPrediction x and x#?"dims" and instance(x#"dims", List)
    and #(x#"dims") == 3 and all(x#"dims", isNonnegativeInteger)
    )

registerTaskKind("ext_pair", hashTable {
    "version" => 1,
    "requirements" => {"smooth-complete-intersection"},
    "validate_set" => (s -> checkFields(s, "ext_pair set", taskKindField, {
                ("sheaves", nullable extSelector), ("sources", nullable extSelector), ("targets", nullable extSelector)
                })),
    "validate_task" => (t -> checkTaskFields(t, {
                ("surface", x -> instance(x, HashTable)), ("source", isString), ("target", isString)
                }, {})),
    "validate_result" => (r -> (
            if not extPrediction r#"predicted" or (r#"value" =!= null and not extValue r#"value") then
                error "invalid ext_pair result")),
    "expand" => expandExtPairs,
    "run" => runExtPair
    });
