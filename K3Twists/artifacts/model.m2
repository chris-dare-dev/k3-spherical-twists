-- Version 1 stores data over a prime field in the ordered standard-graded coordinates x_0, ...
protect symbol artifactModelDigest

artifactFields = (data, fields) -> (
    if not instance(data, HashTable) or sort keys data =!= sort fields then
        error "unexpected artifact fields";
    data
    )

artifactEnvelope = (kind, payload) -> hashTable {"version" => 1, "kind" => kind, "payload" => payload}

artifactPayload = (data, kind, fields) -> (
    artifactFields(data, {"version", "kind", "payload"});
    if data#"version" =!= 1 or data#"kind" =!= kind then error "unexpected artifact kind or version";
    artifactFields(data#"payload", fields)
    )

artifactDigest = digest -> (
    if not instance(digest, String) or not match("^[a-f0-9]{64}$", digest) then
        error "expected a lowercase SHA-256 model digest";
    digest
    )

artifactCoordinates = n -> apply(n, i -> "x_" | toString i)

artifactPolynomial = (R, terms, d) -> (
    if not instance(terms, List) then error "expected sparse polynomial terms";
    if #terms == 0 then return 0_R;
    p := char R;
    n := numgens R;
    scan(terms, t -> (
        if not instance(t, List) or #t != 2 then error "expected {exponents, coefficient}";
        (e, c) := (t#0, t#1);
        if not instance(e, List) or #e != n or not all(e, i -> instance(i, ZZ) and i >= 0) or sum e != d then
            error "wrong number or degree of exponents";
        if not instance(c, ZZ) or c <= 0 or c >= p then error "coefficient is outside the prime field"
        ));
    if #unique apply(terms, first) != #terms then error "duplicate exponents in a polynomial";
    quarticPolynomial(R, terms)
    )

artifactGenerators = (R, terms, degs) -> (
    if not instance(terms, List) or #terms != #degs or any(terms, t -> t === {}) then
        error "wrong number of nonzero ideal generators";
    apply(terms, degs, (t, d) -> artifactPolynomial(R, t, d))
    )

k3ModelArtifact = method()
k3ModelArtifact K3Surface := HashTable => K -> (
    R := ring first K#"equations";
    data := f -> quarticPolynomialData(lift(f, R), K#"characteristic");
    marks := hashTable apply(pairs K#"markedIdeals", (label, J) -> (
        polynomials := sort(flatten entries gens trim J, f -> first degree f);
        label => apply(polynomials, data)
        ));
    params := hashTable (select(pairs K#"recipe"#"parameters", (k, v) -> k =!= "model") |
        {"family" => K#"recipe"#"family"});
    artifactEnvelope("k3-model", hashTable {
        "parameters" => params, "coordinates" => artifactCoordinates numgens R,
        "grading" => degrees R, "equations" => apply(K#"equations", data), "markings" => marks
        })
    )

loadK3ModelArtifact = method()
loadK3ModelArtifact(HashTable, String) := K3Surface => (data, digest) -> (
    artifactDigest digest;
    info := artifactPayload(data, "k3-model", {"parameters", "coordinates", "grading", "equations", "markings"});
    params := artifactFields(info#"parameters", {"family", "d", "seed", "characteristic", "special_quadric"});
    recipe := k3Recipe params;
    n := params#"d" + 2;
    if info#"coordinates" =!= artifactCoordinates n or info#"grading" =!= apply(n, i -> {1}) then
        error "unexpected coordinate order or grading";
    kk := recipe#"field";
    x := getSymbol "x";
    R := kk(monoid[x_0..x_(n-1)]);
    eqs := artifactGenerators(R, info#"equations", recipe#"degrees");
    marked := markedQuarticDegrees#?(recipe#"family");
    marks := artifactFields(info#"markings", if marked then {"point", "curve"} else {"point"});
    pt := ideal artifactGenerators(R, marks#"point", apply(n - 1, i -> 1));
    c := if marked then ideal artifactGenerators(R, marks#"curve", {1, markedQuarticDegrees#(recipe#"family")})
        else null;
    if marked then recipe = k3Recipe merge(params, hashTable {"model" => hashTable {
            "equation" => info#"equations"#0, "point" => marks#"point", "curve" => marks#"curve"
            }}, (a, b) -> b);
    K := assembleK3Surface(recipe, eqs, pt, c);
    K.cache#(symbol artifactModelDigest) = digest;
    K
    )

-- Attach the identity of a verified model to an already computed surface.
bindK3ModelArtifact = method()
bindK3ModelArtifact(K3Surface, HashTable, String) := K3Surface => (K, data, digest) -> (
    artifactDigest digest;
    if k3ModelArtifact K =!= data then error "artifact does not describe this surface";
    if K.cache#?(symbol artifactModelDigest) and K.cache#(symbol artifactModelDigest) =!= digest then
        error "surface is already bound to a different artifact";
    K.cache#(symbol artifactModelDigest) = digest;
    K
    )

artifactParent = (K, digest) -> (
    artifactDigest digest;
    if not K.cache#?(symbol artifactModelDigest) or K.cache#(symbol artifactModelDigest) =!= digest then
        error "artifact model digest does not match the loaded surface";
    K#"ring"
    )
