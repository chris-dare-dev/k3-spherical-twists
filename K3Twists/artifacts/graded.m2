-- Degree-zero maps are stored row-major with source and target basis degrees.
artifactBasis = M -> apply(degrees M, first)

artifactFree = (R, basis) -> (
    if not instance(basis, List) or not all(basis, d -> instance(d, ZZ)) then
        error "expected integer basis degrees";
    R^(apply(basis, d -> {-d}))
    )

artifactMatrixData = (K, f) -> (
    R := K#"ring";
    if ring f =!= R then error "matrix belongs to a different model ring";
    if f.?RingMap then error "matrix must be linear over the model ring";
    if not isHomogeneous f then error "matrix must be homogeneous";
    A := ring first K#"equations";
    sd := artifactBasis source f;
    td := artifactBasis target f;
    rows := entries f;
    apply(#td, i -> apply(#sd, j -> (
        c := rows#i#j;
        if c != 0 and degree c =!= {sd#j - td#i} then error "matrix must preserve the grading";
        quarticPolynomialData(lift(c, A), char R)
        )))
    )

artifactMatrix = (K, F, G, rows) -> (
    sourceDegrees := artifactBasis F;
    targetDegrees := artifactBasis G;
    if not instance(rows, List) or #rows != #targetDegrees or
        not all(rows, row -> instance(row, List) and #row == #sourceDegrees) then
        error "matrix shape does not agree with basis degrees";
    if #sourceDegrees == 0 or #targetDegrees == 0 then return map(G, F, 0);
    R := K#"ring";
    A := ring first K#"equations";
    matrixEntries := apply(#rows, i -> apply(#sourceDegrees, j ->
        sub(artifactPolynomial(A, rows#i#j, sourceDegrees#j - targetDegrees#i), R)));
    map(G, F, matrixEntries)
    )

requireArtifactRing = (K, M, digest) -> (
    if ring M =!= K#"ring" then error "object belongs to a different model ring";
    artifactParent(K, digest);
    )

artifactPresentationFields = {"source", "target", "matrix"}

artifactPresentationData = (K, M) -> (
    f := presentation M;
    hashTable {"source" => artifactBasis source f,
        "target" => artifactBasis target f, "matrix" => artifactMatrixData(K, f)
        }
    )

artifactPresentedModule = (K, info) -> (
    R := K#"ring";
    F := artifactFree(R, info#"source");
    G := artifactFree(R, info#"target");
    coker artifactMatrix(K, F, G, info#"matrix")
    )

gradedPresentationArtifact = method()
gradedPresentationArtifact(K3Surface, Module, String) := HashTable => (K, M, digest) -> (
    requireArtifactRing(K, M, digest);
    info := append(pairs artifactPresentationData(K, M), "model_digest" => digest);
    artifactEnvelope(1, "graded-presentation", hashTable info)
    )

loadGradedPresentation = method()
loadGradedPresentation(K3Surface, HashTable) := Module => (K, data) -> (
    info := artifactPayload(data, "graded-presentation", prepend("model_digest", artifactPresentationFields), {1});
    artifactParent(K, info#"model_digest");
    artifactPresentedModule(K, info)
    )

requireArtifactDifferential = f -> (
    if not isWellDefined f then error "differential must descend through the module relations";
    f
    )

gradedComplexArtifact = method()
gradedComplexArtifact(K3Surface, Complex, String) := HashTable => (K, C, digest) -> (
    requireArtifactRing(K, C, digest);
    (lo, hi) := concentration C;
    if not instance(lo, ZZ) or not instance(hi, ZZ) or lo > hi then error "expected a nonempty bounded complex";
    if not isWellDefined C then error "complex differentials must compose to zero";
    modules := apply(toList(lo..hi), i -> C_i);
    free := all(modules, isFreeModule);
    terms := if free then apply(modules, artifactBasis) else apply(modules, M -> artifactPresentationData(K, M));
    diffs := apply(toList(lo+1..hi), i -> (
        f := requireArtifactDifferential ((C.dd)_i);
        artifactMatrixData(K, f)
        ));
    artifactEnvelope(if free then 1 else 2, "graded-complex", hashTable {
        "model_digest" => digest, "base" => lo, "terms" => terms, "differentials" => diffs
        })
    )

loadGradedComplex = method()
loadGradedComplex(K3Surface, HashTable) := Complex => (K, data) -> (
    info := artifactPayload(data, "graded-complex", {"model_digest", "base", "terms", "differentials"}, {1, 2});
    R := artifactParent(K, info#"model_digest");
    lo := info#"base";
    if not instance(lo, ZZ) or not instance(info#"terms", List) or #info#"terms" == 0 then
        error "expected nonempty complex terms and integer base degree";
    modules := if data#"version" === 1 then apply(info#"terms", basis -> artifactFree(R, basis))
        else apply(info#"terms", term -> artifactPresentedModule(K, artifactFields(term, artifactPresentationFields)));
    diffs := info#"differentials";
    if not instance(diffs, List) or #diffs != #modules - 1 then error "wrong number of differentials";
    maps := apply(#diffs, i -> requireArtifactDifferential artifactMatrix(K, modules#(i+1), modules#i, diffs#i));
    C := complex(if #maps == 0 then modules else maps, Base => lo);
    if not isWellDefined C then error "complex differentials must compose to zero";
    C
    )

artifactChainMapFields = {"model_digest", "source_digest", "target_digest", "components"}

artifactMapIndices = (D, E) -> (
    (dlo, dhi) := concentration D;
    (elo, ehi) := concentration E;
    if not all({dlo, dhi, elo, ehi}, i -> instance(i, ZZ)) or dlo > dhi or elo > ehi then
        error "chain map endpoints must be nonempty bounded complexes";
    -- Outside the intersection at least one term is zero.
    lo := max(dlo, elo);
    hi := min(dhi, ehi);
    if lo > hi then {} else toList(lo..hi)
    )

requireArtifactChainMap = u -> (
    if not isWellDefined u or not isComplexMorphism u then
        error "expected a well-defined degree-zero chain map";
    u
    )

gradedChainMapArtifact = method()
gradedChainMapArtifact(K3Surface, ComplexMap, String, Sequence) := HashTable => (K, u, model, endpoints) -> (
    (src, dst) := endpoints;
    D := source u;
    E := target u;
    requireArtifactRing(K, D, model);
    requireArtifactRing(K, E, model);
    artifactDigest src;
    artifactDigest dst;
    requireArtifactChainMap u;
    indices := artifactMapIndices(D, E);
    artifactEnvelope(1, "graded-chain-map", hashTable {
        "model_digest" => model, "source_digest" => src, "target_digest" => dst,
        "components" => apply(indices, i -> artifactMatrixData(K, requireArtifactDifferential u_i))
        })
    )

loadGradedChainMap = method()
loadGradedChainMap(K3Surface, HashTable, Sequence, Sequence) := ComplexMap => (K, data, src, dst) -> (
    info := artifactPayload(data, "graded-chain-map", artifactChainMapFields, {1});
    (D, sourceDigest) := src;
    (E, targetDigest) := dst;
    if artifactDigest sourceDigest =!= info#"source_digest" or artifactDigest targetDigest =!= info#"target_digest" then
        error "chain map endpoint digest mismatch";
    model := info#"model_digest";
    requireArtifactRing(K, D, model);
    requireArtifactRing(K, E, model);
    indices := artifactMapIndices(D, E);
    matrices := info#"components";
    if not instance(matrices, List) or #matrices != #indices then error "wrong number of chain map components";
    maps := hashTable apply(indices, matrices, (i, rows) -> i => requireArtifactDifferential artifactMatrix(K, D_i, E_i, rows));
    requireArtifactChainMap map(E, D, maps, Degree => 0)
    )
