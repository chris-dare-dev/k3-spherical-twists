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

gradedPresentationArtifact = method()
gradedPresentationArtifact(K3Surface, Module, String) := HashTable => (K, M, digest) -> (
    requireArtifactRing(K, M, digest);
    f := presentation M;
    artifactEnvelope("graded-presentation", hashTable {
        "model_digest" => digest, "source" => artifactBasis source f,
        "target" => artifactBasis target f, "matrix" => artifactMatrixData(K, f)
        })
    )

loadGradedPresentation = method()
loadGradedPresentation(K3Surface, HashTable) := Module => (K, data) -> (
    info := artifactPayload(data, "graded-presentation", {"model_digest", "source", "target", "matrix"});
    R := artifactParent(K, info#"model_digest");
    F := artifactFree(R, info#"source");
    G := artifactFree(R, info#"target");
    coker artifactMatrix(K, F, G, info#"matrix")
    )

gradedComplexArtifact = method()
gradedComplexArtifact(K3Surface, Complex, String) := HashTable => (K, C, digest) -> (
    requireArtifactRing(K, C, digest);
    (lo, hi) := concentration C;
    if not instance(lo, ZZ) or not instance(hi, ZZ) or lo > hi then error "expected a nonempty bounded complex";
    indices := toList(lo..hi);
    if not all(indices, i -> isFreeModule C_i) then error "version 1 requires free complex terms";
    if not isWellDefined C then error "complex differentials must compose to zero";
    artifactEnvelope("graded-complex", hashTable {
        "model_digest" => digest, "base" => lo, "terms" => apply(indices, i -> artifactBasis C_i),
        "differentials" => apply(toList(lo+1..hi), i -> artifactMatrixData(K, (C.dd)_i))
        })
    )

loadGradedComplex = method()
loadGradedComplex(K3Surface, HashTable) := Complex => (K, data) -> (
    info := artifactPayload(data, "graded-complex", {"model_digest", "base", "terms", "differentials"});
    R := artifactParent(K, info#"model_digest");
    lo := info#"base";
    if not instance(lo, ZZ) or not instance(info#"terms", List) or #info#"terms" == 0 then
        error "expected nonempty complex terms and integer base degree";
    modules := apply(info#"terms", basis -> artifactFree(R, basis));
    diffs := info#"differentials";
    if not instance(diffs, List) or #diffs != #modules - 1 then error "wrong number of differentials";
    maps := apply(#diffs, i -> artifactMatrix(K, modules#(i+1), modules#i, diffs#i));
    C := complex(if #maps == 0 then modules else maps, Base => lo);
    if not isWellDefined C then error "complex differentials must compose to zero";
    C
    )
