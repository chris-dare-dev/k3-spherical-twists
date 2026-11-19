-- A dual Koszul resolution gives finite derived global sections. The cover
-- forms have no common zero on Proj, so the augmented resolution is locally
-- split. A positive power beyond the term bounds makes each twist acyclic
-- and identifies its global sections with the corresponding graded piece.
quarticSectionsComplex = (K, C) -> (
    R := K#"ring";
    P := ring first K#"equations";
    quotientMap := map(R, P, gens R);
    (lo, hi) := concentration C;
    bounds := apply(toList(lo..hi), i -> (
        M := C_i;
        if M == 0 then 0
        -- For R-free terms use the cohomology of line bundles on the quartic.
        else if isFreeModule M then max flatten degrees M
        else regularity pushForward(quotientMap, M)
        ));
    n := 1 + max prepend(0, bounds);
    forms := quarticCoverForms K;
    powers := map(R^1, R^{#forms : -n}, {apply(forms, x -> x^n)});
    cover := naiveTruncation(koszulComplex powers, 1, #forms)[1];
    D := Hom(cover, C);
    (a, b) := concentration D;
    kk := K#"field";
    strands := apply(toList(a..b), i -> basis(0, D_i));
    complex hashTable for i from a+1 to b list (
        f := (D.dd)_i;
        left := strands#(i-a-1);
        right := strands#(i-a);
        linear := if f == 0 then map(kk^(numColumns left), kk^(numColumns right), 0)
            else if isFreeModule target f and isFreeModule source f then
                sub(last coefficients(matrix(f * right), Monomials => matrix left), kk)
            else part(0, f);
        i => linear
        )
    )

hypercohomologyObservation = method(Options => {Degrees => null})
hypercohomologyObservation(K3Surface, Complex) := DegreeObservation => opts -> (K, C) -> (
    requireDegrees opts.Degrees;
    if ring C =!= K#"ring" then error "complex belongs to a different model ring";
    if K#"d" != 2 then
        return unsupportedObservation("hypercohomology", {C}, "requires a certified smooth quartic");
    if not isWellDefined C then error "expected a bounded complex with differentials that compose to zero";
    (lo, hi) := concentration C;
    if not all(lo+1..hi, i -> (
        f := (C.dd)_i;
        isHomogeneous f and degree f === {0} and isWellDefined f
        )) then error "expected degree-zero differentials respecting the module relations";
    G := quarticSectionsComplex(K, C);
    -- Keep the sparse homology calculation in M2. Degree i is homological -i.
    measureDegrees("hypercohomology", {C}, "degree-zero Koszul total complex", {-hi, 2 - lo},
        opts.Degrees, i -> rank HH_(-i) G)
    )
