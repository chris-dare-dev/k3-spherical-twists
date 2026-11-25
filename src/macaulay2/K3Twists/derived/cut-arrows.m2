-- The marking supplies a homological degree q for the strict upper phase cut.
-- Here HH_i = H^(-i). Keep the cycles at q and the original terms above q.
homologicalCutInclusion = method()
homologicalCutInclusion(Complex, ZZ) := ComplexMap => (C, q) -> (
    (lo, hi) := concentration C;
    if q <= lo then return id_C;
    U := canonicalTruncation(C, q, infinity);
    if q > hi then return map(C, U, 0);
    map(C, U, i -> if i == q then inducedMap(C_i, U_i) else id_(C_i))
    )

lowerProjection = (C, p) -> (
    (lo, hi) := concentration C;
    if p >= hi then return id_C;
    L := canonicalTruncation(C, -infinity, p);
    if p < lo then return map(L, C, 0);
    map(L, C, i -> if i == p then map(L_i, C_i, id_(C_i)) else id_(C_i))
    )

kernelInclusion = f -> (
    D := source f;
    U := kernel f;
    map(D, U, i -> inducedMap(D_i, U_i))
    )

validCutMap = f -> isWellDefined f and isComplexMorphism f and all(values f.map, isWellDefined)

-- Lower projections are degreewise onto. Their ordinary kernels compute
-- homotopy fibres, and their inverse images compute homotopy pullbacks.
signedCutInclusion = method()
signedCutInclusion(Complex, ComplexMap, ZZ, ZZ) := ComplexMap => (C, f, direction, q) -> (
    if not member(direction, {1,-1}) then error "expected twist sign 1 or -1";
    if not validCutMap f then error "expected a degree-zero chain map on the presented modules";
    standard := cone f;
    if C != (if direction == 1 then standard else standard[1]) then
        error "output must be the indicated cone or shifted cone in the supplied presentation";
    A := source f;
    B := target f;
    if direction == 1 then (
        -- Pull back the top cycles in cone(f_low) across C -> cone(f_low).
        low := cone canonicalTruncation(f, -infinity, q-1);
        a := lowerProjection(A, q-1);
        b := lowerProjection(B, q-1);
        p := map(low, C, i -> a_(i-1) ++ b_i);
        k := homologicalCutInclusion(low, q);
        quotient := coker k;
        return kernelInclusion(canonicalMap(quotient, low) * p)
        );
    -- Remove bottom cohomology from fib(f_high) and compose into the fibre.
    high := (cone canonicalTruncation(f, q, infinity))[1];
    jA := homologicalCutInclusion(A, q);
    jB := homologicalCutInclusion(B, q);
    j := map(C, high, i -> jA_i ++ jB_(i+1));
    j * kernelInclusion(lowerProjection(high, q-1))
    )

-- Test even the bottom homology of the cone (surjectivity matters there).
acyclicCone = f -> (
    C := cone f;
    (lo, hi) := concentration C;
    all(lo..hi, i -> HH_i C == 0)
    )

-- A strictly commuting square with specified vertical quasi-isomorphisms
-- witnesses equality of the two arrows over the identified target in D(R).
certifiesCutSquare = method()
certifiesCutSquare(ComplexMap, ComplexMap, ComplexMap, ComplexMap) := Boolean => (a, b, s, t) -> (
    if source s =!= source a or target s =!= source b
        or source t =!= target a or target t =!= target b then return false;
    if not all({a,b,s,t}, validCutMap) then return false;
    t*a == b*s and acyclicCone s and acyclicCone t
    )
