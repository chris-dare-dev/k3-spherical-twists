-- The geometric input is the Tramel--Xia lift for a single contracted (-2)-curve.
CurveWallMark = new Type of HashTable
CurveWallMark.synonym = "single-curve wall marking"

curveWallMark = method()
curveWallMark(DivisorClass, DivisorClass, List, List) := CurveWallMark => (H, C, beta, z) -> (
    if #beta != 2 or not instance(beta#0, DivisorClass) or not instance(beta#1, ZZ) then
        error "expected beta as a marked numerator and an integer denominator";
    (b, den) := toSequence beta;
    if den <= 0 or #z != 2 or not all(z, x -> instance(x, ZZ) or instance(x, QQ)) then
        error "expected a positive beta denominator and exact real and imaginary parts of z";
    h2 := divisorPairing(H,H);
    if h2 <= 0 or divisorPairing(C,C) != -2 or divisorPairing(H,C) != 0 or divisorPairing(H,b) != 0 then
        error "expected a positive H orthogonal to the marked (-2)-curve and beta";
    bc := divisorPairing(b,C)/den;
    if bc == floor bc then error "beta lies on an endpoint of the curve-heart strip";
    if z#0 <= 0 or z#0 + (z#1)^2/h2 <= -divisorPairing(b,b)/(2*den^2) then
        error "the marked charge fails the single-curve positivity test";
    new CurveWallMark from {"nefDivisor" => H, "curve" => C, "curveCutoff" => floor(bc)-1,
        "slopeCutoff" => -z#1}
    )

-- In a local frame the kernel of evaluation is I_Z L and L is its double dual.
-- For E = [L -> Q], the map E -> L(mC)[1] is s_C^m in degree one.
curveWallIdealCut = method()
curveWallIdealCut(CurveWallMark, DivisorClass, RingElement, ComplexMap) := HashTable => (W, L, n, f) -> (
    C := W#"curve";
    H := W#"nefDivisor";
    degC := divisorPairing(C,L);
    if divisorPairing(H,L) >= W#"slopeCutoff" then error "expected the line strictly below the first slope cutoff";
    if concentration(source f) != (0,0) or concentration(target f) != (0,0) or not validCutMap f then
        error "expected a line evaluation in degree zero";
    e := f_0;
    line := source e;
    if not isFreeModule line or numgens line != 1 or coker e != 0 or dim(target e) > 0 then
        error "expected a free line surjecting onto a finite-length quotient in a local frame";
    if ring n =!= ring line or n == 0 or degree n != degree(1_(ring line)) then
        error "expected the degree-zero local equation of the marked Cartier divisor";
    m := max(0, (degC - W#"curveCutoff" - 1) // 2);
    g := n^m * id_line;
    if ker g != 0 then error "the marked section must be regular";
    tail := divisorClass(L#"lattice", apply(L#"coordinates", C#"coordinates", (a,b) -> a + m*b));
    incl := inducedMap(line, ker e);
    U := complex(g*incl);
    E := cone f;
    j := map(E, U, hashTable {1 => incl});
    G := complex(line, Base => 1);
    p := map(G, E, hashTable {1 => g});
    hashTable {"curveSteps" => m, "tailDivisor" => tail, "inclusion" => j, "projection" => p}
    )

-- Pull the n-power torsion of H_0 back into the original complex. This has
-- a geometric phase interpretation when the outer pieces have the required gaps.
curveTorsionPreimage = method()
curveTorsionPreimage(Complex, RingElement) := ComplexMap => (E, n) -> (
    if first concentration E < 0 then error "expected a complex in nonnegative homological degrees";
    if ring n =!= ring E or n == 0 then error "expected a nonzero equation in the complex's ring";
    N := coker E.dd_1;
    if N == 0 then return id_E;
    rel := presentation N;
    outside := (target rel) / saturate(image rel, ideal n);
    residue := map(outside,N,id_(target rel)) * map(N,E_0,1);
    kernelInclusion(map(complex outside, E, hashTable {0 => residue}))
    )
