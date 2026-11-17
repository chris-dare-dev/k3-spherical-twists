newPackage(
    "K3Twists",
    Version => "0.1",
    Headline => "sheaves on explicit K3 surfaces that arise from spherical twists along O and O(H)",
    Authors => {{Name => "Christopher Dare"}},
    PackageExports => {"Varieties"},
    DebuggingMode => false
    )

export {
    "k3Surface",
    "Characteristic",
    "Seed",
    "cohomologyDims",
    "extDims",
    "pointIdealSheaf",
    "pointSheaf",
    "kernelBundle",
    "pointKernelBundle",
    "quotientBundle",
    "chainNumber",
    "sheafInvariants",
    "Slow"
    }

-- A K3 surface of degree 2d in P^(d+1), d = 2, 3 or 4, as a complete intersection through the
-- point x = (1:0:...:0): a quartic, a quadric and a cubic, three quadrics.
completeIntersectionDegrees = new HashTable from {2 => {4}, 3 => {2, 3}, 4 => {2, 2, 2}};

k3Surface = method(Options => {Characteristic => 32003, Seed => 1})
k3Surface ZZ := HashTable => opts -> d -> (
    if not completeIntersectionDegrees#?d then error "expected d = 2, 3 or 4";
    degs := completeIntersectionDegrees#d;
    kk := ZZ/(opts.Characteristic);
    x := getSymbol "x";
    N := d + 1;
    R := kk(monoid[x_0..x_N]);
    setRandomSeed opts.Seed;
    atPoint := apply(gens R, v -> if v == R_0 then v => 1_kk else v => 0_kk);
    eqs := apply(degs, e -> (g := random(e, R); g - sub(g, atPoint) * R_0^e));
    I := ideal eqs;
    if codim I != #degs then error "the random forms are not a complete intersection; change the seed";
    if dim(I + minors(#degs, jacobian I)) != 0 then error "the surface is singular; change the seed";
    S := R / I;
    new HashTable from {
        "d" => d,
        "n" => d + 2,
        "degrees" => degs,
        "ring" => S,
        "variety" => Proj S,
        "point" => ideal drop(gens S, 1)
        }
    )

cohomologyDims = method()
cohomologyDims CoherentSheaf := List => F -> apply(3, i -> rank HH^i(F))

extDims = method()
extDims(CoherentSheaf, CoherentSheaf) := List => (F, G) -> apply(3, i -> rank Ext^i(F, G))

-- I_x, the ideal sheaf of the point
pointIdealSheaf = method()
pointIdealSheaf HashTable := CoherentSheaf => K -> sheaf module K#"point"

-- O_x, the skyscraper sheaf
pointSheaf = method()
pointSheaf HashTable := CoherentSheaf => K -> sheaf((K#"ring")^1 / K#"point")

-- M_H, the kernel of H^0(O(H)) (x) O -> O(H)
kernelBundle = method()
kernelBundle HashTable := CoherentSheaf => K -> (
    S := K#"ring";
    sheaf kernel map(S^{1}, S^(numgens S), vars S)
    )

-- M_x, the kernel of H^0(I_x(H)) (x) O -> I_x(H); the linear forms through x generate I_x(H)
pointKernelBundle = method()
pointKernelBundle HashTable := CoherentSheaf => K -> (sheaf kernel gens K#"point")(1)

-- Q, the cokernel of O -> H^0(O(H))^dual (x) O(H)
quotientBundle = method()
quotientBundle HashTable := CoherentSheaf => K -> (
    S := K#"ring";
    sheaf coker map(S^{numgens S : 1}, S^1, transpose vars S)
    )

-- c_(-1) = c_0 = 1, c_(k+1) = n c_k - c_(k-1)
chainNumber = method()
chainNumber(ZZ, ZZ) := ZZ => (n, k) -> (
    if k < -1 then error "expected k >= -1";
    (a, b) := (1, 1);
    for j from 1 to k do (a, b) = (b, n * b - a);
    b
    )

-- A list of {name, computed value, predicted value}.  The default list uses sheaf cohomology only.
-- With Slow => true the same numbers are also computed as Ext groups, together with the Ext groups
-- of the sheaves with themselves; these take most of the time and are practical for d = 2 only.
sheafInvariants = method(Options => {Slow => false})
sheafInvariants HashTable := List => opts -> K -> (
    n := K#"n";
    X := K#"variety";
    OX := OO_X^1;
    O1 := OO_X^1(1);
    Ix := pointIdealSheaf K;
    Ox := pointSheaf K;
    MH := kernelBundle K;
    Mx := pointKernelBundle K;
    Q := quotientBundle K;
    out := {
        {"h^i(O)", cohomologyDims OX, {1, 0, 1}},
        {"h^i(O(H))", cohomologyDims O1, {n, 0, 0}},
        {"h^i(O(-H))", cohomologyDims OX(-1), {0, 0, n}},
        {"h^i(I_x)", cohomologyDims Ix, {0, 0, 1}},
        {"h^i(I_x(-H))", cohomologyDims Ix(-1), {0, 1, n}},
        {"h^i(I_x(H))", cohomologyDims Ix(1), {chainNumber(n, 1), 0, 0}},
        {"rank M_H", rank MH, n - 1},
        {"h^i(M_H)", cohomologyDims MH, {0, 0, n}},
        {"h^i(M_H(-H))", cohomologyDims MH(-1), {0, 1, n^2 - 1}},
        {"generators of I_x(H)", numgens K#"point", n - 1},
        {"rank M_x", rank Mx, n - 2},
        {"h^i(M_x)", cohomologyDims Mx, {0, 0, chainNumber(n, 1)}},
        {"h^i(M_x(-H))", cohomologyDims Mx(-1), {0, 0, chainNumber(n, 2)}},
        {"rank Q", rank Q, n - 1},
        {"h^i(Q)", cohomologyDims Q, {n^2 - 1, 1, 0}}
        };
    if opts.Slow then out = out | {
        {"Ext^i(O, O(H))", extDims(OX, O1), {n, 0, 0}},
        {"Ext^i(O(H), O)", extDims(O1, OX), {0, 0, n}},
        {"Ext^i(O(H), M_H)", extDims(O1, MH), {0, 1, n^2 - 1}},
        {"Ext^i(M_x, O_x)", extDims(Mx, Ox), {n - 2, 0, 0}},
        {"Ext^i(I_x(H), I_x(H))", extDims(Ix(1), Ix(1)), {1, 2, 1}},
        {"Ext^i(M_H, M_H)", extDims(MH, MH), {1, 0, 1}},
        {"Ext^i(M_x, M_x)", extDims(Mx, Mx), {1, 2, 1}}
        };
    out
    )

beginDocumentation()

doc ///
    Key
        K3Twists
    Headline
        sheaves on explicit K3 surfaces that arise from spherical twists along O and O(H)
    Description
        Text
            The package builds a K3 surface of degree $2d$ in $\mathbb{P}^{d+1}$ for $d = 2, 3, 4$
            through a chosen point, constructs the sheaves $I_x$, $M_H$, $M_x$ and $Q$, and compares
            their cohomology and Ext groups with closed formulas in $n = d + 2$.
///

TEST ///
    -- the recursion c_(k+1) = n c_k - c_(k-1)
    assert(apply(4, k -> chainNumber(4, k)) == {1, 3, 11, 41});
    assert(chainNumber(5, 2) == 19);
///

TEST ///
    -- the quartic surface: the surface itself and the two line bundles
    K = k3Surface 2;
    X = K#"variety";
    assert(dim X == 2);
    assert(degree X == 4);
    assert(cohomologyDims(OO_X^1) == {1, 0, 1});
    assert(cohomologyDims(OO_X^1(1)) == {4, 0, 0});
    assert(extDims(OO_X^1(1), OO_X^1) == {0, 0, 4});
///

TEST ///
    -- the quartic surface: every invariant of the fast list
    K = k3Surface 2;
    scan(sheafInvariants K, r -> assert(r#1 === r#2));
///

TEST ///
    -- a second quartic, from another seed and another prime field
    K = k3Surface(2, Seed => 7, Characteristic => 10007);
    scan(sheafInvariants K, r -> assert(r#1 === r#2));
///

TEST ///
    -- degree 6: a quadric and a cubic in P^4
    K = k3Surface 3;
    assert(degree K#"variety" == 6);
    scan(sheafInvariants K, r -> assert(r#1 === r#2));
///

TEST ///
    -- degree 8: three quadrics in P^5
    K = k3Surface 4;
    assert(degree K#"variety" == 8);
    scan(sheafInvariants K, r -> assert(r#1 === r#2));
///

TEST ///
    -- on the quartic, three of the numbers again as Ext groups
    K = k3Surface 2;
    X = K#"variety";
    assert(extDims(OO_X^1, OO_X^1(1)) == {4, 0, 0});
    assert(extDims(OO_X^1(1), kernelBundle K) == {0, 1, 15});
    assert(extDims(pointKernelBundle K, pointSheaf K) == {2, 0, 0});
///

end--
