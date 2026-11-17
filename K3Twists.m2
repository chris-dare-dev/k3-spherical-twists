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
    "Slow",
    "SpecialQuadric",
    "mukaiBundle",
    "tracelessKernelBundle",
    "quadricKernelBundle",
    "mukaiPairing",
    "twistVector",
    "dualVector",
    "catalogue",
    "extViaHom",
    "extTableRow"
    }

-- A K3 surface of degree 2d in P^(d+1), d = 2, 3 or 4, as a complete intersection through the
-- point x = (1:0:...:0): a quartic, a quadric and a cubic, three quadrics.
completeIntersectionDegrees = new HashTable from {2 => {4}, 3 => {2, 3}, 4 => {2, 2, 2}};

-- With SpecialQuadric => true and d = 3 the quadric is x_0 x_1 + x_2 x_3 + x_4^2, which has an explicit
-- matrix factorisation; the surface then carries the rank 2 bundle of mukaiBundle.
k3Surface = method(Options => {Characteristic => 32003, Seed => 1, SpecialQuadric => false})
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
    if opts.SpecialQuadric then (
        if d != 3 then error "SpecialQuadric is for d = 3";
        eqs = {R_0 * R_1 + R_2 * R_3 + R_4^2, eqs#1};
        );
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
        "point" => ideal drop(gens S, 1),
        "specialQuadric" => opts.SpecialQuadric
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

-- E_2, the kernel of sl(V) (x) O -> V (x) O(H), phi |-> phi(x), V = H^0(O(H)).  It is the sheaf with
-- T_O T_{O(H)}(O[1]) = E_2[1]; rank n^2 - n - 1.
tracelessKernelBundle = method()
tracelessKernelBundle HashTable := CoherentSheaf => K -> (
    S := K#"ring";
    n := numgens S;
    unit := (i, j) -> matrix table(n, n, (a, b) -> if (a, b) == (i, j) then 1_S else 0_S);
    basisMatrices := flatten apply(n, i -> apply(n, j ->
            if i != j then unit(i, j) else if i < n - 1 then unit(i, i) - unit(n - 1, n - 1) else null));
    basisMatrices = select(basisMatrices, m -> m =!= null);
    cols := apply(basisMatrices, m -> m * transpose vars S);
    sheaf kernel map(S^{n : 1}, S^(#cols), fold((a, b) -> a | b, cols))
    )

-- M_2H, the kernel of H^0(O(2H)) (x) O -> O(2H); T_O(O(2H)) = M_2H[1]
quadricKernelBundle = method()
quadricKernelBundle HashTable := CoherentSheaf => K -> (
    S := K#"ring";
    B := basis(2, S);
    sheaf kernel map(S^{2}, S^(numColumns B), entries B)
    )

-- On the surface with the special quadric (d = 3): the cokernel of the 4 x 4 matrix A of linear forms
-- with A^2 = (x_0 x_1 + x_2 x_3 + x_4^2) Id.  A rank 2 bundle with four sections, class (2, 1, 2).
mukaiBundle = method()
mukaiBundle HashTable := CoherentSheaf => K -> (
    if not K#"specialQuadric" then error "expected a surface built with SpecialQuadric => true";
    S := K#"ring";
    x := gens S;
    A := matrix {
        {x#4, 0, x#0, x#2},
        {0, x#4, -x#3, x#1},
        {x#1, -x#2, -x#4, 0},
        {x#3, x#0, 0, -x#4}};
    sheaf coker map(S^4, S^{4 : -1}, A)
    )

-- classes (r, c, s) with <v, w> = 2d c c' - r s' - r' s; chi(E, F) = -<v(E), v(F)>
mukaiPairing = method()
mukaiPairing(ZZ, List, List) := ZZ => (d, v, w) -> 2 * d * v#1 * w#1 - v#0 * w#2 - v#2 * w#0

twistVector = method()
twistVector(ZZ, List, ZZ) := List => (d, v, t) -> {v#0, v#1 + v#0 * t, v#2 + 2 * d * v#1 * t + d * v#0 * t^2}

dualVector = method()
dualVector List := List => v -> {v#0, -v#1, v#2}

-- Ext^i(E, F) as the cohomology of the sheaf Hom(E, F); valid when E is locally free
extViaHom = method()
extViaHom(CoherentSheaf, CoherentSheaf) := List => (E, F) -> cohomologyDims sheafHom(E, F)

-- The sheaves of the study with their classes: a list of {name, sheaf, class, locally free}
catalogue = method()
catalogue HashTable := List => K -> (
    d := K#"d";
    n := K#"n";
    X := K#"variety";
    S := K#"ring";
    tw := (name, F, v, lf, ts) -> apply(ts, t -> {
            name | (if t == 0 then "" else "(" | toString t | "H)"), F(t), twistVector(d, v, t), lf});
    Ix := pointIdealSheaf K;
    MH := kernelBundle K;
    Mx := pointKernelBundle K;
    out := tw("O", OO_X^1, {1, 0, 1}, true, {-2, -1, 0, 1, 2, 3})
        | tw("I_x", Ix, {1, 0, 0}, false, {-1, 0, 1, 2})
        | {{"O_x", pointSheaf K, {0, 0, 1}, false}}
        | tw("M_H", MH, {n - 1, -1, 1}, true, {0, 1})
        | tw("M_H^dual", dual MH, {n - 1, 1, 1}, true, {0, 1})
        | tw("M_x", Mx, {n - 2, -1, 1}, true, {0, 1})
        | tw("M_x^dual", dual Mx, {n - 2, 1, 1}, true, {0})
        | tw("E_2", tracelessKernelBundle K, {n^2 - n - 1, -n, n - 1}, true, {0, 1})
        | tw("M_2H", quadricKernelBundle K, {4 * d + 1, -2, 1}, true, {0, 1});
    if K#"specialQuadric" then (
        U := mukaiBundle K;
        out = out | tw("U", U, {2, 1, 2}, true, {-1, 0}) | tw("U^dual", dual U, {2, -1, 2}, true, {0, 1});
        );
    out
    )

-- One row of the table of Ext groups: {name of E, name of F, dimensions or null, chi predicted, method}.
-- The dimensions are computed when one of the two sheaves is locally free (by Serre duality if it is F).
extTableRow = method()
extTableRow(ZZ, List, List) := List => (d, a, b) -> (
    chi := -mukaiPairing(d, a#2, b#2);
    -- of two locally free sheaves the one of smaller rank is used as the source of the Hom sheaf
    if a#3 and (not b#3 or a#2#0 <= b#2#0) then {a#0, b#0, extViaHom(a#1, b#1), chi, "Hom sheaf"}
    else if b#3 then {a#0, b#0, reverse extViaHom(b#1, a#1), chi, "Serre duality"}
    else {a#0, b#0, null, chi, "not computed"}
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

TEST ///
    -- the classes of the catalogue have the ranks of the sheaves, and chi(O, F) = r + s
    K = k3Surface 2;
    scan(catalogue K, a -> (
        assert(rank a#1 == a#2#0);
        if a#3 and a#2#0 <= 3 then (
            h := cohomologyDims a#1;
            assert(h#0 - h#1 + h#2 == a#2#0 + a#2#2));
        ));
///

TEST ///
    -- the rank 2 bundle on the degree 6 surface with the special quadric: class (2, 1, 2), spherical
    K = k3Surface(3, SpecialQuadric => true);
    U = mukaiBundle K;
    assert(rank U == 2);
    assert(cohomologyDims U == {4, 0, 0});
    assert(extViaHom(U, U) == {1, 0, 1});
///

TEST ///
    -- Ext groups through Hom sheaves and Serre duality, against known values on the quartic
    K = k3Surface 2;
    cat = catalogue K;
    pick = name -> first select(cat, a -> a#0 == name);
    assert((extTableRow(2, pick "M_H", pick "M_H"))#2 == {1, 0, 1});
    assert((extTableRow(2, pick "O(1H)", pick "M_H"))#2 == {0, 1, 15});
    assert((extTableRow(2, pick "I_x(1H)", pick "M_x"))#2 == {0, 1, 10});
    assert((extTableRow(2, pick "M_x", pick "O_x"))#2 == {2, 0, 0});
///

end--
