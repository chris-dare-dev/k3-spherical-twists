-- Dimensions of cohomology and Ext groups, and the sheaves of the study.  Each sheaf is built once per
-- surface and kept in the surface's cache.

protect symbol localFreeness

cohomologyDims = method()
cohomologyDims CoherentSheaf := List => F -> apply(3, i -> rank HH^i(F))

commonExtVariety = (E, F) -> (
    X := variety E;
    if X =!= variety F then error "Ext requires sheaves on the same variety";
    X
    )

extDims = method()
extDims(CoherentSheaf, CoherentSheaf) := List => (E, F) -> (
    commonExtVariety(E, F);
    apply(3, i -> rank Ext^i(E, F))
    )

locallyFreeForHom = F -> (
    if F.cache#?(symbol localFreeness) then return F.cache#(symbol localFreeness);
    M := module F;
    if isFreeModule M then return true;
    S := ring M;
    if not instance(variety F, ProjectiveVariety) or not isField coefficientRing S
        or not all(degrees S, d -> d == {1}) then return false;
    r := rank M;
    if not instance(r, ZZ) then return false;
    P := presentation M;
    -- A unit Fitt_r on Proj and a zero Fitt_(r-1) certify a rank r bundle.
    F.cache#(symbol localFreeness) = dim fittingIdeal(r, P) <= 0
        and fittingIdeal(r - 1, P) == ideal(0_S)
    )

-- Ext^i(E, F) as the cohomology of the sheaf Hom(E, F); valid when E is locally free
extViaHom = method()
extViaHom(CoherentSheaf, CoherentSheaf) := List => (E, F) -> (
    commonExtVariety(E, F);
    if not locallyFreeForHom E then
        error "extViaHom requires a locally free source; use extDims for direct Ext";
    cohomologyDims sheafHom(E, F)
    )

cachedBundle = (K, key, f) -> cached(K, key, () -> (
    F := f();
    F.cache#(symbol localFreeness) = true;
    F
    ))

-- I_x, the ideal sheaf of the point
pointIdealSheaf = method()
pointIdealSheaf K3Surface := CoherentSheaf => K -> cached(K, "I_x", () -> sheaf module K#"point")

-- O_x, the skyscraper sheaf
pointSheaf = method()
pointSheaf K3Surface := CoherentSheaf => K -> cached(K, "O_x", () -> sheaf((K#"ring")^1 / K#"point"))

-- M_H, the kernel of H^0(O(H)) (x) O -> O(H)
kernelBundle = method()
kernelBundle K3Surface := CoherentSheaf => K -> cachedBundle(K, "M_H", () -> (
        S := K#"ring";
        sheaf kernel map(S^{1}, S^(numgens S), vars S)
        ))

-- M_x, the kernel of H^0(I_x(H)) (x) O -> I_x(H); the linear forms through x generate I_x(H)
pointKernelBundle = method()
pointKernelBundle K3Surface := CoherentSheaf => K -> cachedBundle(K, "M_x", () -> (sheaf kernel gens K#"point")(1))

-- Q, the cokernel of O -> H^0(O(H))^dual (x) O(H)
quotientBundle = method()
quotientBundle K3Surface := CoherentSheaf => K -> cachedBundle(K, "Q", () -> (
        S := K#"ring";
        sheaf coker map(S^{numgens S : 1}, S^1, transpose vars S)
        ))

-- E_2, the kernel of sl(V) (x) O -> V (x) O(H), phi |-> phi(x), V = H^0(O(H)).  It is the sheaf with
-- T_O T_{O(H)}(O[1]) = E_2[1]; rank n^2 - n - 1.
tracelessKernelBundle = method()
tracelessKernelBundle K3Surface := CoherentSheaf => K -> cachedBundle(K, "E_2", () -> (
        S := K#"ring";
        n := numgens S;
        unit := (i, j) -> matrix table(n, n, (a, b) -> if (a, b) == (i, j) then 1_S else 0_S);
        basisMatrices := flatten apply(n, i -> apply(n, j ->
                if i != j then unit(i, j) else if i < n - 1 then unit(i, i) - unit(n - 1, n - 1) else null));
        basisMatrices = select(basisMatrices, m -> m =!= null);
        cols := apply(basisMatrices, m -> m * transpose vars S);
        sheaf kernel map(S^{n : 1}, S^(#cols), fold((a, b) -> a | b, cols))
        ))

-- M_2H, the kernel of H^0(O(2H)) (x) O -> O(2H); T_O(O(2H)) = M_2H[1]
quadricKernelBundle = method()
quadricKernelBundle K3Surface := CoherentSheaf => K -> cachedBundle(K, "M_2H", () -> (
        S := K#"ring";
        B := basis(2, S);
        sheaf kernel map(S^{2}, S^(numColumns B), entries B)
        ))

-- On the surface with the special quadric (d = 3): the cokernel of the 4 x 4 matrix A of linear forms
-- with A^2 = (x_0 x_1 + x_2 x_3 + x_4^2) Id.  A rank 2 bundle with four sections, class (2, 1, 2).
mukaiBundle = method()
mukaiBundle K3Surface := CoherentSheaf => K -> (
    if not K#"specialQuadric" then error "expected a surface built with SpecialQuadric => true";
    cachedBundle(K, "U", () -> (
            S := K#"ring";
            x := gens S;
            A := matrix {
                {x#4, 0, x#0, x#2},
                {0, x#4, -x#3, x#1},
                {x#1, -x#2, -x#4, 0},
                {x#3, x#0, 0, -x#4}};
            sheaf coker map(S^4, S^{4 : -1}, A)
            ))
    )
