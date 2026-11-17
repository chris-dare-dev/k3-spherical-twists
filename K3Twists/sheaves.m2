-- Dimensions of cohomology and Ext groups, and the sheaves of the study.  Each sheaf is built once per
-- surface and kept in the surface's cache.

cohomologyDims = method()
cohomologyDims CoherentSheaf := List => F -> apply(3, i -> rank HH^i(F))

extDims = method()
extDims(CoherentSheaf, CoherentSheaf) := List => (F, G) -> apply(3, i -> rank Ext^i(F, G))

-- Ext^i(E, F) as the cohomology of the sheaf Hom(E, F); valid when E is locally free
extViaHom = method()
extViaHom(CoherentSheaf, CoherentSheaf) := List => (E, F) -> cohomologyDims sheafHom(E, F)

-- I_x, the ideal sheaf of the point
pointIdealSheaf = method()
pointIdealSheaf K3Surface := CoherentSheaf => K -> cached(K, "I_x", () -> sheaf module K#"point")

-- O_x, the skyscraper sheaf
pointSheaf = method()
pointSheaf K3Surface := CoherentSheaf => K -> cached(K, "O_x", () -> sheaf((K#"ring")^1 / K#"point"))

-- M_H, the kernel of H^0(O(H)) (x) O -> O(H)
kernelBundle = method()
kernelBundle K3Surface := CoherentSheaf => K -> cached(K, "M_H", () -> (
        S := K#"ring";
        sheaf kernel map(S^{1}, S^(numgens S), vars S)
        ))

-- M_x, the kernel of H^0(I_x(H)) (x) O -> I_x(H); the linear forms through x generate I_x(H)
pointKernelBundle = method()
pointKernelBundle K3Surface := CoherentSheaf => K -> cached(K, "M_x", () -> (sheaf kernel gens K#"point")(1))

-- Q, the cokernel of O -> H^0(O(H))^dual (x) O(H)
quotientBundle = method()
quotientBundle K3Surface := CoherentSheaf => K -> cached(K, "Q", () -> (
        S := K#"ring";
        sheaf coker map(S^{numgens S : 1}, S^1, transpose vars S)
        ))

-- E_2, the kernel of sl(V) (x) O -> V (x) O(H), phi |-> phi(x), V = H^0(O(H)).  It is the sheaf with
-- T_O T_{O(H)}(O[1]) = E_2[1]; rank n^2 - n - 1.
tracelessKernelBundle = method()
tracelessKernelBundle K3Surface := CoherentSheaf => K -> cached(K, "E_2", () -> (
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
quadricKernelBundle K3Surface := CoherentSheaf => K -> cached(K, "M_2H", () -> (
        S := K#"ring";
        B := basis(2, S);
        sheaf kernel map(S^{2}, S^(numColumns B), entries B)
        ))

-- On the surface with the special quadric (d = 3): the cokernel of the 4 x 4 matrix A of linear forms
-- with A^2 = (x_0 x_1 + x_2 x_3 + x_4^2) Id.  A rank 2 bundle with four sections, class (2, 1, 2).
mukaiBundle = method()
mukaiBundle K3Surface := CoherentSheaf => K -> (
    if not K#"specialQuadric" then error "expected a surface built with SpecialQuadric => true";
    cached(K, "U", () -> (
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
