-- Invariants of the sheaves I_x, M_H, M_x and Q with the values predicted for them as formulas in n.

-- A list of {name, function computing the value, predicted value}.  The fast list uses sheaf
-- cohomology only.  The slow list computes some of the same numbers as Ext groups, together with the
-- Ext groups of three sheaves with themselves; these are practical for d = 2 only.
invariantSpecs = (K, slow) -> (
    n := K#"n";
    X := K#"variety";
    OX := OO_X^1;
    O1 := OO_X^1(1);
    Ix := () -> pointIdealSheaf K;
    Ox := () -> pointSheaf K;
    MH := () -> kernelBundle K;
    Mx := () -> pointKernelBundle K;
    Q := () -> quotientBundle K;
    out := {
        {"h^i(O)", () -> cohomologyDims OX, {1, 0, 1}},
        {"h^i(O(H))", () -> cohomologyDims O1, {n, 0, 0}},
        {"h^i(O(-H))", () -> cohomologyDims OX(-1), {0, 0, n}},
        {"h^i(I_x)", () -> cohomologyDims Ix(), {0, 0, 1}},
        {"h^i(I_x(-H))", () -> cohomologyDims (Ix())(-1), {0, 1, n}},
        {"h^i(I_x(H))", () -> cohomologyDims (Ix())(1), {chainNumber(n, 1), 0, 0}},
        {"rank M_H", () -> rank MH(), n - 1},
        {"h^i(M_H)", () -> cohomologyDims MH(), {0, 0, n}},
        {"h^i(M_H(-H))", () -> cohomologyDims (MH())(-1), {0, 1, n^2 - 1}},
        {"generators of I_x(H)", () -> numgens K#"point", n - 1},
        {"rank M_x", () -> rank Mx(), n - 2},
        {"h^i(M_x)", () -> cohomologyDims Mx(), {0, 0, chainNumber(n, 1)}},
        {"h^i(M_x(-H))", () -> cohomologyDims (Mx())(-1), {0, 0, chainNumber(n, 2)}},
        {"rank Q", () -> rank Q(), n - 1},
        {"h^i(Q)", () -> cohomologyDims Q(), {n^2 - 1, 1, 0}}
        };
    if slow then out = out | {
        {"Ext^i(O, O(H))", () -> extDims(OX, O1), {n, 0, 0}},
        {"Ext^i(O(H), O)", () -> extDims(O1, OX), {0, 0, n}},
        {"Ext^i(O(H), M_H)", () -> extDims(O1, MH()), {0, 1, n^2 - 1}},
        {"Ext^i(M_x, O_x)", () -> extDims(Mx(), Ox()), {n - 2, 0, 0}},
        {"Ext^i(I_x(H), I_x(H))", () -> extDims((Ix())(1), (Ix())(1)), {1, 2, 1}},
        {"Ext^i(M_H, M_H)", () -> extDims(MH(), MH()), {1, 0, 1}},
        {"Ext^i(M_x, M_x)", () -> extDims(Mx(), Mx()), {1, 2, 1}}
        };
    out
    )

-- the names of the invariants, in the order of sheafInvariants
sheafInvariantNames = method(Options => {Slow => false})
sheafInvariantNames K3Surface := List => opts -> K -> apply(invariantSpecs(K, opts.Slow), first)

-- {name, computed value, predicted value} for one invariant of the fast or the slow list
sheafInvariant = method()
sheafInvariant(K3Surface, String) := List => (K, name) -> (
    found := select(invariantSpecs(K, true), s -> s#0 == name);
    if #found == 0 then error("no invariant named " | name);
    s := first found;
    {s#0, (s#1)(), s#2}
    )

-- A list of {name, computed value, predicted value}; with Slow => true the slow list is appended.
sheafInvariants = method(Options => {Slow => false})
sheafInvariants K3Surface := List => opts -> K ->
    apply(invariantSpecs(K, opts.Slow), s -> {s#0, (s#1)(), s#2})
