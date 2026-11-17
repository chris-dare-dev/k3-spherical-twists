-- Mukai vectors on a marked K3 lattice and the rank-one study's list interface.

MukaiClass = new Type of HashTable
MukaiClass.synonym = "Mukai class"

mukaiClass = method()
mukaiClass(ZZ, DivisorClass, ZZ) := MukaiClass => (r, c, s) ->
    new MukaiClass from {"rank" => r, "divisor" => c, "eulerComponent" => s}

-- <v, w> = 2d c c' - r s' - r' s; chi(E, F) = -<v(E), v(F)>
mukaiPairing = method()
mukaiPairing(ZZ, List, List) := ZZ => (d, v, w) -> 2 * d * v#1 * w#1 - v#0 * w#2 - v#2 * w#0
mukaiPairing(MukaiClass, MukaiClass) := ZZ => (v, w) -> (
    divisorPairing(v#"divisor", w#"divisor") - v#"rank" * w#"eulerComponent" - v#"eulerComponent" * w#"rank"
    )

-- Tensor by the line bundle of D, keeping the marked parent in all coordinates.
tensorByDivisor = method()
tensorByDivisor(MukaiClass, DivisorClass) := MukaiClass => (v, D) -> (
    c := v#"divisor";
    L := requireSameLattice(c, D);
    r := v#"rank";
    coords := apply(c#"coordinates", D#"coordinates", (a, b) -> a + r * b);
    s := v#"eulerComponent" + divisorPairing(c, D) + r * (divisorPairing(D, D) // 2);
    mukaiClass(r, divisorClass(L, coords), s)
    )

-- the class of E(tH)
twistVector = method()
twistVector(ZZ, List, ZZ) := List => (d, v, t) -> {v#0, v#1 + v#0 * t, v#2 + 2 * d * v#1 * t + d * v#0 * t^2}

-- the class of the dual of a locally free sheaf
dualVector = method()
dualVector List := List => v -> {v#0, -v#1, v#2}
dualVector MukaiClass := MukaiClass => v -> (
    c := v#"divisor";
    mukaiClass(v#"rank", divisorClass(c#"lattice", apply(c#"coordinates", a -> -a)), v#"eulerComponent")
    )

-- c_(-1) = c_0 = 1, c_(k+1) = n c_k - c_(k-1)
chainNumber = method()
chainNumber(ZZ, ZZ) := ZZ => (n, k) -> (
    if k < -1 then error "expected k >= -1";
    (a, b) := (1, 1);
    for j from 1 to k do (a, b) = (b, n * b - a);
    b
    )
