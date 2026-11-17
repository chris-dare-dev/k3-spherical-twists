-- Classes (r, c, s) of sheaves on a K3 surface of degree 2d, where c is the multiple of H, and the
-- numbers attached to them.

-- <v, w> = 2d c c' - r s' - r' s; chi(E, F) = -<v(E), v(F)>
mukaiPairing = method()
mukaiPairing(ZZ, List, List) := ZZ => (d, v, w) -> 2 * d * v#1 * w#1 - v#0 * w#2 - v#2 * w#0

-- the class of E(tH)
twistVector = method()
twistVector(ZZ, List, ZZ) := List => (d, v, t) -> {v#0, v#1 + v#0 * t, v#2 + 2 * d * v#1 * t + d * v#0 * t^2}

-- the class of the dual of a locally free sheaf
dualVector = method()
dualVector List := List => v -> {v#0, -v#1, v#2}

-- c_(-1) = c_0 = 1, c_(k+1) = n c_k - c_(k-1)
chainNumber = method()
chainNumber(ZZ, ZZ) := ZZ => (n, k) -> (
    if k < -1 then error "expected k >= -1";
    (a, b) := (1, 1);
    for j from 1 to k do (a, b) = (b, n * b - a);
    b
    )
