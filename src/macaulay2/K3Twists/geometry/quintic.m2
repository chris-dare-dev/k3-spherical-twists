-- A single smooth quintic threefold and a rational point on it.

QuinticThreefold = new Type of VarietyModel
QuinticThreefold.synonym = "marked quintic threefold"
protect symbol quinticModelIdentity

quinticThreefold = () -> (
    k := ZZ/101;
    x := getSymbol "x";
    A := k(monoid[x_0..x_4]);
    F := sum apply(gens A, x -> x^5);
    I := ideal F;
    if dim(A/I) != 4 or dim(I + minors(1, jacobian I)) != 0 then error "expected a smooth quintic threefold";
    J := ideal(A_0 + A_1, A_2, A_3, A_4);
    if not isSubset(I, J) or dim(A/J) != 1 or degree(A/J) != 1 then
        error "expected a rational point on the quintic";
    R := A/I;
    X := Proj R;
    new QuinticThreefold from {
        symbol quinticModelIdentity => new MutableHashTable,
        "field" => k, "ring" => R, "variety" => X, "equations" => {F}, "point" => sub(J,R),
        "distinguishedObjects" => {"O", "O_x", "I_x"},
        "geometryEvidence" => hashTable {
            "family" => "Fermat quintic", "characteristic" => 101, "smooth" => true,
            "canonicalBundle" => "trivial by adjunction", "canonicalDegree" => 5-numgens A, "serreShift" => 3,
            "pointCoordinates" => {1,-1,0,0,0}},
        "capabilities" => hashTable {
            "numerical" => "Euler subgroup spanned by the structure and point sheaves",
            "cohomology" => "degree-indexed projective sheaf cohomology",
            "ext" => "structure source and marked point to structure via Serre duality",
            "spherical" => "the structure sheaf and its shifts",
            "realization" => "one forward structure twist of the marked point"},
        cache => new CacheTable
        }
    )
net QuinticThreefold := K -> net "smooth Fermat quintic threefold over ZZ/101 with a marked rational point"
