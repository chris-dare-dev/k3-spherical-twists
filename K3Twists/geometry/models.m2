-- A K3 surface of degree 2d in P^(d+1), d = 2, 3 or 4, as a complete intersection through the
-- point x = (1:0:...:0): a quartic, a quadric and a cubic, three quadrics.

K3Surface = new Type of HashTable
K3Surface.synonym = "K3 surface"
protect symbol k3Model

-- With SpecialQuadric => true and d = 3 the quadric has a matrix factorisation
-- for the rank two bundle of mukaiBundle.
completeIntersectionEquations = recipe -> (
    params := recipe#"parameters";
    d := params#"d";
    degs := recipe#"degrees";
    kk := recipe#"field";
    x := getSymbol "x";
    N := d + 1;
    R := kk(monoid[x_0..x_N]);
    setRandomSeed params#"seed";
    atPoint := apply(gens R, v -> if v == R_0 then v => 1_kk else v => 0_kk);
    eqs := apply(degs, e -> (g := random(e, R); g - sub(g, atPoint) * R_0^e));
    if params#"special_quadric" then eqs = {R_0 * R_1 + R_2 * R_3 + R_4^2, eqs#1};
    (eqs, ideal drop(gens R, 1), null)
    )

assembleK3Surface = (recipe, eqs, point, curve) -> (
    params := recipe#"parameters";
    d := params#"d";
    degs := recipe#"degrees";
    kk := recipe#"field";
    marked := markedQuarticDegrees#?(recipe#"family");
    I := ideal eqs;
    R := ring I;
    if codim I != #degs then error "the equations are not a complete intersection";
    if dim(I + minors(#degs, jacobian I)) != 0 then error "the surface is singular";
    if marked then validateMarkedQuartic(I, point, curve, markedQuarticDegrees#(recipe#"family"));
    if not marked and (ring point =!= R or codim point != numgens R - 1
        or degree(R/point) != 1 or not isSubset(I, point)) then
        error "the marked point must be a rational point on the surface";
    if params#"special_quadric" and eqs#0 =!= R_0 * R_1 + R_2 * R_3 + R_4^2 then
        error "the saved special quadric has different equations";
    S := R / I;
    X := Proj S;
    point = sub(point, S);
    markings := hashTable {"point" => point};
    if marked then markings = merge(markings, hashTable {"curve" => sub(curve, S)}, (a, b) -> b);
    h2 := degree X;
    c := if marked then markedQuarticDegrees#(recipe#"family") else null;
    L := if marked then markedDivisorLattice(kk, {"H", "C"}, matrix {{h2, c}, {c, -2}})
        else markedDivisorLattice(kk, {"H"}, matrix {{h2}});
    H := divisorClass(L, if marked then {1, 0} else {1});
    X.cache#(symbol k3Model) = H;
    new K3Surface from {
        "recipe" => recipe,
        "field" => kk,
        "equations" => eqs,
        "coordinates" => gens R,
        "grading" => degrees R,
        "polarization" => H,
        "lattice" => L,
        "markedIdeals" => markings,
        "d" => d,
        "n" => d + 2,
        "degrees" => degs,
        "ring" => S,
        "variety" => X,
        "point" => point,
        "specialQuadric" => params#"special_quadric",
        "seed" => params#"seed",
        "characteristic" => params#"characteristic",
        cache => new CacheTable
        }
    )

realizeK3Surface = method()
realizeK3Surface K3FamilyRecipe := K3Surface => recipe -> (
    (eqs, point, curve) := if markedQuarticDegrees#?(recipe#"family") then markedQuarticEquations recipe
        else completeIntersectionEquations recipe;
    assembleK3Surface(recipe, eqs, point, curve)
    )

k3Surface = method(Options => {Characteristic => 32003, Seed => 1, SpecialQuadric => false})
k3Surface ZZ := K3Surface => opts -> d -> realizeK3Surface k3Recipe hashTable {
    "d" => d, "characteristic" => opts.Characteristic, "seed" => opts.Seed, "special_quadric" => opts.SpecialQuadric
    }

net K3Surface := K -> net concatenate(
    "K3 surface of degree ", toString(2 * K#"d"), " in P^", toString(K#"d" + 1),
    if K#"recipe"#"family" === "complete_intersection" then
        ", complete intersection of degrees " | toString K#"degrees"
    else ", marked quartic with a " | (if K#"recipe"#"family" === "quartic_with_line" then "line" else "conic"),
    " over ZZ/", toString K#"characteristic", " (seed ", toString K#"seed", ")",
    if K#"specialQuadric" then ", special quadric" else "")

-- the value of f(), computed once per surface
cached = (K, key, f) -> (
    if not K.cache#?key then K.cache#key = f();
    K.cache#key
    )
