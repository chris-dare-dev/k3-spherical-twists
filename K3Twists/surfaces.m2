-- A K3 surface of degree 2d in P^(d+1), d = 2, 3 or 4, as a complete intersection through the
-- point x = (1:0:...:0): a quartic, a quadric and a cubic, three quadrics.

K3Surface = new Type of HashTable
K3Surface.synonym = "K3 surface"

completeIntersectionDegrees = new HashTable from {2 => {4}, 3 => {2, 3}, 4 => {2, 2, 2}};

-- With SpecialQuadric => true and d = 3 the quadric is x_0 x_1 + x_2 x_3 + x_4^2, which has an explicit
-- matrix factorisation; the surface then carries the rank 2 bundle of mukaiBundle.
k3Surface = method(Options => {Characteristic => 32003, Seed => 1, SpecialQuadric => false})
k3Surface ZZ := K3Surface => opts -> d -> (
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
    new K3Surface from {
        "d" => d,
        "n" => d + 2,
        "degrees" => degs,
        "ring" => S,
        "variety" => Proj S,
        "point" => ideal drop(gens S, 1),
        "specialQuadric" => opts.SpecialQuadric,
        "seed" => opts.Seed,
        "characteristic" => opts.Characteristic,
        cache => new CacheTable
        }
    )

net K3Surface := K -> net concatenate(
    "K3 surface of degree ", toString(2 * K#"d"), " in P^", toString(K#"d" + 1),
    ", complete intersection of degrees ", toString K#"degrees",
    " over ZZ/", toString K#"characteristic", " (seed ", toString K#"seed", ")",
    if K#"specialQuadric" then ", special quadric" else "")

-- the value of f(), computed once per surface
cached = (K, key, f) -> (
    if not K.cache#?key then K.cache#key = f();
    K.cache#key
    )
