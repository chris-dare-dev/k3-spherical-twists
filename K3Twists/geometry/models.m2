-- A K3 surface of degree 2d in P^(d+1), d = 2, 3 or 4, as a complete intersection through the
-- point x = (1:0:...:0): a quartic, a quadric and a cubic, three quadrics.

K3Surface = new Type of HashTable
K3Surface.synonym = "K3 surface"
protect symbol k3Model

-- With SpecialQuadric => true and d = 3 the quadric is x_0 x_1 + x_2 x_3 + x_4^2, which has an explicit
-- matrix factorisation. The surface carries the rank 2 bundle of mukaiBundle.
realizeK3Surface = method()
realizeK3Surface K3FamilyRecipe := K3Surface => recipe -> (
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
    I := ideal eqs;
    if codim I != #degs then error "the random forms are not a complete intersection; change the seed";
    if dim(I + minors(#degs, jacobian I)) != 0 then error "the surface is singular; change the seed";
    S := R / I;
    X := Proj S;
    point := ideal drop(gens S, 1);
    L := markedDivisorLattice(kk, {"H"}, matrix {{degree X}});
    H := divisorClass(L, {1});
    X.cache#(symbol k3Model) = H;
    new K3Surface from {
        "recipe" => recipe,
        "field" => kk,
        "equations" => eqs,
        "coordinates" => gens R,
        "grading" => degrees R,
        "polarization" => H,
        "lattice" => L,
        "markedIdeals" => hashTable {"point" => point},
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

k3Surface = method(Options => {Characteristic => 32003, Seed => 1, SpecialQuadric => false})
k3Surface ZZ := K3Surface => opts -> d -> realizeK3Surface k3Recipe hashTable {
    "d" => d, "characteristic" => opts.Characteristic, "seed" => opts.Seed, "special_quadric" => opts.SpecialQuadric
    }

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
