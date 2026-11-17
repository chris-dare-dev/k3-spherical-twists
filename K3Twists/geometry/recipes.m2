-- Recipes validate the family parameters before generating any equations.

K3FamilyRecipe = new Type of HashTable
K3FamilyRecipe.synonym = "K3 family recipe"

completeIntersectionDegrees = hashTable {2 => {4}, 3 => {2, 3}, 4 => {2, 2, 2}};

k3Recipe = method()
k3Recipe HashTable := K3FamilyRecipe => spec -> (
    scan(keys spec, key -> if not member(key, {"family", "d", "characteristic", "seed", "special_quadric"})
        then error("unknown K3 surface parameter " | toString key));
    if spec#?"family" and spec#"family" =!= "complete_intersection" then
        error("unknown K3 surface family " | toString spec#"family");
    if not spec#?"d" or not instance(spec#"d", ZZ) or not completeIntersectionDegrees#?(spec#"d") then
        error "expected d = 2, 3 or 4";
    d := spec#"d";
    p := if spec#?"characteristic" then spec#"characteristic" else 32003;
    if not instance(p, ZZ) or p <= 0 or not isPrime p then
        error "k3Surface requires a positive prime characteristic";
    seed := if spec#?"seed" then spec#"seed" else 1;
    if not instance(seed, ZZ) then error "K3 surface seed must be an integer";
    special := if spec#?"special_quadric" then spec#"special_quadric" else false;
    if not instance(special, Boolean) then error "special_quadric must be a Boolean";
    if special and d != 3 then error "SpecialQuadric is for d = 3";
    new K3FamilyRecipe from {
        "family" => "complete_intersection",
        "parameters" => hashTable {"d" => d, "seed" => seed, "characteristic" => p, "special_quadric" => special},
        "field" => ZZ/p,
        "degrees" => completeIntersectionDegrees#d
        }
    )

-- Keep the rank-one study's wire representation stable.
normalizeK3SurfaceSpec = spec -> (k3Recipe spec)#"parameters"
