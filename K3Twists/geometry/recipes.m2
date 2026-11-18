-- Recipes validate the family parameters before generating any equations.

K3FamilyRecipe = new Type of HashTable
K3FamilyRecipe.synonym = "K3 family recipe"

completeIntersectionDegrees = hashTable {2 => {4}, 3 => {2, 3}, 4 => {2, 2, 2}};
markedQuarticDegrees = hashTable {"quartic_with_line" => 1, "quartic_with_conic" => 2};

k3Families = () -> prepend("complete_intersection", sort keys markedQuarticDegrees)

recipeOption = (spec, key, default) ->
    if spec#?key and spec#key =!= null then spec#key else default

k3Recipe = method()
k3Recipe HashTable := K3FamilyRecipe => spec -> (
    family := if spec#?"family" then spec#"family" else "complete_intersection";
    if not member(family, k3Families()) then error("unknown K3 surface family " | toString family);
    marked := markedQuarticDegrees#?family;
    allowed := {"family", "d", "characteristic", "seed", "special_quadric"};
    if marked then allowed = append(allowed, "model");
    scan(keys spec, key -> if not member(key, allowed)
        then error("unknown K3 surface parameter " | toString key));
    d := if spec#?"d" then spec#"d" else if marked then 2 else null;
    if not instance(d, ZZ) or not completeIntersectionDegrees#?d then error "expected d = 2, 3 or 4";
    if marked and d != 2 then error "a marked quartic requires d = 2";
    p := recipeOption(spec, "characteristic", 32003);
    if not instance(p, ZZ) or p <= 0 or not isPrime p then
        error "k3Surface requires a positive prime characteristic";
    seed := recipeOption(spec, "seed", 1);
    if not instance(seed, ZZ) then error "K3 surface seed must be an integer";
    special := recipeOption(spec, "special_quadric", false);
    if not instance(special, Boolean) then error "special_quadric must be a Boolean";
    if special and d != 3 then error "SpecialQuadric is for d = 3";
    params := hashTable {"d" => d, "seed" => seed, "characteristic" => p, "special_quadric" => special};
    if marked then (
        params = merge(params, hashTable {"family" => family}, (a, b) -> b);
        if recipeOption(spec, "model", null) =!= null then
            params = merge(params, hashTable {
                    "model" => normalizeQuarticData(spec#"model", p, markedQuarticDegrees#family)
                    }, (a, b) -> b);
        );
    new K3FamilyRecipe from {
        "family" => family, "parameters" => params, "field" => ZZ/p,
        "degrees" => completeIntersectionDegrees#d
        }
    )

-- Keep the rank-one study's wire representation stable.
normalizeK3SurfaceSpec = spec -> (k3Recipe spec)#"parameters"
