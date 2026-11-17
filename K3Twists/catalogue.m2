-- The sheaves of the study with their classes, and the Ext groups between two of them.

protect symbol catalogueMetadata

twistName = (name, t) -> name | (if t == 0 then "" else "(" | toString t | "H)")

-- A list of {name, class, locally free, constructor}.  Nothing is built until a constructor is called.
catalogueSpecs = K -> (
    d := K#"d";
    n := K#"n";
    X := K#"variety";
    tw := (name, F, v, lf, ts) -> apply(ts, t -> {twistName(name, t), twistVector(d, v, t), lf, () -> (F())(t)});
    dualOf := (name, F) -> () -> cached(K, name, () -> dual F());
    out := tw("O", () -> OO_X^1, {1, 0, 1}, true, {-2, -1, 0, 1, 2, 3})
        | tw("I_x", () -> pointIdealSheaf K, {1, 0, 0}, false, {-1, 0, 1, 2})
        | {{"O_x", {0, 0, 1}, false, () -> pointSheaf K}}
        | tw("M_H", () -> kernelBundle K, {n - 1, -1, 1}, true, {0, 1})
        | tw("M_H^dual", dualOf("M_H^dual", () -> kernelBundle K), {n - 1, 1, 1}, true, {0, 1})
        | tw("M_x", () -> pointKernelBundle K, {n - 2, -1, 1}, true, {0, 1})
        | tw("M_x^dual", dualOf("M_x^dual", () -> pointKernelBundle K), {n - 2, 1, 1}, true, {0})
        | tw("E_2", () -> tracelessKernelBundle K, {n^2 - n - 1, -n, n - 1}, true, {0, 1})
        | tw("M_2H", () -> quadricKernelBundle K, {4 * d + 1, -2, 1}, true, {0, 1});
    if K#"specialQuadric" then out = out
        | tw("U", () -> mukaiBundle K, {2, 1, 2}, true, {-1, 0})
        | tw("U^dual", dualOf("U^dual", () -> mukaiBundle K), {2, -1, 2}, true, {0, 1});
    out
    )

-- {name, class, locally free} for every sheaf of the catalogue; no sheaf is built
catalogueClasses = method()
catalogueClasses K3Surface := List => K -> apply(catalogueSpecs K, s -> take(s, 3))

realizeCatalogueEntry = spec -> (
    (name, v, locallyFree, constructor) := toSequence spec;
    F := constructor();
    F.cache#(symbol catalogueMetadata, name) = {v, locallyFree};
    F.cache#(symbol localFreeness) = locallyFree;
    {name, F, v, locallyFree}
    )

-- {name, sheaf, class, locally free} for one sheaf of the catalogue
catalogueEntry = method()
catalogueEntry(K3Surface, String) := List => (K, name) -> (
    found := select(catalogueSpecs K, s -> s#0 == name);
    if #found == 0 then error("no sheaf named " | name | " in the catalogue");
    realizeCatalogueEntry first found
    )

-- {name, sheaf, class, locally free} for every sheaf of the catalogue
catalogue = method()
catalogue K3Surface := List => K -> apply(catalogueSpecs K, realizeCatalogueEntry)

-- How Ext^i(E, F) is computed for two entries or two rows of catalogueClasses: as the cohomology of
-- the sheaf Hom(E, F) when E is locally free, by Serre duality when only F is, and not at all when
-- neither is.  Of two locally free sheaves the one of smaller rank is the source of the Hom sheaf.
extMethod = (lfE, rankE, lfF, rankF) -> (
    if lfE and (not lfF or rankE <= rankF) then "Hom sheaf"
    else if lfF then "Serre duality"
    else "not computed"
    )

checkCatalogueEntry = a -> (
    if #a != 4 or not instance(a#0, String) or not instance(a#1, CoherentSheaf) then
        error "extTableRow expects entries from catalogue or catalogueEntry";
    evidence := (symbol catalogueMetadata, a#0);
    F := a#1;
    if not F.cache#?evidence or F.cache#evidence =!= {a#2, a#3} then
        error "extTableRow requires catalogue class and local-freeness metadata"
    )

catalogueExtRow = (a, b, expectedHalfDegree) -> (
    scan({a, b}, checkCatalogueEntry);
    X := commonExtVariety(a#1, b#1);
    if not X.cache#?(symbol k3Model) then
        error "extTableRow requires a surface constructed by k3Surface";
    d := (degree X) // 2;
    if expectedHalfDegree =!= null and expectedHalfDegree != d then
        error "extTableRow degree does not match the catalogue surface";
    chi := -mukaiPairing(d, a#2, b#2);
    how := extMethod(a#3, a#2#0, b#3, b#2#0);
    dims := if how == "Hom sheaf" then extViaHom(a#1, b#1)
        else if how == "Serre duality" then reverse extViaHom(b#1, a#1)
        else null;
    {a#0, b#0, dims, chi, how}
    )

-- One row of the table of Ext groups: {name of E, name of F, dimensions or null, chi predicted, method}.
extTableRow = method()
extTableRow(List, List) := List => (a, b) -> catalogueExtRow(a, b, null)
extTableRow(ZZ, List, List) := List => (d, a, b) -> catalogueExtRow(a, b, d)
extTableRow(K3Surface, String, String) := List => (K, nameE, nameF) ->
    extTableRow(catalogueEntry(K, nameE), catalogueEntry(K, nameF))
