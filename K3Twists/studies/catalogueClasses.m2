-- Interpret a rank-one study triple in the marked class of the polarization.
studyMukaiClass = (H, v) -> (
    c := divisorClass(H#"lattice", apply(H#"coordinates", h -> v#1 * h));
    mukaiClass(v#0, c, v#2)
    )

catalogueMukaiClass = method()
catalogueMukaiClass(K3Surface, String) := MukaiClass => (K, name) -> (
    found := select(catalogueClasses K, row -> row#0 == name);
    if #found == 0 then error("no sheaf named " | name | " in the catalogue");
    studyMukaiClass(K#"polarization", (first found)#1)
    )
