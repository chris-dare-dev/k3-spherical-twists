-- Degree-indexed invariants use the cohomological convention H^i(E[a]) = H^(i+a)(E).

DegreeObservation = new Type of HashTable

observationBase = (kind, subjects) -> hashTable {
    "quantity" => kind,
    "subjects" => subjects,
    "convention" => "cohomological"
    }

unsupportedObservation = (kind, subjects, reason) -> new DegreeObservation from merge(
    observationBase(kind, subjects), hashTable {
        "status" => "unsupported", "method" => null, "support" => null,
        "dimensions" => hashTable {}, "complete" => false, "reason" => reason
        }, (a, b) -> b)

requireDegrees = requested -> (
    if requested =!= null and (not instance(requested, List) or not all(requested, i -> instance(i, ZZ))) then
        error "Degrees must be a list of integers"
    )

measureDegrees = (kind, subjects, methodName, support, requested, dimensionAt) -> (
    requireDegrees requested;
    domain := toList (support#0 .. support#1);
    measured := if requested === null then domain else select(sort unique requested, i -> member(i, domain));
    dimensions := hashTable apply(measured, i -> i => dimensionAt i);
    new DegreeObservation from merge(observationBase(kind, subjects), hashTable {
        "status" => "measured", "method" => methodName, "support" => support,
        "dimensions" => dimensions, "complete" => #measured == #domain, "reason" => null
        }, (a, b) -> b)
    )

degreeStatus = method()
degreeStatus(DegreeObservation, ZZ) := String => (obs, i) -> (
    if obs#"status" === "unsupported" then "unsupported"
    else if obs#"dimensions"#?i then "measured"
    else if i < obs#"support"#0 or i > obs#"support"#1 then "zero"
    else "uncomputed"
    )

observedDimension = method()
observedDimension(DegreeObservation, ZZ) := (obs, i) -> (
    status := degreeStatus(obs, i);
    if status === "measured" then obs#"dimensions"#i
    else if status === "zero" then 0 else null
    )

-- Realize the catalogue and multiples of the known polarization. Other references are symbolic.
observationSheaf = E -> (
    if not E#?"definition" then return null;
    K := E#"surface";
    desc := E#"definition";
    if desc#"kind" === "catalogue" then return (catalogueEntry(K, desc#"name"))#1;
    if desc#"kind" =!= "line_bundle" then return null;
    H := K#"polarization"#"coordinates";
    D := desc#"coordinates";
    index := position(H, h -> h != 0);
    t := D#index // H#index;
    if D =!= apply(H, h -> t * h) then return null;
    X := K#"variety";
    (OO_X^1)(t)
    )

observationTerm = E -> (
    if instance(E, ShiftedK3Object) then (observationSheaf E#"object", E#"shift")
    else (observationSheaf E, 0)
    )

observeCohomology = (subject, F, shift, requested) -> (
    requireDegrees requested;
    if F === null then return unsupportedObservation("cohomology", {subject}, "reference has no supported sheaf realization");
    if not instance(variety F, ProjectiveVariety) then
        return unsupportedObservation("cohomology", {subject}, "requires a projective sheaf");
    bound := dim variety F;
    measureDegrees("cohomology", {subject}, "sheaf cohomology", {-shift, bound - shift},
        requested, i -> rank HH^(i + shift)(F))
    )

cohomologyObservation = method(Options => {Degrees => null})
cohomologyObservation CoherentSheaf := DegreeObservation => opts -> F -> observeCohomology(F, F, 0, opts.Degrees)
cohomologyObservation K3ObjectReference := DegreeObservation => opts -> E -> (
    (F, shift) := observationTerm E;
    observeCohomology(E, F, shift, opts.Degrees)
    )

observeExt = (subjects, E, F, offset, requested) -> (
    requireDegrees requested;
    if E === null or F === null then
        return unsupportedObservation("ext", subjects, "reference has no supported sheaf realization");
    X := commonExtVariety(E, F);
    if not X.cache#?(symbol k3Model) then
        return unsupportedObservation("ext", subjects, "requires a certified smooth K3 model");
    measureDegrees("ext", subjects, "direct Ext", {offset, offset + dim X},
        requested, i -> rank Ext^(i - offset)(E, F))
    )

extObservation = method(Options => {Degrees => null})
extObservation(CoherentSheaf, CoherentSheaf) := DegreeObservation => opts -> (E, F) ->
    observeExt({E, F}, E, F, 0, opts.Degrees)
extObservation(K3ObjectReference, K3ObjectReference) := DegreeObservation => opts -> (A, B) -> (
    requireObjectModel(A#"surface", B#"surface");
    (E, a) := observationTerm A;
    (F, b) := observationTerm B;
    observeExt({A, B}, E, F, a - b, opts.Degrees)
    )
