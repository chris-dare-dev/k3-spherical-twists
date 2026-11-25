-- Part 203 in the ordered regular parameters u,v. Internal grading shifts
-- make every map degree zero; after forgetting the grading these are jets.
-- Keep the input, output differential and both sides of each comparison.
arrowMatrixRows = m -> apply(entries m, row -> apply(row, toExternalString))

arrowComponents = f -> (
    (lo, hi) := concentration source f;
    for i from lo to hi list {i, arrowMatrixRows f_i}
    )

arrowModel = C -> (
    (lo, hi) := concentration C;
    hashTable {"terms" => for i from lo to hi list (
        d := presentation C_i;
        {i, artifactBasis target d, artifactBasis source d, arrowMatrixRows d}
        ), "differential" => arrowComponents C.dd}
    )

-- Identify the cone of the inclusion with the proposed lower object.
cutQuotientMap = (cut, p) -> (
    if p*cut != 0 then error "lower projection does not kill the supplied cut";
    L := target p;
    U := source cut;
    map(L, cone cut, i -> map(L_i, U_(i-1), 0) | p_i)
    )

cutSquareEvidence = (f, cut, reference, s, t, p, quotientMap) -> hashTable {
    "input_source" => arrowModel source f, "input_target" => arrowModel target f,
    "output" => arrowModel target cut, "upper" => arrowModel source cut,
    "reference_source" => arrowModel source reference, "reference_target" => arrowModel target reference,
    "input_map" => arrowComponents f, "cut" => arrowComponents cut, "reference" => arrowComponents reference,
    "source_identification" => arrowComponents s, "output_identification" => arrowComponents t,
    "lower" => arrowModel target p, "lower_projection" => arrowComponents p,
    "quotient_identification" => arrowComponents quotientMap
    }

jetConeCheck = (R, u, v, split) -> (
    k := R^1/ideal(u,v);
    soc := k ** R^{-1};
    D := R^1/ideal(v,u^2);
    -- [k --u--> D] resolves k[-1]. The identity on its top k is a roof
    -- for the tangent extension. The second target summand is unmapped.
    A := complex(map(D, soc, {{u}}), Base => -1);
    B := (complex soc) ++ complex(k, Base => -1);
    f := map(B, A, hashTable {0 => if split then 0*id_soc else id_soc});
    C := cone f;
    cut := signedCutInclusion(C, f, 1, 0);
    middle := if split then k ++ soc else D;
    -- C_0 = D + k. Its relation from degree one is (-u,0) or (-u,1).
    -- Quotienting by it identifies the whole output, including its low term.
    quotient := if split then map(middle, C_0, {{1,0},{0,1}}) else map(middle, C_0, {{1,u}});
    U := complex middle;
    lower := complex(k, Base => -1);
    model := U ++ lower;
    t := map(model, C, hashTable {0 => quotient, -1 => id_k});
    p := map(lower, C, hashTable {-1 => id_k});
    quotientMap := cutQuotientMap(cut, p);
    ref := map(model, U, hashTable {0 => id_middle});
    s := map(U, source cut, hashTable {0 => quotient * inducedMap(C_0, (source cut)_0)});
    -- The cone on upper inputs alone supplies only the original target copy.
    naive := map(C, complex soc, hashTable {0 => map(C_0, soc, {{0},{1}})});
    upper := HH_0 source cut;
    value := hashTable {
        "arrow" => certifiesCutSquare(cut, ref, s, t),
        "quotient" => acyclicCone quotientMap,
        "zero_rejected" => not certifiesCutSquare(cut, 0*ref, s, t),
        "upper_length" => length upper, "lower_length" => length HH_(-1) cone cut,
        "uncorrected_defect" => length coker homology(0, naive),
        "radical_length" => length(ideal(u,v)*upper)
        };
    (value, cutSquareEvidence(f, cut, ref, s, t, p, quotientMap))
    )

jetFibreCheck = (R, u, v, firstU, secondU) -> (
    k := R^1/ideal(u,v);
    soc := k ** R^{-1};
    jet := (a,b) -> R^1/ideal(b,a^2);
    (a,A) := if firstU then (u,jet(u,v)) else (v,jet(v,u));
    (b,B) := if secondU then (u,jet(u,v)) else (v,jet(v,u));
    B = B ** R^{1};
    f := map(complex B, complex A, hashTable {0 => map(B,A,{{b}})});
    Y := (cone f)[1];
    cut := signedCutInclusion(Y, f, -1, 0);
    inc := map(Y_0, soc, {{a}});
    ref := map(Y, complex soc, hashTable {0 => inc});
    s := map(source cut, source ref, hashTable {0 => inc // cut_0});
    residue := k ** R^{1};
    p := map(complex(residue, Base => -1), Y, hashTable {-1 => map(residue, B, {{1}})});
    quotientMap := cutQuotientMap(cut, p);
    -- Lift the first Koszul differential through the actual splice -d_Y.
    -- d2=(-v,u)^t fixes the orientation. Its lift lands in the marked socle.
    lift0 := map(Y_(-1), R^{1}, {{1}});
    d1 := map(R^{1}, R^2, {{u,v}});
    d2 := map(R^2, R^{-1}, {{-v},{u}});
    middle := -Y.dd_0;
    lift1 := (lift0*d1) // middle;
    obstruction := (lift1*d2) // inc;
    if p_(-1)*lift0 != map(residue, R^{1}, {{1}}) or d1*d2 != 0
        or middle*lift1 != lift0*d1 or inc*obstruction != lift1*d2 then
        error "invalid lift through the fibre splice";
    coefficient := lift(obstruction_(0,0), ZZ);
    value := hashTable {
        "arrow" => certifiesCutSquare(ref, cut, s, id_Y),
        "quotient" => acyclicCone quotientMap,
        "zero_rejected" => not certifiesCutSquare(0*ref, cut, s, id_Y),
        "upper_length" => length HH_0 source cut, "lower_length" => length HH_(-1) cone cut,
        "uncorrected_defect" => length HH_(-1) Y, "yoneda" => coefficient
        };
    evidence := merge(cutSquareEvidence(f, cut, ref, s, id_Y, p, quotientMap),
        hashTable {"koszul_lift" => arrowMatrixRows lift1}, (x,y) -> y);
    (value, evidence)
    )

pointTwistCutCheck = (K, forward) -> (
    S := sphericalObject structureObject K;
    P := catalogueObject(K, "O_x");
    I := module pointIdealSheaf K;
    input := if forward then P else shiftObject(catalogueObject(K, "I_x"), 1);
    direction := if forward then 1 else -1;
    realized := realizeTwistImage(twistWord {twistStep(S, direction)}, input);
    C := realized#"complex";
    f := realized#"chainMap";
    cut := signedCutInclusion(C, f, direction, 1);
    zeroSource := complex((ring C)^0, Base => 1);
    emptyCut := map(C, zeroSource, 0);
    reference := if forward then map(C, complex(I, Base => 1),
        hashTable {1 => inducedMap(C_1, I)}) else emptyCut;
    s := if forward then map(source cut, source reference, hashTable {1 => reference_1 // cut_1})
        else map(source cut, zeroSource, 0);
    -- The cut on inputs alone gives zero for evaluation and the whole fibre
    -- for coevaluation. Each fails the comparison over the very same C.
    naive := if forward then emptyCut else id_C;
    R := K#"ring";
    Opoint := module pointSheaf K;
    p := if forward then map(zeroSource, C, 0)
        else map(complex Opoint, C, hashTable {0 => map(Opoint,C_0,{{1_R}})});
    quotientMap := cutQuotientMap(cut, p);
    identified := if forward then f_0 == map(Opoint, R^1, {{1_R}})
        else f_1 == inducedMap(R^1,I) and p == realized#"projection" and acyclicCone p;
    if not all({f, cut, reference, s, p, quotientMap}, isHomogeneous) then error "expected graded quartic maps";
    value := hashTable {"arrow" => certifiesCutSquare(reference, cut, s, id_C),
        "quotient" => acyclicCone quotientMap,
        "uncorrected_rejected" => not certifiesCutSquare(cut, naive, map(source naive, source cut, 0), id_C),
        "cut_is_iso" => acyclicCone cut, "cut_is_zero" => acyclicCone map(source cut, zeroSource, 0),
        "twist_map_identified" => identified};
    (value, cutSquareEvidence(f, cut, reference, s, id_C, p, quotientMap))
    )

jetArrowCases = {"cone-split","cone-u","fibre-uu","fibre-uv","fibre-vu","fibre-vv"}
pointArrowCases = {"point-forward","ideal-inverse"}
arrowCaseField = ("case", s -> member(s, jetArrowCases | pointArrowCases))
arrowPredictionField = ("prediction", v -> instance(v, HashTable))

expandArrowChecks = (i, spec, surfaces) -> apply(spec#"items", item -> (
    name := item#"case";
    t := hashTable {"id" => "hn_arrow/" | name, "kind" => "hn_arrow", "case" => name, "set" => i,
        "group" => "HN arrows", "cost" => 1, "comparison" => "equals", "predicted" => item#"prediction"};
    if member(name, jetArrowCases) then return t;
    if #surfaces != 1 or surfaces#0#"d" != 2 then error "point twist checks require one quartic surface";
    merge(t, hashTable {"id" => t#"id" | "/" | surfaceLabel surfaces#0, "surface" => surfaces#0}, (x,y) -> y)
    ))

runArrowCheck = t -> (
    name := t#"case";
    punctual := member(name, jetArrowCases);
    (seconds, result) := timed(() -> (
        if not punctual then return pointTwistCutCheck(surfaceFromSpec t#"surface", name === "point-forward");
        R := QQ[local u,local v];
        if member(name, {"cone-split","cone-u"}) then jetConeCheck(R,R_0,R_1,name === "cone-split")
        else jetFibreCheck(R,R_0,R_1,substring(6,1,name) === "u",substring(7,1,name) === "u")
        ));
    (observed, maps) := result;
    window := if punctual then "At c=0 finite-length sheaves have phase 1 and their [-1] shifts have phase 0."
        else "At c=1 use the supplied membership of I_x, O and k_x in the geometric heart P((0,1]).";
    evidence := merge(maps, hashTable {"supplied_window" => window,
        "heart_operations" => if punctual then "Ordinary kernels and cokernels of finite-length modules."
            else "Use the point ideal sequence in the supplied heart and its shifted sequence in the next heart.",
        "homological_lower_bound" => if punctual then 0 else 1,
        "square_direction" => if member(name, {"cone-split","cone-u"}) then "computed to reference" else "reference to computed"},
        (x,y) -> y);
    hashTable {"value" => observed, "predicted" => t#"predicted", "agrees" => observed === t#"predicted",
        "method" => "signed window correction and a chain square over the identified output",
        "evidence" => evidence, "setup_seconds" => 0, "compute_seconds" => seconds}
    )

registerTaskKind("hn_arrow", hashTable {
    "version" => 1, "requirements" => {},
    "validate_set" => (s -> (
        checkFields(s, "HN arrow set", taskKindField | {("items", x -> instance(x,List))}, {});
        scan(s#"items", item -> checkFields(item, "HN arrow example", {arrowCaseField,arrowPredictionField}, {}))
        )),
    "validate_task" => (t -> (
        checkTaskFields(t, {arrowCaseField, ("predicted", x -> instance(x, HashTable))},
            {("surface", x -> instance(x, HashTable))});
        if member(t#"case", pointArrowCases) =!= t#?"surface" then
            error "supply a surface for the quartic cases only";
        if t#?"surface" and (checkSurfaceSpec t#"surface")#"d" != 2 then error "expected a quartic surface"
        )),
    "validate_result" => (r -> null), "expand" => expandArrowChecks, "run" => runArrowCheck
    })
