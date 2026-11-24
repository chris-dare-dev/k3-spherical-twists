-- Exact quartic data uses sparse terms {exponents, coefficient} in four ordered coordinates.
-- The data can cross the JSON boundary without evaluating Macaulay2 source.

normalizeQuarticPolynomial = (terms, degree, p) -> (
    if not instance(terms, List) or #terms == 0 then error "expected a nonzero homogeneous polynomial as a list of terms";
    validateTerm := term -> (
        if not instance(term, List) or #term != 2 then error "expected a term {exponents, coefficient}";
        e := term#0;
        c := term#1;
        if not instance(e, List) or #e != 4 or not all(e, i -> instance(i, ZZ) and i >= 0)
            or sum e != degree then error("expected four exponents of total degree " | toString degree);
        if not instance(c, ZZ) or c % p == 0 then error "expected a nonzero integer coefficient modulo the characteristic";
        {e, c % p}
        );
    normalized := sort apply(terms, validateTerm);
    if #unique apply(normalized, first) != #normalized then error "duplicate exponents in a polynomial";
    normalized
    )

normalizeQuarticGenerators = (generators, degrees, p) -> (
    if not instance(generators, List) or #generators != #degrees then error "wrong number of marking generators";
    apply(generators, degrees, (terms, d) -> normalizeQuarticPolynomial(terms, d, p))
    )

normalizeQuarticData = (model, p, curveDegree) -> (
    if not instance(model, HashTable) or sort keys model =!= {"curve", "equation", "point"} then
        error "a marked quartic model requires equation, curve and point data";
    hashTable {
        "equation" => normalizeQuarticPolynomial(model#"equation", 4, p),
        "curve" => normalizeQuarticGenerators(model#"curve", {1, curveDegree}, p),
        "point" => normalizeQuarticGenerators(model#"point", {1, 1, 1}, p)
        }
    )

quarticPolynomialData = (f, p) ->
    sort apply(listForm f, (exponents, coefficient) -> {exponents, lift(coefficient, ZZ) % p})

quarticGeneratorsData = (I, p) -> (
    generators := sort(flatten entries gens trim I, f -> first degree f);
    apply(generators, f -> quarticPolynomialData(f, p))
    )

quarticPolynomial = (R, terms) -> (
    x := gens R;
    sum apply(terms, t -> (sub(t#1, R)) * product apply(x, t#0, (z, i) -> z^i))
    )
