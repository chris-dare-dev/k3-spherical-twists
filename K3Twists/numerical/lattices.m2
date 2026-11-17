-- Integral intersection forms with separately identified bases.

MarkedDivisorLattice = new Type of HashTable
MarkedDivisorLattice.synonym = "marked divisor lattice"
DivisorClass = new Type of HashTable
DivisorClass.synonym = "divisor class"
protect symbol latticeIdentity

markedDivisorLattice = method()
markedDivisorLattice(Ring, List, Matrix) := MarkedDivisorLattice => (k, names, G) -> (
    if not isField k then error "expected a field of definition";
    if #names == 0 or not all(names, name -> instance(name, String) and #name > 0)
        or #unique names != #names then error "expected distinct, nonempty basis names";
    if ring G =!= ZZ or numRows G != #names or numColumns G != #names or G != transpose G then
        error "expected a symmetric integral Gram matrix of the basis size";
    if det G == 0 then error "expected a nondegenerate Gram matrix";
    if not all(#names, i -> G_(i,i) % 2 == 0) then error "expected an even K3 divisor lattice";
    new MarkedDivisorLattice from {
        "field" => k,
        "basis" => names,
        "gram" => G,
        symbol latticeIdentity => new MutableHashTable
        }
    )

divisorClass = method()
divisorClass(MarkedDivisorLattice, List) := DivisorClass => (L, coords) -> (
    if #coords != #(L#"basis") or not all(coords, c -> instance(c, ZZ)) then
        error "expected one integral coordinate per basis element";
    new DivisorClass from {"lattice" => L, "coordinates" => coords}
    )

requireSameLattice = (a, b) -> (
    L := a#"lattice";
    if L#(symbol latticeIdentity) =!= (b#"lattice")#(symbol latticeIdentity) then
        error "divisor classes must have the same marked lattice parent";
    L
    )

divisorPairing = method()
divisorPairing(DivisorClass, DivisorClass) := ZZ => (a, b) -> (
    L := requireSameLattice(a, b);
    A := matrix {a#"coordinates"};
    B := matrix {b#"coordinates"};
    (A * L#"gram" * transpose B)_(0,0)
    )
