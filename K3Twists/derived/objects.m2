-- References to objects and shifts in one realized marked K3 model.

K3ObjectReference = new Type of HashTable
K3ObjectReference.synonym = "K3 object reference"
ShiftedK3Object = new Type of K3ObjectReference
ShiftedK3Object.synonym = "shifted K3 object"

protect symbol objectIdentity
protect symbol twistReference
protect symbol shiftedReference

requireObjectModel = (K, K') -> (
    if (K#"lattice")#(symbol latticeIdentity) =!= (K'#"lattice")#(symbol latticeIdentity)
        or K#"variety" =!= K'#"variety" then error "objects and twists must belong to the same realized K3 model"
    )

requireSurfaceClass = (K, v) -> requireSameLattice(K#"polarization", v#"divisor")

classCoordinates = v -> (v#"rank", (v#"divisor")#"coordinates", v#"eulerComponent")

newObjectReference = (K, definition, v) -> (
    requireSurfaceClass(K, v);
    cached(K, (symbol twistReference, definition, classCoordinates v), () ->
        new K3ObjectReference from {
            "surface" => K,
            "definition" => definition,
            "mukaiClass" => v,
            "evidence" => {},
            symbol objectIdentity => new MutableHashTable
            })
    )

objectReference = method()
objectReference(K3Surface, String, MukaiClass) := K3ObjectReference => (K, name, v) -> (
    if #name == 0 then error "expected a nonempty object reference";
    newObjectReference(K, hashTable {"kind" => "declared", "name" => name}, v)
    )

catalogueObject = method()
catalogueObject(K3Surface, String) := K3ObjectReference => (K, name) ->
    newObjectReference(K, hashTable {"kind" => "catalogue", "name" => name}, catalogueMukaiClass(K, name))

lineBundleObject = method()
lineBundleObject(K3Surface, DivisorClass) := K3ObjectReference => (K, D) -> (
    requireSameLattice(K#"polarization", D);
    v := mukaiClass(1, D, 1 + divisorPairing(D, D) // 2);
    newObjectReference(K, hashTable {"kind" => "line_bundle", "coordinates" => D#"coordinates"}, v)
    )

structureObject = method()
structureObject K3Surface := K3ObjectReference => K ->
    lineBundleObject(K, divisorClass(K#"lattice", apply((K#"lattice")#"basis", i -> 0)))

mukaiClass K3ObjectReference := MukaiClass => E -> E#"mukaiClass"

shiftObject = method()
shiftObject(K3ObjectReference, ZZ) := K3ObjectReference => (E, n) -> (
    if n == 0 then return E;
    K := E#"surface";
    cached(K, (symbol shiftedReference, E#(symbol objectIdentity), n), () -> (
            v := E#"mukaiClass";
            (r, c, s) := classCoordinates v;
            sign := if n % 2 == 0 then 1 else -1;
            shiftedClass := mukaiClass(sign * r, divisorClass(K#"lattice", apply(c, i -> sign * i)), sign * s);
            new ShiftedK3Object from {
                "surface" => K,
                "object" => E,
                "shift" => n,
                "mukaiClass" => shiftedClass,
                "evidence" => E#"evidence",
                symbol objectIdentity => new MutableHashTable
                }
            ))
    )
shiftObject(ShiftedK3Object, ZZ) := K3ObjectReference => (E,n) -> shiftObject(E#"object", E#"shift" + n)

net K3ObjectReference := E -> (
    desc := E#"definition";
    if desc#"kind" == "line_bundle" then net ("line bundle O(" | toString desc#"coordinates" | ")")
    else net (desc#"kind" | " object " | desc#"name")
    )
net ShiftedK3Object := E -> net E#"object" | "[" | net E#"shift" | "]"
