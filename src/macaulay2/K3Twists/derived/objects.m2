-- References to objects and shifts in one realized marked K3 model.

K3ObjectReference = new Type of VarietyObjectReference
K3ObjectReference.synonym = "K3 object reference"
ShiftedK3Object = new Type of K3ObjectReference
ShiftedK3Object.synonym = "shifted K3 object"

protect symbol objectIdentity
protect symbol twistReference
protect symbol shiftedReference

requireObjectModel = (K, K') -> (
    sameParent := if instance(K, K3Surface) and instance(K', K3Surface) then
        (K#"lattice")#(symbol latticeIdentity) === (K'#"lattice")#(symbol latticeIdentity)
    else if instance(K, QuinticThreefold) and instance(K', QuinticThreefold) then
        K#(symbol quinticModelIdentity) === K'#(symbol quinticModelIdentity)
    else false;
    if not sameParent or K#"variety" =!= K'#"variety"
        then error "objects and twists must belong to the same realized model"
    )

requireSurfaceClass = (K, v) -> requireSameLattice(K#"polarization", v#"divisor")

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

numericalClass K3ObjectReference := MukaiClass => E -> mukaiClass E

-- Used by each model's shift constructor. Keep shift cancellation geometric.
shiftReference = (F, E, n) -> (
    if n == 0 then return E;
    K := E#"surface";
    cached(K, (symbol shiftedReference, E#(symbol objectIdentity), n), () -> (
        v := numericalClass E;
        if n % 2 != 0 then v = negateNumerical v;
        new F from ({
            "surface" => K, "object" => E, "shift" => n, "evidence" => E#"evidence",
            symbol objectIdentity => new MutableHashTable
            } | numericalReferenceFields v)
        ))
    )

shiftObject = method()
shiftObject(K3ObjectReference, ZZ) := K3ObjectReference => (E,n) -> shiftReference(ShiftedK3Object, E, n)
shiftObject(ShiftedK3Object, ZZ) := K3ObjectReference => (E,n) -> shiftObject(E#"object", E#"shift" + n)

net K3ObjectReference := E -> (
    desc := E#"definition";
    if desc#"kind" == "line_bundle" then net ("line bundle O(" | toString desc#"coordinates" | ")")
    else net (desc#"kind" | " object " | desc#"name")
    )
net ShiftedK3Object := E -> net E#"object" | "[" | net E#"shift" | "]"
