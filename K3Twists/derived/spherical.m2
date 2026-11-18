-- Spherical generators carry the evidence used to apply their twist.

SphericalTwistGenerator = new Type of HashTable
SphericalTwistGenerator.synonym = "spherical twist generator"

-- Only realized models certified by the package's K3 constructors supply K3 Serre duality.
requireCertifiedK3 = K -> (
    X := K#"variety";
    marker := symbol k3Model;
    if not X.cache#?marker or X.cache#marker =!= K#"polarization" then
        error "expected a certified smooth K3 model"
    )

makeSphericalObject = (E, kind, reason, checkedExt) -> (
    K := E#"surface";
    requireCertifiedK3 K;
    v := E#"mukaiClass";
    if mukaiPairing(v, v) != -2 then error "a K3 spherical class must have Mukai square -2";
    evidence := hashTable {
        "kind" => kind,
        "reason" => reason,
        "object" => E,
        "selfExt" => checkedExt
        };
    new SphericalTwistGenerator from {
        "object" => E,
        "surface" => K,
        "dimension" => 2,
        "evidence" => evidence
        }
    )

sphericalObject = method()
sphericalObject K3ObjectReference := SphericalTwistGenerator => E -> (
    if not E#?"definition" or (E#"definition")#"kind" =!= "line_bundle" then
        error "automatic sphericality requires a line bundle; use checkedSphericalObject or assumeSphericalObject";
    makeSphericalObject(E, "theorem", "line bundle on a smooth K3 surface", null)
    )
sphericalObject ShiftedK3Object := SphericalTwistGenerator => E -> (
    sphericalObject E#"object";
    makeSphericalObject(E, "theorem", "shift of a line bundle on a smooth K3 surface", null)
    )

checkedSphericalObject = method()
checkedSphericalObject K3ObjectReference := SphericalTwistGenerator => E -> (
    K := E#"surface";
    requireCertifiedK3 K;
    if not E#?"definition" or (E#"definition")#"kind" =!= "catalogue" then
        error "a self-Ext check requires a catalogue object with a sheaf realization";
    entry := catalogueEntry(K, (E#"definition")#"name");
    F := entry#1;
    dims := if entry#3 then extViaHom(F, F) else extDims(F, F);
    if dims =!= {1, 0, 1} then error("self-Ext dimensions " | toString dims | " are not spherical");
    makeSphericalObject(E, "checked", "computed self-Ext and K3 Serre duality", dims)
    )

assumeSphericalObject = method()
assumeSphericalObject(K3ObjectReference, String) := SphericalTwistGenerator => (E, reason) -> (
    if #reason == 0 then error "record a reason for the sphericality assumption";
    makeSphericalObject(E, "assumed", reason, null)
    )

net SphericalTwistGenerator := S -> net S#"object" | " (" | net ((S#"evidence")#"kind") | ")"
