newPackage(
    "K3Twists",
    Version => "0.2",
    Headline => "sheaves on explicit K3 surfaces that arise from spherical twists along O and O(H)",
    Authors => {{Name => "Christopher Dare"}},
    PackageExports => {"Varieties"},
    AuxiliaryFiles => true,
    DebuggingMode => false
    )

export {
    -- surfaces
    "K3Surface",
    "k3Surface",
    "K3FamilyRecipe",
    "k3Recipe",
    "k3Families",
    "markedQuarticSpec",
    "markedCurveClass",
    "markedCurveSheaf",
    "realizeK3Surface",
    "Characteristic",
    "Seed",
    "SpecialQuadric",
    -- classes
    "MarkedDivisorLattice",
    "markedDivisorLattice",
    "DivisorClass",
    "divisorClass",
    "divisorPairing",
    "MukaiClass",
    "mukaiClass",
    "mukaiPairing",
    "tensorByDivisor",
    "twistVector",
    "dualVector",
    "chainNumber",
    -- sheaves
    "cohomologyDims",
    "extDims",
    "extViaHom",
    "pointIdealSheaf",
    "pointSheaf",
    "kernelBundle",
    "pointKernelBundle",
    "quotientBundle",
    "tracelessKernelBundle",
    "quadricKernelBundle",
    "mukaiBundle",
    -- catalogue
    "catalogue",
    "catalogueClasses",
    "catalogueMukaiClass",
    "catalogueEntry",
    "extTableRow",
    -- invariants
    "sheafInvariants",
    "sheafInvariantNames",
    "sheafInvariant",
    "Slow",
    -- tasks
    "expandBatch",
    "runTask",
    "registerTaskKind"
    }

load "./K3Twists/numerical/lattices.m2"
load "./K3Twists/numerical/classes.m2"
load "./K3Twists/geometry/quartic-data.m2"
load "./K3Twists/geometry/recipes.m2"
load "./K3Twists/geometry/models.m2"
load "./K3Twists/geometry/marked-quartics.m2"
load "./K3Twists/sheaves.m2"
load "./K3Twists/studies/catalogueClasses.m2"
load "./K3Twists/catalogue.m2"
load "./K3Twists/invariants.m2"
load "./K3Twists/tasks.m2"
load "./K3Twists/tasks/ext-pair.m2"
load "./K3Twists/tasks/invariant.m2"
load "./K3Twists/tasks/synthetic.m2"

beginDocumentation()

load "./K3Twists/doc.m2"
load "./K3Twists/doc-marked-quartics.m2"
load "./K3Twists/doc-models.m2"
load "./K3Twists/tests.m2"
load "./K3Twists/tests-marked-quartics.m2"
load "./K3Twists/tests-models.m2"

end--
