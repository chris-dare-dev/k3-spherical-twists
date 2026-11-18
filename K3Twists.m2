newPackage(
    "K3Twists",
    Version => "0.2",
    Headline => "sheaves on explicit K3 surfaces that arise from spherical twists along O and O(H)",
    Authors => {{Name => "Christopher Dare"}},
    PackageExports => {"Varieties"},
    PackageImports => {"Complexes"},
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
    -- portable artifact data
    "k3ModelArtifact",
    "loadK3ModelArtifact",
    "bindK3ModelArtifact",
    "gradedPresentationArtifact",
    "loadGradedPresentation",
    "gradedComplexArtifact",
    "loadGradedComplex",
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
    -- measured and predicted invariants
    "DegreeObservation",
    "ObservationPrediction",
    "ObservationCheck",
    "cohomologyObservation",
    "extObservation",
    "observedDimension",
    "degreeStatus",
    "observationPrediction",
    "checkObservation",
    "Full",
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
    -- explicit twist realizations
    "TwistRealization",
    "realizeTwistImage",
    "realizedHomology",
    -- tasks
    "expandBatch",
    "runTask",
    "registerTaskKind",
    -- spherical twist words
    "K3ObjectReference",
    "ShiftedK3Object",
    "SymbolicTwistImage",
    "SphericalTwistGenerator",
    "SphericalTwistStep",
    "SphericalTwistWord",
    "objectReference",
    "catalogueObject",
    "lineBundleObject",
    "structureObject",
    "shiftObject",
    "sphericalObject",
    "checkedSphericalObject",
    "assumeSphericalObject",
    "twistStep",
    "twistWord",
    "composeTwistWords",
    "inverseTwistWord",
    "mukaiReflection",
    "applyWordToClass",
    "applyWord",
    "VerifiedOnly"
    }

load "./K3Twists/numerical/lattices.m2"
load "./K3Twists/numerical/classes.m2"
load "./K3Twists/geometry/quartic-data.m2"
load "./K3Twists/geometry/recipes.m2"
load "./K3Twists/geometry/models.m2"
load "./K3Twists/geometry/marked-quartics.m2"
load "./K3Twists/artifacts/model.m2"
load "./K3Twists/artifacts/graded.m2"
load "./K3Twists/sheaves.m2"
load "./K3Twists/studies/catalogueClasses.m2"
load "./K3Twists/catalogue.m2"
load "./K3Twists/studies/shortWordInvariants.m2"
load "./K3Twists/tasks.m2"
load "./K3Twists/tasks/ext-pair.m2"
load "./K3Twists/tasks/invariant.m2"
load "./K3Twists/tasks/synthetic.m2"
load "./K3Twists/derived/objects.m2"
load "./K3Twists/observations/degrees.m2"
load "./K3Twists/observations/predictions.m2"
load "./K3Twists/derived/spherical.m2"
load "./K3Twists/derived/words.m2"

load "./K3Twists/derived/quarticDerived.m2"
load "./K3Twists/derived/quarticCones.m2"
load "./K3Twists/tasks/quartic-prefix.m2"

beginDocumentation()

load "./K3Twists/doc.m2"
load "./K3Twists/doc-marked-quartics.m2"
load "./K3Twists/doc-artifacts.m2"
load "./K3Twists/doc-models.m2"
load "./K3Twists/doc-words.m2"
load "./K3Twists/tests.m2"
load "./K3Twists/tests-marked-quartics.m2"
load "./K3Twists/tests-models.m2"
load "./K3Twists/doc-observations.m2"
load "./K3Twists/tests-observations.m2"
load "./K3Twists/tests-words.m2"

load "./K3Twists/doc-cones.m2"
load "./K3Twists/tests-cones.m2"
load "./K3Twists/tests-derived-quartic.m2"

end--
