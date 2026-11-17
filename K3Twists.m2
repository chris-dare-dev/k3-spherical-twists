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
    "Characteristic",
    "Seed",
    "SpecialQuadric",
    -- classes
    "mukaiPairing",
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

load "./K3Twists/classes.m2"
load "./K3Twists/surfaces.m2"
load "./K3Twists/sheaves.m2"
load "./K3Twists/catalogue.m2"
load "./K3Twists/invariants.m2"
load "./K3Twists/tasks.m2"
load "./K3Twists/tasks/ext-pair.m2"
load "./K3Twists/tasks/invariant.m2"
load "./K3Twists/tasks/synthetic.m2"

beginDocumentation()

load "./K3Twists/doc.m2"
load "./K3Twists/tests.m2"

end--
