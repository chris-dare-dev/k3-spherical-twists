-- Installs the package into a temporary directory, as installPackage "K3Twists" does for a reader, and
-- exits with status 1 if an exported symbol has no documentation, if the documentation links to a node
-- that does not exist, or if an example fails.  Macaulay2 removes the directory when the install
-- succeeds; when installPackage fails it keeps it, with the error logs that it names.
--   M2 --script tests/macaulay2/install-package.m2
path = prepend(currentFileDirectory | "../../src/macaulay2/", path);
loadPackage("K3Twists", LoadDocumentation => true);

-- installPackage of Macaulay2 1.25 does not check this itself
exports = K3Twists#"exported symbols";
undocumented' = select(exports, s -> not K3Twists#"raw documentation"#?(format makeDocumentTag s));
if #undocumented' > 0 then (
    stderr << "exported without documentation: " << toString undocumented' << endl;
    exit 1;
    );

installPackage(K3Twists, InstallPrefix => temporaryFileName() | "/");
<< "installed: " << #exports << " exported symbols, each documented, and the examples ran" << endl;
