-- Runs the tests of the package.  Exits with status 1 if a test fails.
path = prepend(currentDirectory(), path);
needsPackage "K3Twists";
check "K3Twists";
<< "all tests passed" << endl;
