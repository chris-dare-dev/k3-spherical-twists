-- A word in spherical twists of your own, applied to the skyscraper sheaf of a point.
-- Paste the expressions into M2, or run with M2 --script examples/own-word.m2 from the repository.
--
-- A word lists signed steps in the order they are applied: 1 is a twist, -1 its inverse.  The class of
-- the image costs lattice arithmetic only, whatever the length of the word.  Building the image as a
-- complex is a separate step, and it answers "unsupported", with the reason, where the package has no
-- construction (GUIDE.md, "Certified quartic cones", says which words it has).
needsPackage "K3Twists";
K = k3Surface 2;
P = catalogueObject(K, "O_x");                                      -- the point sheaf
S = sphericalObject structureObject K;                              -- T_O
T = sphericalObject lineBundleObject(K, K#"polarization");          -- T_{O(H)}
coordinates = v -> {v#"rank", (v#"divisor")#"coordinates", v#"eulerComponent"};

-- the image of the point under T_O, then T_{O(H)}^{-1}, then T_O: a symbolic object and its Mukai class
W = twistWord {twistStep(S, 1), twistStep(T, -1), twistStep(S, 1)};
E = applyWord(W, P, VerifiedOnly => true);
<< "class of the image, as {rank, divisor, Euler component}: " << coordinates mukaiClass E << endl;
assert(applyWord(inverseTwistWord W, E) === P);                     -- the inverse word undoes it

-- the same on classes alone, for a word of forty steps
long = twistWord flatten toList(20 : {twistStep(S, 1), twistStep(T, 1)});
v = applyWordToClass(long, mukaiClass P);
<< "class after (T_{O(H)} T_O)^20: " << coordinates v << endl;
assert(mukaiPairing(v, v) == mukaiPairing(mukaiClass P, mukaiClass P));   -- twists are isometries
assert(applyWordToClass(inverseTwistWord long, v) === mukaiClass P);

-- as a complex: a word of three steps is beyond the constructions of the package, and it says so
R = realizeTwistImage E;
<< R << endl;
assert(R#"status" === "unsupported");
