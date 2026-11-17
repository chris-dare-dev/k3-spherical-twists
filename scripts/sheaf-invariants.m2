-- Prints computed and predicted invariants for one surface and exits with status 1 if any differ.
-- Environment: K3D = 2, 3 or 4 (default 2); K3SLOW = 1 adds the slow Ext groups;
-- K3SEED and K3CHAR choose the random seed and the characteristic.
path = prepend(currentDirectory(), path);
needsPackage "K3Twists";

env = (name, default) -> if getenv name === "" then default else value getenv name;
d = env("K3D", 2);
K = k3Surface(d, Seed => env("K3SEED", 1), Characteristic => env("K3CHAR", 32003));
<< "d = " << d << ", n = " << K#"n" << ": complete intersection of degrees " << toString K#"degrees"
   << " in P^" << d + 1 << " over " << toString coefficientRing K#"ring" << ", smooth, through x" << endl << flush;

t0 = currentTime();
rows = sheafInvariants(K, Slow => (env("K3SLOW", 0) == 1));
bad = 0;
scan(rows, r -> (
    ok := (r#1 === r#2);
    if not ok then bad = bad + 1;
    << "  " << pad(r#0, 26) << " computed " << pad(toString r#1, 14) << " predicted " << pad(toString r#2, 14)
       << (if ok then "ok" else "DIFFERENT") << endl;
    ));
<< #rows << " invariants, " << bad << " different, " << currentTime() - t0 << " s" << endl;
if bad > 0 then exit 1;
