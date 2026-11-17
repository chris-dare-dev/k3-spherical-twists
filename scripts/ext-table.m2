-- Ext groups between pairs of sheaves of the catalogue on one surface.
-- One line per ordered pair: name of E, name of F, dimensions of Ext^0, Ext^1, Ext^2, the Euler
-- characteristic predicted from the classes, whether the two agree, and the time.
-- Environment:
--   K3D = 2, 3 or 4;  K3SPECIAL = 1 uses the special quadric (d = 3) and adds the rank 2 bundle U;
--   K3MAXRANK = r (default 5): a pair is "light" if the smaller of the two ranks is at most r;
--   K3TIER = light (default) computes the light pairs in this process, each with a limit of
--            K3PAIRLIMIT seconds (default 600);
--   K3TIER = list prints the indices "i j" of the other pairs, one per line;
--   K3PAIR = "i j" computes that one pair (use a shell time limit around the process).
path = prepend(currentDirectory(), path);
needsPackage "K3Twists";

env = (name, default) -> if getenv name === "" then default else value getenv name;
d = env("K3D", 2);
limit = env("K3PAIRLIMIT", 600);
maxRank = env("K3MAXRANK", 5);
tier = if getenv "K3TIER" === "" then "light" else getenv "K3TIER";
K = k3Surface(d, Seed => env("K3SEED", 1), Characteristic => env("K3CHAR", 32003),
    SpecialQuadric => (env("K3SPECIAL", 0) == 1));
cat = catalogue K;
isLight = (a, b) -> min(a#2#0, b#2#0) <= maxRank or not (a#3 and b#3);

report = (a, b, row, t0) -> (
    status := if row#2 === null then "skipped"
        else if row#2 === "timeout" then "TIMEOUT"
        else if row#2#0 - row#2#1 + row#2#2 == row#3 then "ok" else "CHI DIFFERS";
    << pad(row#0, 14) << pad(row#1, 14) << pad(toString row#2, 18) << " chi " << pad(toString row#3, 6)
       << pad(status, 12) << currentTime() - t0 << " s" << endl << flush;
    status
    );

if getenv "K3PAIR" =!= "" then (
    ij := apply(separate(" ", getenv "K3PAIR"), value);
    (a, b) = (cat#(ij#0), cat#(ij#1));
    t0 = currentTime();
    st = report(a, b, extTableRow(d, a, b), t0);
    exit(if st === "CHI DIFFERS" then 1 else 0);
    );

if tier === "list" then (
    scan(#cat, i -> scan(#cat, j -> if not isLight(cat#i, cat#j) then << i << " " << j << endl));
    exit 0;
    );

<< "# d = " << d << ", n = " << K#"n" << ", " << #cat << " sheaves; light pairs, limit " << limit << " s each" << endl << flush;
scan(cat, a -> << "# class of " << a#0 << " = " << toString a#2 << (if a#3 then "" else "  (not locally free)") << endl);
(done, bad, late) = (0, 0, 0);
scan(cat, a -> scan(cat, b -> if isLight(a, b) then (
    t0 := currentTime();
    row := try (alarm limit; r := extTableRow(d, a, b); alarm 0; r) else (alarm 0; {a#0, b#0, "timeout", -mukaiPairing(d, a#2, b#2), "timeout"});
    st := report(a, b, row, t0);
    done = done + 1;
    if st === "CHI DIFFERS" then bad = bad + 1;
    if st === "TIMEOUT" then late = late + 1;
    )));
<< "# " << done << " pairs, " << bad << " with a different Euler characteristic, " << late << " timeouts" << endl;
if bad > 0 then exit 1;
