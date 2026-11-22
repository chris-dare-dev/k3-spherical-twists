-- The Ext groups between two sheaves of the catalogue, of your own choice.
-- Paste the expressions into M2, or run with M2 --script data/examples/own-pair.m2 from the repository root.
--
-- The names are those of `catalogue K`.  A row is {E, F, dimensions of Ext^0, Ext^1, Ext^2, the Euler
-- characteristic predicted from the Mukai classes, the method}.  The dimensions are null where neither
-- sheaf is locally free: the package has no method for such a pair.
-- The cost grows quickly with the degree and with the ranks: the pairs below take about a second each
-- on the quartic, where M_H with itself takes about twenty; for d = 3 or 4 a pair among M_H and M_x
-- did not finish within two minutes when this was written.
path = prepend("src/", path);                -- the package is in src/ of the repository
needsPackage "K3Twists";
K = k3Surface 2;
<< "sheaves: " << apply(catalogueClasses K, first) << endl;
chosen = {("O", "M_H"), ("M_H", "M_x"), ("M_x", "O_x"), ("O_x", "O_x")};
for names in chosen do (
    row := extTableRow(K, names#0, names#1);
    << row << endl;
    -- where the groups were computed, their alternating sum is the predicted Euler characteristic
    if row#2 =!= null then assert(row#2#0 - row#2#1 + row#2#2 == row#3)
    );
