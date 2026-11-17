doc ///
    Key
        K3Twists
    Headline
        sheaves on explicit K3 surfaces that arise from spherical twists along O and O(H)
    Description
        Text
            The package builds a K3 surface of degree $2d$ in $\mathbb{P}^{d+1}$ for $d = 2, 3, 4$
            through a chosen point $x$, constructs the sheaves $I_x$, $M_H$, $M_x$, $Q$ and a few more,
            and compares their cohomology and Ext groups with closed formulas in $n = d + 2$.
        Example
            K = k3Surface 2
            cohomologyDims kernelBundle K
            sheafInvariant(K, "h^i(M_H)")
        Text
            The sheaves of the study are listed with their classes by @TO catalogue@, and
            @TO extTableRow@ computes the Ext groups between two of them.  Long computations are
            described as tasks: @TO expandBatch@ lists the tasks of a batch and @TO runTask@ computes one.
    Subnodes
        k3Surface
        k3Recipe
        markedDivisorLattice
        mukaiClass
        catalogue
        sheafInvariants
        expandBatch
///

doc ///
    Key
        k3Surface
        (k3Surface, ZZ)
        K3Surface
        (net, K3Surface)
        Characteristic
        Seed
        SpecialQuadric
        [k3Surface, Characteristic]
        [k3Surface, Seed]
        [k3Surface, SpecialQuadric]
    Headline
        a K3 surface of degree 2d through a point, as a random complete intersection
    Usage
        K = k3Surface d
    Inputs
        d:ZZ
            2, 3 or 4
        Characteristic => ZZ
            the characteristic of the prime field
        Seed => ZZ
            the seed of the random forms
        SpecialQuadric => Boolean
            for $d = 3$, whether the quadric is $x_0 x_1 + x_2 x_3 + x_4^2$
    Outputs
        K:K3Surface
    Description
        Text
            The surface is a quartic in $\mathbb{P}^3$, the intersection of a quadric and a cubic in
            $\mathbb{P}^4$, or the intersection of three quadrics in $\mathbb{P}^5$.  The forms are random
            among those vanishing at $x = (1:0:\dots:0)$; an error is raised if they do not define a
            smooth surface. Repeating a recipe with the same generator produces the same equations.
        Example
            K = k3Surface(3, Seed => 7, Characteristic => 10007)
            degree K#"variety"
            K#"point"
        Text
            A K3 surface is a hash table with the keys @TT "\"d\""@, @TT "\"n\""@ (which is $d + 2$,
            the number of sections of $O(H)$), @TT "\"degrees\""@, @TT "\"ring\""@,
            @TT "\"variety\""@, @TT "\"point\""@ (the ideal of $x$), @TT "\"seed\""@,
            @TT "\"characteristic\""@ and @TT "\"specialQuadric\""@.

            For the realized equations and marked lattice, see @TO realizeK3Surface@.
            With the special quadric the surface carries the rank 2 bundle of @TO mukaiBundle@.
///

doc ///
    Key
        mukaiPairing
        (mukaiPairing, ZZ, List, List)
        (mukaiPairing, MukaiClass, MukaiClass)
    Headline
        the pairing of two classes on a K3 surface of degree 2d
    Usage
        mukaiPairing(d, v, w)
    Inputs
        d:ZZ
        v:List
            a class $(r, c, s)$, where $c$ is the multiple of $H$
        w:List
    Outputs
        :ZZ
            $2d \cdot c c' - r s' - r' s$
    Description
        Text
            For sheaves $E$ and $F$ with classes $v$ and $w$ the Euler characteristic
            $\sum (-1)^i \dim Ext^i(E, F)$ is the negative of the pairing.
            The two-argument overload uses a shared marked lattice. See @TO mukaiClass@.
        Example
            mukaiPairing(2, {1, 0, 1}, {1, 0, 1})
            mukaiPairing(2, {3, -1, 1}, {1, 1, 3})
    SeeAlso
        twistVector
        dualVector
///

doc ///
    Key
        twistVector
        (twistVector, ZZ, List, ZZ)
        dualVector
        (dualVector, List)
        (dualVector, MukaiClass)
    Headline
        the class of a twist and of a dual
    Usage
        twistVector(d, v, t)
        dualVector v
    Inputs
        d:ZZ
        v:List
            the class $(r, c, s)$ of a sheaf $E$
        t:ZZ
    Outputs
        :List
            the class of $E(tH)$, or of the dual of a locally free $E$
    Description
        Text
            The typed operations on a marked lattice are @TO tensorByDivisor@ and the overload
            of @TT "dualVector"@ for @TO MukaiClass@.
        Example
            twistVector(2, {1, 0, 1}, 1)
            dualVector {3, -1, 1}
    SeeAlso
        mukaiPairing
///

doc ///
    Key
        chainNumber
        (chainNumber, ZZ, ZZ)
    Headline
        the sequence c_(k+1) = n c_k - c_(k-1) with c_(-1) = c_0 = 1
    Usage
        chainNumber(n, k)
    Inputs
        n:ZZ
        k:ZZ
            at least -1
    Outputs
        :ZZ
            $c_k$
    Description
        Text
            The numbers $c_1 = n - 1$ and $c_2 = n^2 - n - 1$ are ranks and cohomology dimensions of
            the sheaves of the study.
        Example
            apply(4, k -> chainNumber(4, k))
///

doc ///
    Key
        cohomologyDims
        (cohomologyDims, CoherentSheaf)
        extDims
        (extDims, CoherentSheaf, CoherentSheaf)
        extViaHom
        (extViaHom, CoherentSheaf, CoherentSheaf)
    Headline
        dimensions of cohomology and Ext groups on a surface
    Usage
        cohomologyDims F
        extDims(E, F)
        extViaHom(E, F)
    Inputs
        E:CoherentSheaf
        F:CoherentSheaf
    Outputs
        :List
            the dimensions in degrees 0, 1, 2
    Description
        Text
            @TT "extDims"@ computes $Ext^i(E, F)$ of sheaves directly, which is practical on the
            quartic only. Both methods require sheaves on the same variety.
            @TT "extViaHom"@ uses the cohomology of the sheaf $Hom(E, F)$ once it has evidence
            that $E$ is locally free. This includes bundles constructed by the package, free
            graded modules, and presentations certified by Fitting ideals on standard-graded
            projective varieties over a field. Use @TO extDims@ for direct Ext if the shortcut
            cannot establish local freeness.
        Example
            K = k3Surface 2;
            X = K#"variety";
            cohomologyDims(OO_X^1(1))
            extViaHom(pointKernelBundle K, pointSheaf K)
            extDims(OO_X^1(1), OO_X^1)
    SeeAlso
        extTableRow
///

doc ///
    Key
        pointIdealSheaf
        (pointIdealSheaf, K3Surface)
        pointSheaf
        (pointSheaf, K3Surface)
    Headline
        the ideal sheaf and the skyscraper sheaf of the point
    Usage
        pointIdealSheaf K
        pointSheaf K
    Inputs
        K:K3Surface
    Outputs
        :CoherentSheaf
            $I_x$ or $O_x$
    Description
        Example
            K = k3Surface 2;
            cohomologyDims pointIdealSheaf K
            cohomologyDims pointSheaf K
///

doc ///
    Key
        kernelBundle
        (kernelBundle, K3Surface)
        pointKernelBundle
        (pointKernelBundle, K3Surface)
        quotientBundle
        (quotientBundle, K3Surface)
    Headline
        the bundles M_H, M_x and Q
    Usage
        kernelBundle K
        pointKernelBundle K
        quotientBundle K
    Inputs
        K:K3Surface
    Outputs
        :CoherentSheaf
    Description
        Text
            $M_H$ is the kernel of $H^0(O(H)) \otimes O \to O(H)$, of rank $n - 1$.  $M_x$ is the kernel
            of $H^0(I_x(H)) \otimes O \to I_x(H)$, of rank $n - 2$.  $Q$ is the cokernel of
            $O \to H^0(O(H))^* \otimes O(H)$, of rank $n - 1$.
        Example
            K = k3Surface 2;
            rank kernelBundle K, rank pointKernelBundle K, rank quotientBundle K
            cohomologyDims kernelBundle K
    SeeAlso
        tracelessKernelBundle
        quadricKernelBundle
///

doc ///
    Key
        tracelessKernelBundle
        (tracelessKernelBundle, K3Surface)
        quadricKernelBundle
        (quadricKernelBundle, K3Surface)
    Headline
        the bundles E_2 and M_2H
    Usage
        tracelessKernelBundle K
        quadricKernelBundle K
    Inputs
        K:K3Surface
    Outputs
        :CoherentSheaf
    Description
        Text
            With $V = H^0(O(H))$, the bundle $E_2$ is the kernel of $sl(V) \otimes O \to V \otimes O(H)$,
            $\phi \mapsto \phi(x)$, of rank $n^2 - n - 1$.  $M_{2H}$ is the kernel of
            $H^0(O(2H)) \otimes O \to O(2H)$, of rank $4d + 1$.
        Example
            K = k3Surface 2;
            rank tracelessKernelBundle K, rank quadricKernelBundle K
///

doc ///
    Key
        mukaiBundle
        (mukaiBundle, K3Surface)
    Headline
        a rank 2 bundle on the degree 6 surface with the special quadric
    Usage
        mukaiBundle K
    Inputs
        K:K3Surface
            built with @TT "SpecialQuadric => true"@
    Outputs
        :CoherentSheaf
            of class $(2, 1, 2)$, with four sections
    Description
        Text
            The bundle is the cokernel of a $4 \times 4$ matrix $A$ of linear forms with
            $A^2 = (x_0 x_1 + x_2 x_3 + x_4^2) \cdot Id$.
        Example
            K = k3Surface(3, SpecialQuadric => true);
            U = mukaiBundle K;
            rank U, cohomologyDims U
///

doc ///
    Key
        catalogue
        (catalogue, K3Surface)
        catalogueClasses
        (catalogueClasses, K3Surface)
        catalogueEntry
        (catalogueEntry, K3Surface, String)
    Headline
        the sheaves of the study with their classes
    Usage
        catalogue K
        catalogueClasses K
        catalogueEntry(K, name)
    Inputs
        K:K3Surface
        name:String
            the name of a sheaf of the catalogue
    Outputs
        :List
            @TT "catalogue"@: a list of @TT "{name, sheaf, class, locally free}"@;
            @TT "catalogueClasses"@: the same without the sheaves;
            @TT "catalogueEntry"@: the one entry called @TT "name"@
    Description
        Text
            The catalogue holds the line bundles $O(tH)$, the ideal sheaves $I_x(tH)$, $O_x$, the
            bundles $M_H$, $M_x$, their duals and twists, $E_2$ and $M_{2H}$, and on the surface with the
            special quadric the bundle $U$ of @TO mukaiBundle@ and its dual.  A class is $(r, c, s)$
            with $c$ the multiple of $H$.

            @TT "catalogueClasses"@ builds no sheaf, and @TT "catalogueEntry"@ builds one; the duals
            take seconds to build for $d = 3, 4$.
        Example
            K = k3Surface 2;
            netList catalogueClasses K
            catalogueEntry(K, "M_H(1H)")
    SeeAlso
        extTableRow
///

doc ///
    Key
        extTableRow
        (extTableRow, List, List)
        (extTableRow, ZZ, List, List)
        (extTableRow, K3Surface, String, String)
    Headline
        the Ext groups between two sheaves of the catalogue
    Usage
        extTableRow(K, nameE, nameF)
        extTableRow(a, b)
        extTableRow(d, a, b)
    Inputs
        K:K3Surface
        nameE:String
        nameF:String
        d:ZZ
            for the three-argument form, half the surface degree
        a:List
            an entry of the catalogue, for $E$
        b:List
            an entry of the catalogue, for $F$
    Outputs
        :List
            @TT "{name of E, name of F, dimensions of Ext^0, Ext^1, Ext^2 or null, predicted Euler characteristic, method}"@
    Description
        Text
            When $E$ is locally free the groups are the cohomology of the sheaf $Hom(E, F)$.  When
            only $F$ is, they are the cohomology of $Hom(F, E)$ in reverse order, by Serre duality.  Of
            two locally free sheaves the one of smaller rank is the source of the Hom sheaf.  When
            neither is locally free nothing is computed and the dimensions are @TT "null"@.

            The predicted Euler characteristic is the negative of the @TO mukaiPairing@ of the classes.
            The two entries must come from the catalogue of the same constructed surface.
            Their classes and local-freeness information are checked against the catalogue data.
            The pairing uses the degree of that surface. The three-argument form also checks that
            $2d$ agrees with the surface degree.
        Example
            K = k3Surface 2;
            extTableRow(K, "M_x", "O_x")
            extTableRow(K, "I_x(1H)", "M_x")
            extTableRow(K, "O_x", "I_x")
    Caveat
        The time grows quickly with the ranks: on the quartic two bundles of rank 3 take seconds and
        two of rank 11 do not finish in minutes.
///

doc ///
    Key
        sheafInvariants
        (sheafInvariants, K3Surface)
        sheafInvariantNames
        (sheafInvariantNames, K3Surface)
        sheafInvariant
        (sheafInvariant, K3Surface, String)
        Slow
        [sheafInvariants, Slow]
        [sheafInvariantNames, Slow]
    Headline
        computed and predicted invariants of I_x, M_H, M_x and Q
    Usage
        sheafInvariants K
        sheafInvariantNames K
        sheafInvariant(K, name)
    Inputs
        K:K3Surface
        name:String
            the name of an invariant of the fast or the slow list
        Slow => Boolean
            whether to append the slow list
    Outputs
        :List
            @TT "sheafInvariants"@: a list of @TT "{name, computed value, predicted value}"@;
            @TT "sheafInvariantNames"@: the names; @TT "sheafInvariant"@: the one row called @TT "name"@
    Description
        Text
            The fast list uses sheaf cohomology only.  The slow list computes some of the same numbers
            as Ext groups, together with $Ext^i(F, F)$ for $F = I_x(H), M_H, M_x$; it takes minutes on
            the quartic and is not practical for $d = 3, 4$.
        Example
            K = k3Surface 2;
            netList sheafInvariants K
            sheafInvariant(K, "h^i(M_x(-H))")
///

doc ///
    Key
        expandBatch
        (expandBatch, HashTable)
        runTask
        (runTask, HashTable)
    Headline
        the tasks of a batch, and the outcome of one task
    Usage
        expandBatch description
        runTask task
    Inputs
        description:HashTable
            with the keys @TT "\"surfaces\""@ and @TT "\"tasks\""@
        task:HashTable
            one of the tasks returned by @TT "expandBatch"@
    Outputs
        :List
            @TT "expandBatch"@: the tasks, as hash tables
        :HashTable
            @TT "runTask"@: the outcome of the task
    Description
        Text
            Batches, tasks and outcomes are hash tables with string keys, the form in which the
            script @TT "runners/task-runner.m2"@ reads and writes them as JSON.

            A surface is given by @TT "\"d\""@ and optionally @TT "\"seed\""@,
            @TT "\"characteristic\""@ and @TT "\"special_quadric\""@.  Each entry of
            @TT "\"tasks\""@ has a @TT "\"kind\""@ and is expanded on every surface:

            @UL {
                LI {TT "\"ext_pair\"", ": one task per ordered pair of sheaves of the catalogue.  ",
                    TT "\"sheaves\"", " is ", TT "\"all\"", " or a list of names; ", TT "\"sources\"",
                    " and ", TT "\"targets\"", " can be given instead.  The task computes ",
                    TO extTableRow, "."},
                LI {TT "\"invariant\"", ": one task per invariant.  ", TT "\"names\"", " is ",
                    TT "\"fast\"", ", ", TT "\"slow\"", ", ", TT "\"all\"", " or a list of names.  ",
                    "The task computes ", TO sheafInvariant, "."},
                LI {TT "\"synthetic\"", ": one task per entry of ", TT "\"items\"",
                    ", which holds memory, sleeps or fails; it exercises the limits of a run."}
            }@

            Every task has an @TT "\"id\""@, a @TT "\"cost\""@ and, where there is one, a
            @TT "\"predicted\""@ value.  The cost of a pair is the rank of the sheaf $Hom(E, F)$; it
            is a hint for ordering tasks and choosing limits, not an estimate of the time.
        Example
            description = hashTable {
                "surfaces" => {hashTable {"d" => 2}},
                "tasks" => {hashTable {"kind" => "ext_pair", "sheaves" => {"O", "M_x"}}}};
            tasks = expandBatch description;
            netList apply(tasks, t -> {t#"id", t#"cost", t#"predicted"#"chi"})
            peek runTask last tasks
        Text
            The outcome has a @TT "\"status\""@: @TT "\"ok\""@ when a value was computed and agrees
            with the predicted one or has none to agree with, @TT "\"mismatch\""@ when it differs,
            @TT "\"unsupported\""@ when there is no method.  It also has the @TT "\"value\""@, the
            @TT "\"predicted\""@ value, @TT "\"agrees\""@, the @TT "\"method\""@ and the seconds spent
            building the sheaves and computing.
///

doc ///
    Key
        registerTaskKind
        (registerTaskKind, String, HashTable)
    Headline
        make a computation kind available to the batch functions
    Usage
        registerTaskKind(name, descriptor)
    Inputs
        name:String
            an unused kind name
        descriptor:HashTable
            a version, requirement names, three validators, an expander and a computation function
    Description
        Text
            Load a kind's module before calling @TO expandBatch@ or @TO runTask@.
            The descriptor has a positive integer @TT "version"@ and a string list
            @TT "requirements"@. The @TT "validate_set"@, @TT "validate_task"@, and
            @TT "validate_result"@ functions check their inputs and raise an error for
            invalid fields. The @TT "expand"@ function accepts the set index, task-set
            parameters, and normalized surface specifications. It returns a list of
            tasks without building those surfaces. The @TT "run"@ function accepts
            one task and returns its observation and prediction.
        Text
            A task has @TT "id"@, @TT "kind"@, @TT "group"@, @TT "set"@ and @TT "cost"@
            fields and any scientific inputs used by the kind. The registry adds the
            kind version and requirements. A computation returns @TT "value"@,
            @TT "predicted"@, @TT "agrees"@, @TT "method"@, @TT "setup_seconds"@ and
            @TT "compute_seconds"@. It may also return a list @TT "outputs"@ of
            references with a name, media type and digest. The registry derives the
            status from the observation and the comparison.
    SeeAlso
        expandBatch
        runTask
///
