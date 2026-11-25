doc ///
    Key
        TwistRealization
        (net, TwistRealization)
        (mukaiClass, TwistRealization)
        realizeTwistImage
        (realizeTwistImage, K3ObjectReference)
        (realizeTwistImage, SphericalTwistWord, K3ObjectReference)
        realizedHomology
        (realizedHomology, TwistRealization, ZZ)
    Headline
        realize certified spherical twists on a quartic
    Description
        Text
            Degree-zero evaluation supports a forward twist about the certified structure
            sheaf on a smooth quartic, applied to the marked point sheaf or hyperplane bundle. The
            evaluation is a chain map of complexes concentrated in homological degree zero.
            Its cone has homological degrees zero and one. @TO realizedHomology@ takes a
            cohomological degree and sheafifies the corresponding homology module.
            The realization includes its symbolic image, hypotheses, complex, and shifted
            catalogue representative. Unsupported words return a status and a reason, while
            their symbolic image and Mukai class remain available.

            The inverse structure-sheaf twist of the marked point ideal uses its actual
            inclusion into O as coevaluation. On I_x[n] its fibre projects
            quasi-isomorphically onto O_x[n-1]. The realization keeps both maps.

            The inverse twist about the hyperplane bundle sends the structure sheaf to
            @TT "Q[-1]"@, where @TO quotientBundle@ gives Q. The coevaluation uses the dual
            of the coordinate basis and its shifted cone has homological degrees minus one
            and zero. The forward twist sends the quotient representative back to the
            structure sheaf by the dual coordinate sequence.

            The forward twist about O also supports O(-H). Its derived Hom is
            four-dimensional in degree two. A finite resolution of an ideal cutting out
            the vertex of the affine cone supplies the evaluation classes Serre dual
            to the four coordinate sections. The result records the evaluation chain map
            and pairing matrix. Its degree-zero and degree-one sheaf homology are
            O(-H) and four copies of O, respectively.

            Pass the signed word and the starting reference directly to
            @TO realizeTwistImage@ to realize the forward structure twist of O(-H)
            followed by its inverse. This entry point retains both steps for the
            chain-level computation. The result includes the forward realization,
            inverse coevaluation and a comparison from the original line bundle
            to the shifted cone of the coevaluation.

            Two forward twists about O on O(-H) use the first explicit cone as
            the target of a degree-three evaluation. The degree-zero Koszul Hom strand
            supplies four evaluation classes modulo coboundaries. The second cone
            has sheaf homology O(-H), O^4, and O^4 in cohomological degrees zero,
            one, and two, respectively, and restores the initial Mukai class.
            The result records the first realization, the second evaluation, and
            the rank of the chosen classes.

            For a certified spherical line bundle O or O(H), the degree-zero identity in its
            self-evaluation splits off. The degree-two Serre trace then gives the surviving
            shift by minus one for a forward twist and plus one for an inverse twist.
            Signed words on the same line bundle use this comparison at each step, including
            shifted inputs. The realization records the supporting Hom degrees, signed
            steps and realization time. Other mixed words require further strategies.
        Example
            K = k3Surface 2;
            S = sphericalObject structureObject K;
            W = twistWord {twistStep(S, 1)};
            R = realizeTwistImage applyWord(W, catalogueObject(K, "O_x"));
            R
            cohomologyDims realizedHomology(R, -1)
            H = lineBundleObject(K, K#"polarization");
            V = twistWord {twistStep(sphericalObject H, -1)};
            U = realizeTwistImage applyWord(V, structureObject K);
            U
            cohomologyDims realizedHomology(U, 1)
///

doc ///
    Key
        homologicalCutInclusion
        (homologicalCutInclusion, Complex, ZZ)
        signedCutInclusion
        (signedCutInclusion, Complex, ComplexMap, ZZ, ZZ)
        certifiesCutSquare
        (certifiesCutSquare, ComplexMap, ComplexMap, ComplexMap, ComplexMap)
    Headline
        recover and compare a strict upper cut with a supplied homological window
    Usage
        homologicalCutInclusion(C, q)
        signedCutInclusion(C, f, sign, q)
        certifiesCutSquare(a, b, s, t)
    Description
        Text
            The marking supplies an integer q for which the desired phase cut on these
            objects is homological truncation in degrees at least q. The first method
            returns the inclusion of the canonical truncation into the original complex.
            The second constructs an arrow into the supplied signed output from the input
            windows of f. Supply the native cone for sign 1 and the fibre (cone f)[1]
            for sign -1 in the indexing of the Complexes package.

            For the cone, take the inverse image of the top cycles in the cone on the lower
            inputs. For the fibre, remove the bottom cohomology from the fibre on the upper
            inputs and compose into C. Both constructions use maps of presented modules.

            The comparison takes chain maps a and b and specified identifications s of
            their sources and t of their targets, directed from a to b. It checks the square
            t*a == b*s and checks that the full cones of s and t are acyclic. A true result
            certifies the two arrows over the specified output identification. A false
            result means these four maps failed to give this strict certificate.
        Example
            K = k3Surface 2;
            W = twistWord {twistStep(sphericalObject structureObject K, 1)};
            R = realizeTwistImage(W, catalogueObject(K, "O_x"));
            j = signedCutInclusion(R#"complex", R#"chainMap", 1, 1);
            target j === R#"complex"
///

doc ///
    Key
        CurveWallMark
        curveWallMark
        (curveWallMark, DivisorClass, DivisorClass, List, List)
        curveWallIdealCut
        (curveWallIdealCut, CurveWallMark, DivisorClass, RingElement, ComplexMap)
    Headline
        compute the phase-one boundary of a shifted rank-one ideal at a single curve wall
    Usage
        W = curveWallMark(H, C, {b, den}, {x, y})
        cut = curveWallIdealCut(W, L, n, f)
    Description
        Text
            Use the geometric Tramel--Xia two-tilt heart on a smooth projective K3.
            The nef class H contracts precisely the marked smooth rational curve C of
            square -2. The marking specifies this geometric lift. Supply an integral H,
            beta = b/den, and z = x + iy with exact rational coordinates. The constructor
            checks the numerical strip and positivity and recovers k = floor(beta.C)-1.
            Effectivity of C and the contracted locus are geometric input.

            L is the divisor class of the double dual of the ideal. On an affine chart
            trivialize L and use a degree-zero equation n for C. Supply a surjection f
            from the free line to a finite-length sheaf Q, as complexes in degree zero.
            The kernel is I and cone f represents I[1]. The method applies at H.L < -y.
            The number m of divisor additions is max(0, floor((L.C-k-1)/2)).
            The inclusion has target cone f. Its source represents L(mC)/I, the entire
            phase-one subobject. The projection to L(mC)[1] is multiplication by n^m
            in degree one. The maps commute with compatible changes of local frames.
            The returned keys are "curveSteps", "tailDivisor", "inclusion" and "projection".
        Example
            NS = markedDivisorLattice(QQ, {"C","F"}, matrix{{-2,1},{1,0}});
            v = (a,b) -> divisorClass(NS,{a,b});
            W = curveWallMark(v(1,2),v(1,0),{v(-1,0),4},{2,-1});
            S = QQ[s,n,Degrees=>{0,0}];
            P = S^1/ideal(s,n);
            f = map(complex P,complex S^1,hashTable {0=>map(P,S^1,{{1}})});
            cut = curveWallIdealCut(W,v(-2,0),n,f);
            (cut#"curveSteps",cut#"tailDivisor"#"coordinates",ann HH_0 source cut#"inclusion")
///

doc ///
    Key
        curveTorsionPreimage
        (curveTorsionPreimage, Complex, RingElement)
    Headline
        lift the divisor-supported torsion of degree-zero homology into its complex
    Usage
        j = curveTorsionPreimage(E, n)
    Description
        Text
            For E in nonnegative homological degrees, project E to its degree-zero
            homology modulo the elements killed by powers of n. The degreewise kernel
            is a homotopy fibre, so its inclusion lifts the torsion to E. Saturating the
            relations of a presentation also works with a nonfree bottom term. Higher
            differentials stay in the kernel, including the attaching map. To identify
            j as an HN inclusion one needs the phase order of the high piece, the
            torsion and the exterior quotient at the given marking.
///
