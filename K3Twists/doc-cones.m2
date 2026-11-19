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
