doc ///
    Key
        TwistRealization
        (net, TwistRealization)
        (mukaiClass, TwistRealization)
        realizeTwistImage
        (realizeTwistImage, K3ObjectReference)
        realizedHomology
        (realizedHomology, TwistRealization, ZZ)
    Headline
        realize degree-zero spherical evaluation on a quartic
    Description
        Text
            The strategy supports one forward twist about the certified structure sheaf on a
            smooth quartic, applied to the marked point sheaf or the hyperplane bundle. The
            evaluation is a chain map of complexes concentrated in homological degree zero.
            Its cone has homological degrees zero and one. @TO realizedHomology@ takes a
            cohomological degree and sheafifies the corresponding homology module.
            The realization includes its symbolic image, hypotheses, complex, and shifted
            catalogue representative. Unsupported words return a status and a reason, while
            their symbolic image and Mukai class remain available.
        Example
            K = k3Surface 2;
            S = sphericalObject structureObject K;
            W = twistWord {twistStep(S, 1)};
            R = realizeTwistImage applyWord(W, catalogueObject(K, "O_x"));
            R
            cohomologyDims realizedHomology(R, -1)
///
