doc ///
    Key
        k3ModelArtifact
        (k3ModelArtifact, K3Surface)
        loadK3ModelArtifact
        (loadK3ModelArtifact, HashTable, String)
        bindK3ModelArtifact
        (bindK3ModelArtifact, K3Surface, HashTable, String)
        gradedPresentationArtifact
        (gradedPresentationArtifact, K3Surface, Module, String)
        loadGradedPresentation
        (loadGradedPresentation, K3Surface, HashTable)
        gradedComplexArtifact
        (gradedComplexArtifact, K3Surface, Complex, String)
        loadGradedComplex
        (loadGradedComplex, K3Surface, HashTable)
        gradedChainMapArtifact
        (gradedChainMapArtifact, K3Surface, ComplexMap, String, Sequence)
        loadGradedChainMap
        (loadGradedChainMap, K3Surface, HashTable, Sequence, Sequence)
    Headline
        encode and reconstruct exact mathematical data
    Description
        Text
            Encode a model, graded presentation, or bounded complex of finitely presented modules as
            a versioned hash table. The JSON package can read and write these tables.
            The data uses exact prime-field coefficients and standard ordered coordinates
            for the K3 complete intersections and marked quartics of this package.
            Free complexes use version 1. A complex with a presented term uses version 2
            and stores a graded presentation for every term.
            Complex indices are homological. The loader checks that differentials preserve
            the internal grading, descend through the module relations, and compose to zero.
            Pass the verified SHA-256 digest of the stored model to @TO loadK3ModelArtifact@.
            The loaded model records this digest and supplies the same quotient ring for all
            reconstructed modules and complexes. The artifact store supplies and verifies the digest.
            For a surface already in memory, @TO bindK3ModelArtifact@ checks the verified model data
            against the surface and binds its digest before writing dependent artifacts.
            Write a degree-zero chain map with @TO gradedChainMapArtifact@, passing the model digest
            and the pair of source and target complex digests after the map.
            Version 1 stores one matrix per homological degree in the intersection of
            the endpoint ranges, in ascending order.
            For @TO loadGradedChainMap@ pass the already loaded source and target complexes,
            each paired with its verified artifact digest. Reuse a loaded complex to
            reconstruct multiple maps that share it. The loader checks the endpoint bindings,
            internal grading, module relations, and chain-map identities.
///
