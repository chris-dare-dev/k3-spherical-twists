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
    Headline
        encode and reconstruct exact mathematical data
    Description
        Text
            Encode a model, graded presentation, or bounded complex of finite free modules as
            a versioned hash table. The JSON package can read and write these tables.
            Version one uses exact prime-field coefficients and standard ordered coordinates.
            It supports the K3 complete intersections and marked quartics of this package.
            Complex indices are homological and all maps preserve the internal grading.
            A complex currently requires free terms.
            Pass the verified SHA-256 digest of the stored model to @TO loadK3ModelArtifact@.
            The loaded model records this digest and supplies the same quotient ring for all
            reconstructed modules and complexes. The artifact store supplies and verifies the digest.
            For a surface already in memory, @TO bindK3ModelArtifact@ checks the verified model data
            against the surface and binds its digest before writing dependent artifacts.
///
