doc ///
    Key
        K3ObjectReference
        ShiftedK3Object
        objectReference
        (objectReference, K3Surface, String, MukaiClass)
        catalogueObject
        (catalogueObject, K3Surface, String)
        lineBundleObject
        (lineBundleObject, K3Surface, DivisorClass)
        structureObject
        (structureObject, K3Surface)
        shiftObject
        (shiftObject, K3ObjectReference, ZZ)
        (shiftObject, ShiftedK3Object, ZZ)
        (mukaiClass, K3ObjectReference)
    Headline
        refer to an object on a realized marked K3 or shift it
    Usage
        E = objectReference(K, name, v)
        E = catalogueObject(K, name)
        E = lineBundleObject(K, D)
        E = structureObject K
        shiftObject(E, n)
        mukaiClass E
    Inputs
        K:K3Surface
        name:String
            an external object reference or a catalogue name
        v:MukaiClass
            the declared class of the external object
        D:DivisorClass
            a divisor on the marked lattice of the model
        n:ZZ
            a cohomological shift
    Outputs
        E:K3ObjectReference
    Description
        Text
            An object reference records its surface model, definition and Mukai class.
            Catalogue references read the class without constructing the sheaf.
            Line bundle references use the full marked divisor coordinates.
            Repeated references to the same definition and class on the same realized model
            share an identity. Use one realized model throughout an expression.
            External references declare numerical data and require their own geometric evidence.
        Text
            A shift retains its object and cohomological degree. It multiplies the Mukai
            class by $(-1)^n$. Even shifts can therefore have the same class as their
            underlying object.
        Example
            K = k3Surface 2;
            OX = structureObject K;
            O2 = shiftObject(OX, 2)
            (mukaiClass O2 === mukaiClass OX, O2 === OX)
    SeeAlso
        sphericalObject
        applyWord
///

doc ///
    Key
        SphericalTwistGenerator
        sphericalObject
        (sphericalObject, K3ObjectReference)
        (sphericalObject, ShiftedK3Object)
        checkedSphericalObject
        (checkedSphericalObject, K3ObjectReference)
        assumeSphericalObject
        (assumeSphericalObject, K3ObjectReference, String)
    Headline
        specify a spherical twist generator with evidence
    Usage
        S = sphericalObject E
        S = checkedSphericalObject E
        S = assumeSphericalObject(E, reason)
    Inputs
        E:K3ObjectReference
        reason:String
            the explicit hypothesis under which to use an external generator
    Outputs
        S:SphericalTwistGenerator
    Description
        Text
            A generator stores its object, surface, spherical dimension and evidence.
            @TT "sphericalObject"@ uses the theorem for a line bundle or its shift on
            a certified smooth K3 surface. @TT "checkedSphericalObject"@ computes the
            self-Ext dimensions of a catalogue sheaf and uses K3 Serre duality.
            @TT "assumeSphericalObject"@ records an explicit hypothesis supplied by
            the caller. The K3 constructors check that the Mukai square is minus two.
        Example
            K = k3Surface 2;
            OX = structureObject K;
            S = sphericalObject OX
            C = checkedSphericalObject catalogueObject(K, "O");
            (S#"dimension", (C#"evidence")#"selfExt")
    SeeAlso
        twistStep
        applyWord
///

doc ///
    Key
        applyWord
        SphericalTwistStep
        SphericalTwistWord
        SymbolicTwistImage
        twistStep
        (twistStep, SphericalTwistGenerator, ZZ)
        twistWord
        (twistWord, List)
        composeTwistWords
        (composeTwistWords, SphericalTwistWord, SphericalTwistWord)
        inverseTwistWord
        (inverseTwistWord, SphericalTwistWord)
        (applyWord, SphericalTwistWord, K3ObjectReference)
        applyWordToClass
        (applyWordToClass, SphericalTwistWord, MukaiClass)
        mukaiReflection
        (mukaiReflection, MukaiClass, MukaiClass)
        VerifiedOnly
        [applyWord, VerifiedOnly]
        [applyWordToClass, VerifiedOnly]
    Headline
        apply signed spherical twists to objects or their numerical classes
    Usage
        a = twistStep(S, direction)
        W = twistWord steps
        composeTwistWords(W, U)
        inverseTwistWord W
        applyWord(W, E)
        applyWordToClass(W, v)
        mukaiReflection(v, s)
    Inputs
        S:SphericalTwistGenerator
        direction:ZZ
            1 for the twist or -1 for its inverse
        steps:List
            signed twist steps in application order
        U:SphericalTwistWord
        E:K3ObjectReference
        v:MukaiClass
        s:MukaiClass
            a class of Mukai square minus two
        VerifiedOnly => Boolean
            require checked or theorem-backed evidence to apply the word
    Outputs
        W:SphericalTwistWord
    Description
        Text
            A word applies its list of steps from first to last. The empty list is
            the identity. @TT "composeTwistWords"@ applies the first word and then
            the second. The inverse reverses the order and negates the signs.
            All objects and generators must belong to the same realized model.
        Text
            @TT "applyWord"@ returns a symbolic object reference, sharing previously
            constructed prefixes on the model. An image records its starting object,
            preceding prefix, last signed step, numerical class and evidence. Its type
            describes a formal image. Computing a complex or its cohomology requires
            a realization strategy. Adjacent inverse steps with the same verified
            object reference cancel. Steps with provisional hypotheses retain their
            evidence. @TT "VerifiedOnly"@ checks the word and the input object's
            inherited evidence.
        Text
            @TT "applyWordToClass"@ computes only the numerical action and builds no
            object prefixes. On a K3, both directions use the reflection
            $v+\langle v,s\rangle s$ on the full marked lattice. The quintic uses
            the alternating Euler form and the direction of each signed step.
            @TT "twistVector"@ is the original tensor-by-a-line-bundle operation.
        Example
            K = k3Surface 2;
            P = catalogueObject(K, "O_x");
            S = sphericalObject structureObject K;
            T = sphericalObject lineBundleObject(K, K#"polarization");
            W = twistWord {twistStep(S, 1), twistStep(T, -1)}
            E = applyWord(W, P, VerifiedOnly => true)
            v = mukaiClass E;
            {v#"rank", (v#"divisor")#"coordinates", v#"eulerComponent"}
            applyWord(inverseTwistWord W, E) === P
    SeeAlso
        mukaiPairing
        tensorByDivisor
///
