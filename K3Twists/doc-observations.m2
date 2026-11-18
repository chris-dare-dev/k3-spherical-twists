doc ///
    Key
        DegreeObservation
        (net, DegreeObservation)
        cohomologyObservation
        (cohomologyObservation, CoherentSheaf)
        (cohomologyObservation, K3ObjectReference)
        [cohomologyObservation, Degrees]
        extObservation
        (extObservation, CoherentSheaf, CoherentSheaf)
        (extObservation, K3ObjectReference, K3ObjectReference)
        [extObservation, Degrees]
        observedDimension
        (observedDimension, DegreeObservation, ZZ)
        degreeStatus
        (degreeStatus, DegreeObservation, ZZ)
    Headline
        observe cohomology and Ext in signed cohomological degrees
    Description
        Text
            An observation keeps its subjects, method, support interval and measured dimensions.
            It is complete when every degree in the support interval was measured.
            Select degrees with @TT "Degrees => {...}"@.
            A degree outside the known support has dimension zero. Inside the support,
            an uncomputed degree has null dimension. @TO degreeStatus@ also identifies
            unsupported observations such as a symbolic reference with no sheaf realization.
            Direct Ext uses the dimension bound on a certified smooth K3 model.
        Example
            K = k3Surface 2;
            E = shiftObject(structureObject K, 1);
            O = cohomologyObservation(E, Degrees => {-1})
            observedDimension(O, -1)
            degreeStatus(O, 1)
            degreeStatus(O, 2)
///

doc ///
    Key
        ObservationPrediction
        ObservationCheck
        (net, ObservationPrediction)
        (net, ObservationCheck)
        observationPrediction
        (observationPrediction, String, String, List, Sequence)
        [observationPrediction, Full]
        Full
        checkObservation
        (checkObservation, DegreeObservation, ObservationPrediction)
    Headline
        compare a measured observation with a versioned prediction
    Description
        Text
            Construct a prediction with its name, version, list of hypotheses, quantity and expected value.
            An integer expected value compares the Euler characteristic. A hash table keyed by degree
            compares the listed degrees. Set @TT "Full => true"@ to interpret omitted degrees as zero
            and require a complete table for a match.
            Each check retains the observation and prediction. A revision can be checked against
            the existing observation. Missing values can make a comparison inconclusive.
        Example
            K = k3Surface 2;
            O = cohomologyObservation shiftObject(structureObject K, 1);
            P = observationPrediction("structure Euler", "1", {"smooth K3"}, ("cohomology", -2));
            checkObservation(O, P)
///
