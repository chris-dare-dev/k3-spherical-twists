-- Public geometry and numerical queries shared by the realized models.

VarietyModel = new Type of HashTable
VarietyObjectReference = new Type of HashTable
VarietyNumericalClass = new Type of HashTable

varietyDimension = method()
varietyDimension VarietyModel := ZZ => K -> dim K#"variety"

varietyEvidence = method()
varietyEvidence VarietyModel := HashTable => K -> K#"geometryEvidence"

serreShift = method()
serreShift VarietyModel := ZZ => K -> (varietyEvidence K)#"serreShift"

varietyCapabilities = method()
varietyCapabilities VarietyModel := HashTable => K -> K#"capabilities"

distinguishedObjects = method()
distinguishedObjects VarietyModel := List => K -> K#"distinguishedObjects"

numericalClass = method()
eulerPairing = method()
negateNumerical = method()
numericalTwistStep = method()
numericalReferenceFields = v -> if instance(v, MukaiClass) then {"mukaiClass" => v} else {"numericalClass" => v}
