module visualize::tests::ModelGeneratorTester

import visualize::ModelGenerator;
import visualize::ADT;

import util::Maybe;


Maybe[JsSpec] generate() = generate(|project://rebel-core/tests/account/saving/SimpleSavings.ebl|);
Maybe[JsSpec] generate(loc file) = generateJsStructureOfInternals(file);