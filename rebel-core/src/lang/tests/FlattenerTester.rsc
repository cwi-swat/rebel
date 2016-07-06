module lang::tests::FlattenerTester

import lang::Flattener;

import lang::Parser;
import lang::Importer;
import lang::Syntax;

import IO;

Module testFlattenModule(loc file) {
	Module modul = parseModule(file);
	
	return flatten(modul, loadImports(modul));
}

Module testFlattenModule() = testFlattenModule(|project://rebel-core/tests/account/saving/SimpleSavings.ebl|);