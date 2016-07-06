module lang::tests::NormalizerTest

import lang::Parser;
import lang::Importer;
import lang::Resolver;
import lang::Flattener;

import lang::Normalizer;
import lang::Syntax;

import IO;
import ValueIO;
import util::ValueUI;

Module testNormalizeSpec(loc file) = normalize(spc, imports, refs)
	when	Module spc := parseModule(file),
			set[Module] imports := loadImports(spc),
			Refs refs := resolve({spc} + imports);

Module testNormalizeSpec() = testNormalizeSpec(|project://rebel-core/tests/account/saving/SimpleSavings.ebl|);

Module testInlining(loc file) = inline(spc, imports, refs)
	when	Module spc := parseModule(file),
			set[Module] imports := loadImports(spc),
			Refs refs := resolve({spc} + imports);
