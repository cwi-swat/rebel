module lang::tests::ImporterTester

import lang::Parser;
import lang::Syntax;

import lang::Importer;

import IO;
import Set;

bool importAllTestFiles() = importAllFilesInDir(|project://rebel-core/tests|); 

bool importAllFilesInDir(loc dir) {
	bool successful = true;
	
	for (loc file <- dir.ls) {
		if (isDirectory(file)) {
			successful = successful && importAllFilesInDir(file);
		}
		else {
			try {
				if (file.extension == "ebl") {
					Module res = parseModule(file);
					set[Module] imports = loadImports(res);
					println("Resolved all imports of \'<res.modDef.fqn>\', nr of imports: <size(imports)>");
				}
			} catch ex: {
				println("Somthing went wrong during importing: <ex>");
				successful = false;
			}
		}
	}
	
	return successful;
}

set[Module] testImport(loc file) = loadImports(parseModule(file));