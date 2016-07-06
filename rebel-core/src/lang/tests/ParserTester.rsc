module lang::tests::ParserTester

import lang::Parser;
import lang::Syntax;

import IO;
import ParseTree;

bool parseAllTestFilesAndCheckForAmbiguity() =
	parseFilesInDirAndCheckForAmbiguity(|project://rebel-core/tests|);

bool parseFilesInDirAndCheckForAmbiguity(loc dir) {
	bool successful = true;
	
	for (loc file <- dir.ls) {
		if (isDirectory(file)) {
			successful = successful && parseFilesInDirAndCheckForAmbiguity(file);
		}
		else {
			try {
				if (file.extension == "ebl") {
					Tree res = parseModule(file);
			
					if (just(_) := isAmbiguous(res)) {
						println("Ambiguity found in: <file>");
						successful = false;
					}
				}
			} catch ex: {
				println("Somthing went wrong during parsing \'<file>\': <ex>");
				successful = false;
			}
		}
	}
	
	return successful;
}