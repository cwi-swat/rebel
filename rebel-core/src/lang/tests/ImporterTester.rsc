@license{
Copyright (c) 2016, CWI
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
@contributor{Jouke Stoel - jouke.stoel@cwi.nl - CWI}
module lang::tests::ImporterTester

import lang::Parser;
import lang::Syntax;

import lang::Importer;

import IO;
import Set;
import Message;

bool importAllTestFiles() = importAllFilesInDir(|project://rebel-core/tests|); 

bool importAllFilesInDir(loc dir) {
	bool successful = true;
	
	for (loc file <- dir.ls) {
		if (isDirectory(file)) {
			successful = successful && importAllFilesInDir(file);
		}
		else {
			if (file.extension == "ebl") {
				Module res = parseModule(file);
				tuple[set[Message], set[Module]] result = loadImports(res);

        if (result<0> == {}) {
				  println("Resolved all imports of \'<res.modDef.fqn>\', nr of imports: <size(result<1>)>");
				} else {
  				iprintln(result<0>);
	   			successful = false;
	   		}
			}
		}
	}
	
	return successful;
}

ImporterResult testImport(loc file) = loadImports(parseModule(file));