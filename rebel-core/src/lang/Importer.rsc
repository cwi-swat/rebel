@license{
Copyright (c) 2016, CWI
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
@contributor{Jouke Stoel - jouke.stoel@cwi.nl - CWI}
module lang::Importer

import lang::Syntax;
import lang::Parser;

import String;
import IO;
import List;
import Message;
import ParseTree;

alias ImporterResult = tuple[set[Message] msgs, set[Module] mods]; 

ImporterResult loadImports(Module m) = loadImports(m, resolveBaseDir(m));

private ImporterResult loadImports(Module initial, loc baseDir) {
	set[Message] msgs = {};
	map[str,Module] importedModules = ();
	
	void recursiveLoad(Module modul) {
    importedModules += ("<modul.modDef.fqn>":modul);
	
    for (imp <- modul.imports, "<imp.fqn>" notin importedModules<0>) {
      try { 
        Module current = parseModule(findFile(imp.fqn, baseDir));
        recursiveLoad(current);
      }  
      catch ParseError(loc l): msgs += error("ParseError while parsing: <l>", imp@\loc); 
      catch IO(str msg): msgs += error("Unable to load import: <msg>", imp@\loc);
	  }
	}	
	
	recursiveLoad(initial);
	
	return <msgs, importedModules<1>>;
}

private loc resolveBaseDir(Module m) {
	loc base = m@\loc.top.parent;
	
	for (package <- reverse(["<p>" | /VarName p := m.modDef.fqn]), endsWith(base.path, "<package>")) {
		base = base.parent;
	}
	
	return base;
}

private str toPath(FullyQualifiedName n) = "<("" | "<it><p>/" | /VarName p := n)><n.modName>";	
	
private loc findFile(FullyQualifiedName n, loc baseDir) = baseDir + "/<toPath(n)>.ebl";
