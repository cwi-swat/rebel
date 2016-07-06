module lang::Importer

import lang::Syntax;
import lang::Parser;

import String;
import IO;
import List;

import ParseTree;

set[Module] loadImports(Module m) = loadImports(m, {}, resolveBaseDir(m));

private set[Module] loadImports(Module m, set[str] imported, loc baseDir) {
	set[Module] importedModules = {m};
		
	for (imp <- m.imports, "<imp.fqn>" notin imported) {
		try {	
			Module current = parseModule(findFile(imp.fqn, baseDir));
			imported += "<current.modDef.fqn>";
			importedModules += loadImports(current, imported, baseDir);
		} 
		catch ParseError(loc l): println("ParseError while parsing: <l>"); 
		catch IO(str msg): println("Unable to load import: <msg>");
	}
	
	return importedModules;
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
