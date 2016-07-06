@license{
Copyright (c) 2016, CWI
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
@contributor{Jouke Stoel - jouke.stoel@cwi.nl - CWI}
module lang::Resolver

import lang::Syntax;

import IO;
import ParseTree;

data Refs = refs(Ref imports, 
				 Ref eventRefs, 
				 Ref functionRefs, 
				 Ref invariantRefs, 
				 Ref lifeCycleRefs, 
				 Ref stateRefs, 
				 Ref keywordRefs, 
				 Ref inheritance, 
				 Ref specRefs);
				   
alias Ref = rel[loc from, loc to];

Refs resolve(set[Module] modules) =
	refs(resolveImports(modules), 
		 resolveEventReferences(modules),
		 resolveFunctionReferences(modules),
		 resolveInvariantReferences(modules),
		 resolveLifeCycleEventReferences(modules),
		 resolveLifeCycleStateReferences(modules),
		 resolveKeywordReferences(modules),	
		 resolveInheritance(modules),
		 resolveSpecRefs(modules));

Ref resolveImports(set[Module] modules) {
	moduleNames = ("<m.modDef.fqn>":m@\loc | m <- modules);
	return {<i.fqn@\loc, moduleNames["<i.fqn>"]> | current <- modules, /Import i := current.imports, "<i.fqn>" in moduleNames};
}

private set[Module] importedModules(Module moi, set[Module] allMods) {
	set[str] impModNames = {"<imp.fqn>" | imp <- moi.imports};
	return {imp | imp <- allMods, "<imp.modDef.fqn>" in impModNames};
}

Ref resolveEventReferences(set[Module] modules) {	
	Ref refs = {};
	for (m <- modules, /Specification s := m) {
		set[Module] imports = importedModules(m, modules);
		defs = ("<def.name>" : def@\loc | /EventDef def := imports);
		
		refs += {<ref@\loc, defs["<ref.eventRef>"]> | /EventRef ref := m, "<ref.eventRef>" in defs};
	}
	
	return refs;
}

Ref resolveFunctionReferences(set[Module] modules) {
	map[str,loc] buildFunctionDef(EventConfigBlock? config) =
		("<name>" : name@\loc | /(Parameter)`<VarName name> : <Type _> -\> <Type _>` := config) +
		("<name>" : name@\loc | /(Parameter)`<VarName name> : <Type _> -\> <Type _> = <Expr _>` := config);

	map[str, loc] buildFunctionRefMapInKeywordParams(EventRef er) =
		("<val>" : val@\loc | /(ConfigParameter)`<VarName name> = <Expr val>` := er);

	Ref refs = {};
	
	for (m <- modules) {
		set[Module] imports = {m} + importedModules(m, modules);
		defs = ("<def.name>" : def@\loc | /FunctionDef def := imports);

		// Find all the function calls
		refs += {<ref@\loc, defs["<func>"]> | /ref:(Expr)`<VarName func>(<{Expr ","}* _>)` := imports, "<func>" in defs};
		
		// Find the block scoped function pointers in event config	
		for (/EventDef e := m) {
			scopedDefs = buildFunctionDef(e.configParams);
			refs += {<ref@\loc, scopedDefs["<func>"]> | /ref:(Expr)`<VarName func>(<{Expr ","}* _>)` := e, "<func>" in scopedDefs};  
				
			// also the default values of the config parameters could point to a function
			refs += {<val@\loc, defs["<val>"]> | /(Parameter)`<VarName _> : <Type _> -\> <Type _> = <Expr val>` := e.configParams, "<val>" in defs};
		}
		
		// Resolve the functions referenced in the keyword parameters
		for (/EventRef er := m) {
			paramRefs = buildFunctionRefMapInKeywordParams(er);
			refs += {<paramRefs[r], defs[r]> | r <- paramRefs, r in defs};
		}
	}
		
	return refs;
}

Ref resolveKeywordReferences(set[Module] modules) {
	Ref refs = {};
	
	for (m <- modules, /Specification s := m) {
		set[Module] imports = importedModules(m, modules);
		defs = ("<def.name>" : def | /EventDef def := imports);
	
		for (/EventRef er := m, "<er.eventRef>" in defs) {
			refs += {<p@\loc, cp@\loc> | /ConfigParameter p := er, /Parameter cp := defs["<er.eventRef>"].configParams, "<p.name>" == "<cp.name>" }; 			
		}
	}

	return refs;
}

Ref resolveInvariantReferences(set[Module] modules) {
	Ref refs = {};
	
	for (m <- modules, /Specification s := m) {
		set[Module] imports = importedModules(m, modules);
		map[str, loc] defs = ("<def.name>" : def@\loc | /InvariantDef def := imports);
		refs += {<inv@\loc, defs["<inv>"]> | /InvariantRefs ref := s, /VarName inv := ref, "<inv>" in defs };
	}
	

	return refs;
}

Ref resolveLifeCycleEventReferences(set[Module] modules) {
	Ref refs = {};
	
	for (m <- modules) {
		if (/Specification s := m) {
			set[Module] chain = {m} + findParents(m, modules); 
			map[str, loc] defs = ("<def.eventRef>" : def@\loc | /EventRef def := chain);
			
			refs += {<event@\loc, defs["<event>"]> | /StateVia ref := m, /VarName event := ref, "<event>" in defs};
		}
	}
	
	return refs;
}

Ref resolveLifeCycleStateReferences(set[Module] modules) {
	Ref refs = {};
	
	for (m <- modules, /Specification s := m) {
		set[Module] chain = {m} + findParents(m, modules); 
		map[str, loc] defs = ("<st.from>" : st.from@\loc | /StateFrom st := chain);
		
		refs += {<ref.to@\loc, defs["<ref.to>"]> | /StateTo ref := m, "<ref.to>" in defs};
	}
	
	return refs;
}

Ref resolveInheritance(set[Module] modules) {
	Ref refs = {};
	
	for (m <- modules, 
		/Extend ext := m, 
		/Import imp := m, 
		"<imp.fqn.modName>" == "<ext.parent>",
		m2 <- modules, 
		"<m2.modDef.fqn>" == "<imp.fqn>") {
		
		refs += {<ext.parent@\loc, m2@\loc>};
	}
	return refs; 	
}

Ref resolveSpecRefs(set[Module] modules) {
	map[str,loc] specNames = 
		("<spc.name>":spc@\loc | /Specification spc := modules);
	
	set[str] importedSpecModules(Module modul) =  
		{"<imp.fqn.modName>" | /Import imp := modul.imports, "<imp.fqn.modName>" in specNames};		

	Ref refs = {};

	for (m <- modules) {
		set[str] impSpecModules = importedSpecModules(m);

		for (/EventDef evnt := m,  /ref:(Ref)`<FullyQualifiedName name>` := evnt, "<name>" in impSpecModules) {
			refs += {<ref@\loc, specNames["<name>"]>};
		}
	}
	
	return refs;
}

Ref resolveSyncedEventRefs(set[Module] modules) {
	//	
}

private set[Module] findParents(Module current, set[Module] modules) {
	if (/Extend ext := current) {
		if (/Import imp := current, "<imp.fqn.modName>" == "<ext.parent>") {
			for(Module m <- modules, "<m.modDef.fqn>" == "<imp.fqn>") {
				return {m} + findParents(m, modules);
			}
			
			return {};
		} else {
			return {};
		}
	} else {
		return {};
	}
}
