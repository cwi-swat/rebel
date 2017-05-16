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
import util::Maybe;

data Refs = refs(Reff imports, 
				         Reff eventRefs, 
				         Reff functionRefs, 
				         Reff invariantRefs, 
				         Reff lifeCycleRefs, 
				         Reff stateRefs, 
				         Reff keywordRefs, 
				         Reff inheritance,
				         Reff syncedEventRefs,
				         Reff specRefs);
				    
alias Reff = rel[loc from, loc to]; 

Refs resolve(Module current, set[Module] imports) =
	   refs(resolveImports(current, imports), 
		      resolveEventReferences(current, imports),
		      resolveFunctionReferences(current + imports),
		      resolveInvariantReferences(current, imports),
		      resolveLifeCycleEventReferences(current + imports),
		      resolveLifeCycleStateReferences(current + imports) + resolveInStateReferences(current + imports),
		      resolveKeywordReferences(current, imports),	
		      resolveInheritance(current + imports),
		      resolveSyncedEventReferences(current + imports),
          resolveReferencedSpecifications(current + imports));

Reff resolveImports(Module current, set[Module] imports) {
  map[str, Module] moduleNames = ("<m.modDef.fqn>":m | m <- imports);
  Reff resolveImportsInt(Module m) = {<imp.fqn@\loc, moduleNames["<imp.fqn>"]@\loc> | Import imp <- current.imports, "<imp.fqn>" in moduleNames}; 
  
  Reff result = resolveImportsInt(current);
  if (current has spec) {
    //also add the imports of the lib modules
    for (Import imp <- current.imports, "<imp.fqn>" in moduleNames, Module def := moduleNames["<imp.fqn>"], def has decls) {
      result += resolveImportsInt(def);
    }
  }
  
  return result;
} 
   
Reff resolveEventReferences(Module current, set[Module] imports) {	
	Reff refs = {};
	if (/Specification s := current, s has optEventRefs) { 
		defs = ("<def.name>" : def@\loc | EventDef def <- allEventDefs(imports));
		
		refs += {<r@\loc, defs["<event>"]> | /r:ref(FullyQualifiedVarName event, _) := s.optEventRefs, "<event>" in defs};
	}
	
	return refs;
}

Reff resolveFunctionReferences(set[Module] modules) {
	map[str,loc] buildFunctionDef(EventConfigBlock? config) =
		("<name>" : name@\loc | /(Parameter)`<VarName name> : <Type _> -\> <Type _>` := config) +
		("<name>" : name@\loc | /(Parameter)`<VarName name> : <Type _> -\> <Type _> = <Expr _>` := config);

	map[str, loc] buildFunctionRefMapInKeywordParams(EventRef er) =
		("<val>" : val@\loc | /(ConfigParameter)`<VarName name> = <Expr val>` := er);

	Reff refs = {};
	
	for (m <- modules) {
		set[Module] imports = {m} + importedModules(m, modules);
		defs = ("<def.name>" : def@\loc | FunctionDef def <- allFunctionDefs(imports));

    // Find all the function calls
    refs += {<f@\loc, defs["<func>"]> | f:(Expr)`<VarName func>(<{Expr ","}* _>)` <- allFunctionCalls(imports), "<func>" in defs};
		
		// Find the block scoped function pointers in event config	
		for (/EventDef e := m) {
			scopedDefs = buildFunctionDef(e.configParams);
			refs += {<r@\loc, scopedDefs["<func>"]> | /r:(Expr)`<VarName func>(<{Expr ","}* _>)` := e, "<func>" in scopedDefs};  
				
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

Reff resolveKeywordReferences(Module current, set[Module] imports) {
	Reff refs = {};
	
	if (current has spec) {
		defs = ("<def.name>" : def | EventDef def <- allEventDefs(imports));
	
		for (/EventRef er := current.spec.optEventRefs, er has eventRef, "<er.eventRef>" in defs) {
			refs += {<p@\loc, cp@\loc> | ConfigParameter cp <- er.config, /EventConfigBlock ecb := defs["<er.eventRef>"].configParams, Parameter p <- ecb.params, "<p.name>" == "<cp.name>" }; 			
		}
	}

	return refs;
}

Reff resolveInvariantReferences(Module current, set[Module] imports) {
	Reff refs = {};
	
	for (current has spec) {
		set[Module] libMods = allLibraryModules(imports);
		map[str, loc] defs = ("<def.name>" : def@\loc | Module lib <- libMods, /InvariantDef def <- lib.decls);
		refs += {<inv@\loc, defs["<inv>"]> | /InvariantRefs ref := current.spec.optInvariantRefs, /FullyQualifiedVarName inv := ref, "<inv>" in defs };
	}

	return refs;
}

Reff resolveLifeCycleEventReferences(set[Module] modules) {
	Reff refs = {};
	
	for (m <- modules) {
		if (m has spec) {
			set[Module] chain = {m} + findParents(m, modules); 
			map[str, loc] defs = ("<def.eventRef>" : def@\loc | EventRef def <- allEventRefs(chain), def has eventRef);
			
			refs += {<event@\loc, defs["<event>"]> | /LifeCycle lc := m.spec.optLifeCycle, StateFrom sf <- lc.from, StateTo st <- sf.destinations, VarName event <- st.via.refs, "<event>" in defs};
		}
	}
	 
	return refs;
}

Reff resolveLifeCycleStateReferences(set[Module] modules) {
	Reff refs = {};
	
	for (current <- modules, current has spec) {
		set[Module] chain = {current} + findParents(current, modules); 
		map[str, loc] defs = ("<sf.from>" : sf.from@\loc | Module m <- chain, /LifeCycle lc := m.spec.optLifeCycle, StateFrom sf <- lc.from);
		
		refs += {<st.to@\loc, defs["<st.to>"]> | Module m <- chain, /LifeCycle lc := m.spec.optLifeCycle, StateFrom sf <- lc.from, StateTo st <- sf.destinations, "<st.to>" in defs};
	}
	 
	return refs;
}

Reff resolveInStateReferences(set[Module] modules) { 
  Reff refs = {};
  
  map[str, loc] defs = ("<m.modDef.fqn>.<sf.from>" : sf@\loc | Module m <- modules, m has spec, /LifeCycle lc := m.spec.optLifeCycle, StateFrom sf <- lc.from);
  map[str, str] fqnLookup = ("<m.spec.name>" : "<m.modDef.fqn>"  | m <- modules, m has spec);
 
  
  for (Module libMod <- modules, libMod has decls, /EventDef evnt := libMod.decls, /(Expr)`<Expr spc>[<Expr _>] instate <StateRef sr>` := evnt, "<spc>" in fqnLookup, /(StateRef)`<VarName state>` := sr, "<fqnLookup["<spc>"]>.<state>" in defs) {
    refs += <sr@\loc, defs["<fqnLookup["<spc>"]>.<sr>"]>;
  } 
  for (Module libMod <- modules, libMod has decls, /EventDef evnt := libMod.decls, /(Expr)`new <Expr spc>[<Expr _>] instate <StateRef sr>` := evnt, "<spc>" in fqnLookup, /(StateRef)`<VarName state>` := sr, "<fqnLookup["<spc>"]>.<state>" in defs) {
    refs += <sr@\loc, defs["<fqnLookup["<spc>"]>.<sr>"]>;
  } 
  
  return refs;
} 

Reff resolveInheritance(set[Module] modules) {
	Reff refs = {}; 
	
	for (m <- allSpecificationModules(modules), 
		/Extend ext := m.spec.\extend, 
		/Import imp := m, 
		"<imp.fqn.modName>" == "<ext.parent>",
		m2 <- modules, 
		"<m2.modDef.fqn>" == "<imp.fqn>") {
		
		refs += {<ext.parent@\loc, m2@\loc>};
	}
	return refs; 	
}

Reff resolveSyncedEventReferences(set[Module] modules) {
  Reff ref = {};
 
  set[Module] libModules = allLibraryModules(modules);
  
  for (Module libMod <- libModules, /EventDef evnt := libMod.decls) { 
    for (/SyncBlock sb := evnt.sync, SyncStatement syncStat <- sb.stats, /(SyncExpr)`<TypeName specName>[<Expr id>].<VarName event>(<{Expr ","}* params>)` := syncStat) {
      if (Module m <- allSpecificationModules(importedModules(libMod, modules)), "<m.spec.name>" == "<specName>", /EventRef er := m.spec.optEventRefs, er has eventRef, "<er.eventRef>" == "<event>") {
        ref += <event@\loc, er@\loc>; 
      } 
    }
  }
  
  return ref;
}

Reff resolveReferencedSpecifications(set[Module] modules) {
  Reff ref = {};
  
  Reff checkStats(Statement* stats, Module libMod) {
    Reff intRef = {};
    
    for (/(Expr)`<TypeName specName>[<Expr _>]` := stats) {
      if (Module m <- allSpecificationModules(importedModules(libMod, modules)), "<m.spec.name>" == "<specName>") {
        intRef += <specName@\loc, m.spec@\loc>;
      }
    }
    
    return intRef;
  }
  
  set[Module] libModules = allLibraryModules(modules);
  
  for(Module libMod <- libModules, /EventDef evnt := libMod.decls) {
    for (/SyncBlock sb := evnt.sync, SyncStatement syncStat <- sb.stats, /(SyncExpr)`<TypeName specName>[<Expr _>].<VarName _>(<{Expr ","}* _>)` := syncStat) {
      if (Module m <- allSpecificationModules(importedModules(libMod, modules)), "<m.spec.name>" == "<specName>") {
        ref += <specName@\loc, m.spec@\loc>;
      }
    }
    
    if (/Statement* stats := evnt.pre) {
      ref += checkStats(stats, libMod);
    } 
    if (/Statement* stats := evnt.post) {
      ref += checkStats(stats, libMod);
    }
      
  }  
  
  return ref;
}

Maybe[EventDef] findEventDef(loc eventLoc, set[Module] modules) {
  if (Module m <- modules, eventLoc.top == m@\loc.top, m has decls, /EventDef evnt := m.decls, evnt@\loc == eventLoc) {
    return just(evnt);
  }
  
  return nothing(); 
} 

@memo
private set[Module] importedModules(Module moi, set[Module] allMods) {
  set[str] impModNames = {"<imp.fqn>" | imp <- moi.imports};
  return {imp | imp <- allMods, "<imp.modDef.fqn>" in impModNames};
}

@memo 
private set[Module] allLibraryModules(set[Module] mods) =
  {m | Module m <- mods, m has decls};
  
@memo
set[Module] allSpecificationModules(set[Module] mods) =
  {m | Module m <- mods, m has spec};

@memo
set[EventDef] allEventDefs(set[Module] mods) =
  {e | Module m <- allLibraryModules(mods), /EventDef e <- m.decls};

@memo
set[EventRef] allEventRefs(set[Module] mods) =
  {er | Module m <- allSpecificationModules(mods), /EventRef er <- m.spec.optEventRefs};

@memo
set[FunctionDef] allFunctionDefs(set[Module] mods) =
  {f | Module m <- allLibraryModules(mods), /FunctionDef f <- m.decls};

set[Expr] allFunctionCalls(set[Module] mods) =
  {fc | EventDef evnt <- allEventDefs(mods), /fc:(Expr)`<VarName func>(<{Expr ","}* _>)` := evnt.pre} +
  {fc | EventDef evnt <- allEventDefs(mods), /fc:(Expr)`<VarName func>(<{Expr ","}* _>)` := evnt.post} +
  {fc | FunctionDef f <- allFunctionDefs(mods), /fc:(Expr)`<VarName func>(<{Expr ","}* _>)` := f.statement}; 

@memo
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
