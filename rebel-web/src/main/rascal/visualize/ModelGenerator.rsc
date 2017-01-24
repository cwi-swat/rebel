@license{
Copyright (c) 2016, CWI
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
@contributor{Jouke Stoel - jouke.stoel@cwi.nl - CWI}
module visualize::ModelGenerator

import lang::ExtendedSyntax;
import lang::Builder;
import lang::Resolver;
import lang::Finder;

import visualize::ADT; 
import visualize::JavaScriptModelWriter;
import visualize::JsonUtil;

import IO;
import ValueIO;
import List;
import String;
import Map;
import util::Maybe; 
import ParseTree;

Maybe[JsSpec] generateForDynamic(loc file) = generateJsStructureOfInternals(file);

void generateForStatic(loc base, loc output) { 
	// step 1, generate the internal machines
	set[JsSpec] specs = generateJsStructuresOfInternals(base, {});
	
	println("Built the internal JS structure");
	
	// step 3, remove links to external machines that are not part of the generation
	specs = filterMissingLinks(specs);
	
	// step 4, generate json
	str jsJsonStringVar = asJsStringVar(specs);
	
	// step 5, save generated json
	writeFile(output, "var specs = <jsJsonStringVar>");
}

set[JsSpec] filterMissingLinks(set[JsSpec] specs) {
	bool imported(str specName, set[JsExternalMachine] ems) = true when /externalMachine(_, specName, _) := ems;
	default bool imported(str specName, set[JsExternalMachine] ems) = false;
	
	bool included(str fqn, set[JsSpec] specs) = true when /spec(fqn,_,_,_,_,_,_,_,_,_,_,_,_) := specs;
	default bool included(str fqn, set[JsSpec] specs) = false; 
	
	set[JsSpec] result = {};
	
	for (sp <- specs) {
		// the extended machine is not included
		sp.inheritsFrom = visit(sp.inheritsFrom) {
			case extends(str name, str fqn) => extends(name, "?") when !included(fqn, specs)
		}
	
		// a link to another specification is not included in the import
		set[JsExternalMachine] ems = sp.externalMachines;
		for (t <- sp.transitionsToExternalMachines, !imported(t.toMachine, ems)) {
			// a new external machine should be added to the set without a fqn
			ems += externalMachine("?", t.toMachine, outgoing());
		}
		
		// the imported specification could not be found in the set of ported specifications
		ems = visit(ems) {
			case externalMachine(str fqn, str name, JsReferenceType rt) => externalMachine("?", name, rt) when fqn != "?" && !included(fqn, specs)
		}
		
		result += spec(sp.fqn, sp.name, sp.doc, sp.modifier, sp.inheritsFrom, sp.extendedBy, sp.fields, sp.events, 
			sp.states, sp.transitions, ems, sp.transitionsToExternalMachines, sp.transitionsFromExternalMachines);	
	}
	
	return result;
}


set[JsSpec] generateJsStructuresOfInternals(loc base, set[JsSpec] result) {
	if (!exists(base)) {
		throw "Can only generate from an existing base directory";
	}	
	
	if (isFile(base) && base.extension == "ebl" && /just(JsSpec sp) := generateJsStructureOfInternals(base)) {
		result += sp; 
	} else if (isDirectory(base)) {
		result = (result | it + generateJsStructuresOfInternals(f, result) | f <- base.ls);
	}

	return result;
}

Maybe[JsSpec] generateJsStructureOfInternals(loc file) {
	println("Working on: <file>");

	tuple[set[Message], Maybe[Built]] model = load(file); 
	
	if (just(Built b) := model<1>, b.inlinedMod has spec) {
	  Module inlined = b.inlinedMod;
	
	  set[Built] imports = loadImports(b);
	  set[Built] referencedBy = loadSpecsRelyingOn(b);
	
		return just(spec(
				"<inlined.modDef.fqn>", 
				"<inlined.modDef.fqn.modName>",
				processSpecDoc(inlined), 
				processSpecModifier(inlined), 
				processExtends(inlined.spec, inlined.imports), 
				processExtendedBy("<inlined.modDef.fqn.modName>", b.usedBy),
				{field("<f.name>", "<f.tipe>") | /FieldDecl f := inlined.spec.fields}, 
				{event("<from.from>_<e.name>_<to.to>", 
					"<e.name>",
					processEventDoc(e),
					[withValue("<p.name>", "<p.tipe>", "<p.defaultValue>") | /Parameter p := e.configParams], 
					[typeOnly("<p.name>", "<p.tipe>") | /Parameter p := e.transitionParams], 
					processPreconditions(e), 
					processPostconditions(e), 
					processSyncBlock(e)) 
					| /StateFrom from := inlined.spec.lifeCycle, 
					  /StateTo to := from.destinations,
					  /VarName via := to.via, 
					  /EventDef e := inlined.spec.events,
					  "<e.name>" == "<via>"}, 
				{processState(state) | /StateFrom state := inlined.spec.lifeCycle}, 
				{trans("<from.from>", "<to.to>", "<from.from>_<via>_<to.to>") | /StateFrom from := inlined.spec.lifeCycle, /StateTo to := from.destinations, /VarName via := to.via}, 
				processExternalMachines(b, imports + referencedBy),  
				({} | it + processLinksToExternalMachines("<from.from>_<e.name>_<to.to>", e, b) | /StateFrom from := inlined.spec.lifeCycle, 
					  /StateTo to := from.destinations,
					  /VarName via := to.via, 
					  /EventDef e := inlined.spec.events,
					  "<e.name>" == "<via>"),
				({} | it + processLinksFromExternalMachines("<from.from>_<er.eventRef>_<to.to>", er, b, referencedBy) | /StateFrom from := inlined.spec.lifeCycle, 
            /StateTo to := from.destinations,
            /VarName via := to.via, 
            /EventRef er := inlined.spec.eventRefs,
            "<er.eventRef>" == "<via>")));
	} else {
		return nothing();
	}
}

bool inEventOfSpec(loc partOfEvent, Built b) = true
  when <loc ref, loc def> <- b.refs.eventRefs,
       contains(b.inlinedMod@\loc, ref),
       contains(def, partOfEvent);
default bool inEventOfSpec(loc partOfEvent, Built b) = false;

private set[JsTransition] processLinksFromExternalMachines(str eventId, EventRef er, Built b, set[Built] referencedBy ) {
  loc erLoc = er@\loc;
  
  return {transFromExternal("<other.inlinedMod.modDef.fqn>", "<callingEvnt.name>", eventId) | 
    Built other <- referencedBy,
    other.inlinedMod@\loc != b.inlinedMod@\loc,
    <loc ref, erLoc> <- other.refs.syncedEventRefs, 
    just(EventDef callingEvnt) := findInlinedEventDef(ref, referencedBy)}; 
}

private set[Built] loadImports(Built origin) = loadImports(origin, {});

private set[Built] loadImports(Built origin, set[Built] alreadyImported) {
  for (<loc ref, loc def> <- origin.refs.imports, ref < origin.inlinedMod@\loc) {
    if (<_, just(Built b)> := load(def.top), b notin alreadyImported) {
      alreadyImported += b;
      alreadyImported += loadImports(b, alreadyImported);
    }
  }
  
  return alreadyImported;
}

private set[Built] loadSpecsRelyingOn(Built origin) {
  set[Built] result = {};
  
  for(loc ub <- origin.usedBy) {
    if (<_, just(Built b)> := load(ub)) {
      if (b.inlinedMod has spec) {
        result += b;
      } else {
        result += loadSpecsRelyingOn(b); 
      }
    } 
  } 
  
  return result;
}

private set[JsInheritance] processExtendedBy(str parentSpec, set[loc] usedBy) =
  {extends("<b.inlinedMod.modDef.fqn.modName>", "<b.inlinedMod.modDef.fqn>") | loc ub <- usedBy, <_ , just(Built b)> := load(ub), b.inlinedMod has spec, /Extend ext := b.inlinedMod.spec, "<ext.parent>" == parentSpec};

private str processSpecDoc(Module spc) = processDoc(spc.spec.annos);
private str processEventDoc(EventDef evnt) = processDoc(evnt.annos);

private str processDoc(&T<:Tree t) = trim("<doc.contents>")
	when /(Annotation)`@doc <TagString doc>` := t; 
private default str processDoc(&T<:Tree t) = "";

private set[JsExternalMachine] processExternalMachines(Built current, set[Built] others) {
	set[tuple[str,str]] og = {<"<m.modDef.fqn>", "<m.spec.name>"> | 
	                                   <loc ref, loc def> <- current.refs.specRefs, 
	                                   inEventOfSpec(ref, current), 
	                                   just(Module m) := findInlinedSpec(def, others)};
	
	set[tuple[str,str]] ic = {<"<b.inlinedMod.modDef.fqn>", "<b.inlinedMod.spec.name>"> |
	                                   Built b <- others,
	                                   b.inlinedMod has spec,
	                                   <loc ref, loc def> <- b.refs.specRefs,
	                                   inEventOfSpec(ref, b),
	                                   contains(current.inlinedMod@\loc, def)};
	
	return {externalMachine(fqn, name, outgoing()) | e:<fqn, name> <- og, e notin ic} +
	       {externalMachine(fqn, name, incoming()) | e:<fqn, name> <- ic, e notin og} +
	       {externalMachine(fqn, name, both())     | e:<fqn, name> <- og, e in ic};
}
	
private set[JsTransition] processLinksToExternalMachines(str id, EventDef evnt, Built b) {
  str getFqnOfSpec(str specName) = "<imp.fqn>"
    when Import imp <- b.inlinedMod.imports,
         "<imp.fqn.modName>" == specName;  
  default str getFqnOfSpec(str specName) { throw "Spec with name \'<specName>\' is not imported"; }
  
  return {transToExternal(id, getFqnOfSpec("<specName>"), "<syncedEvnt>") | /(SyncExpr)`<TypeName specName>[<Expr _>].<VarName syncedEvnt>(<{Expr ","}* params>)` := evnt} +
	       {transToExternal(id, getFqnOfSpec("<specName>")) | /(Expr)`<TypeName specName>[<Expr _>]` := evnt.pre} +
	       {transToExternal(id, getFqnOfSpec("<specName>")) | /(Expr)`<TypeName specName>[<Expr _>]` := evnt.post};
}

private JsSpecModifier processSpecModifier(Module spc) = abstract() when /(SpecModifier)`abstract` := spc;
private JsSpecModifier processSpecModifier(Module spc) = external() when /(SpecModifier)`external` := spc;
private default JsSpecModifier processSpecModifier(Module spc) = noMod();

private JsInheritance processExtends(Specification spc, Import* imports) 
	= extends("<name>", "<parentMod>") 
	when 
		/Extend ext := spc,
		TypeName parentName := ext.parent.modName,
		/parentMod:(FullyQualifiedName)`<{VarName "."}+ _>.<TypeName name>` := imports && "<name>" == "<parentName>";
		
private default JsInheritance processExtends(Specification sp, Import* imp) = none();

private JsState processState((StateFrom)`<LifeCycleModifier? lcm> <VarName name> <StateTo* _>`) = initialState("<name>") when "<lcm>" == "initial";
private JsState processState((StateFrom)`<LifeCycleModifier? lcm> <VarName name> <StateTo* _>`) = finalState("<name>") when "<lcm>" == "final";
private default JsState processState((StateFrom)`<LifeCycleModifier? lcm> <VarName name> <StateTo* _>`) = state("<name>");

private list[JsStatement] processPreconditions(EventDef e) = [processToText(stat) | /Statement stat := e.pre];
private list[JsStatement] processPostconditions(EventDef e) = [processToText(stat) | /Statement stat := e.post];
private list[JsStatement] processSyncBlock(EventDef e) = [processToText(stat) | /SyncStatement stat := e.sync];

private JsStatement processToText((SyncStatement)`<Annotations annos><TypeName specName>[<Expr id>].<VarName event>(<{Expr ","}* params>);`) =
  (/(Annotation)`@doc<TagString doc>` := annos) ? docAndCode("<doc.contents>", "<specName>[<id>].<event>(<params>)") : codeOnly("<specName>[<id>].<event>(<params>)");

private JsStatement processToText((SyncStatement)`<Annotations annos> not <TypeName specName>[<Expr id>].<VarName event>(<{Expr ","}* params>);`) =
  (/(Annotation)`@doc<TagString doc>` := annos) ? docAndCode("<doc.contents>", "<specName>[<id>].<event>(<params>)") : codeOnly("<specName>[<id>].<event>(<params>)");

private JsStatement processToText((Statement)`@doc <TagString doc> <Expr e>;`) = docAndCode("<doc.contents>", "<e>");
private default JsStatement processToText(Statement stat) = codeOnly("<stat>");
