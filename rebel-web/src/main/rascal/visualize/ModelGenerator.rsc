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

Maybe[JsSpec] generateForDynamic(loc file) {
  return generateJsStructureOfInternals(file);
}

void generateForStatic(loc base, loc output) { 
	// step 1, generate the internal machines
	set[JsSpec] specs = generateJsStructuresOfInternals(base, {});
	
	// step 2, augment with incoming links
	specs = {augmentWithIncomingExternalMachinesAndLinks(spc, specs) | spc <- specs};
	
	// step 3, link external machines
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
		for (t <- sp.transitionsToExternal, !imported(t.toMachine, ems)) {
			// a new external machine should be added to the set without a fqn
			ems += externalMachine("?", t.toMachine, outgoing());
		}
		
		// the imported specification could not be found in the set of ported specifications
		ems = visit(ems) {
			case externalMachine(str fqn, str name, JsReferenceType rt) => externalMachine("?", name, rt) when fqn != "?" && !included(fqn, specs)
		}
		
		result += spec(sp.fqn, sp.name, sp.doc, sp.modifier, sp.inheritsFrom, sp.extendedBy, sp.fields, sp.events, 
			sp.states, sp.transitions, ems, sp.transitionsToExternal, sp.transitionsFromExternal);	
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

JsSpec augmentWithIncomingExternalMachinesAndLinks(JsSpec subject, set[JsSpec] allSpecs) {
	str name = subject.name;
	str fqn = subject.fqn;
		
	set[JsSpec] machinesWithLinksToSubject = {spc | JsSpec spc <- allSpecs, /externalMachine(fqn, name, _) := spc};
	set[str] fqnOfIncomingLinks = {spc.fqn | spc <- machinesWithLinksToSubject};
	set[str] fqnOfOutgoingLinks = {em.fqn | em <- subject.externalMachines};
		
	set[JsTransition] incomingTransitions = {transFromExternal(spc.name, fromEvent, id) | JsSpec spc <- machinesWithLinksToSubject, 
		/transToExternal(str fromEvent, name, str toEvent) := spc.transitionsToExternal,
		/event(str id, toEvent, _,_,_,_,_,_) := subject};
	
	set[JsExternalMachine] merged = {em | em <- subject.externalMachines, em.fqn notin fqnOfIncomingLinks} + 
		{externalMachine(spc.fqn, spc.name, incoming()) | JsSpec spc <- machinesWithLinksToSubject, spc.fqn notin fqnOfOutgoingLinks} +
		{externalMachine(spc.fqn, spc.name, both()) | JsSpec spc <- machinesWithLinksToSubject, spc.fqn in fqnOfIncomingLinks && spc.fqn in fqnOfOutgoingLinks};
	
	return spec(subject.fqn, subject.name, subject.doc, subject.modifier, subject.inheritsFrom, 
		subject.extendedBy, subject.fields, subject.events, subject.states, subject.transitions, 
		merged, subject.transitionsToExternal, incomingTransitions);
}

Maybe[JsSpec] generateJsStructureOfInternals(loc file) {
	println("Working on: <file>");

	tuple[set[Message], Maybe[Built]] model = load(file); 
	
	if (just(Built b) := model<1>, b.inlinedMod has spec) {
	  Module inlined = b.inlinedMod;
	
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
				processExternalMachines(b, loadImports(b) + loadSpecsRelyingOn(b)),  
				({} | it + processLinksToExternalMachines("<from.from>_<e.name>_<to.to>", e) | /StateFrom from := inlined.spec.lifeCycle, 
					  /StateTo to := from.destinations,
					  /VarName via := to.via, 
					  /EventDef e := inlined.spec.events,
					  "<e.name>" == "<via>"),
				processLinksFromExternalMachines(b, loadSpecsRelyingOn(b))));
	} else {
		return nothing();
	}
}

private Maybe[EventDef] findEventDef(loc evntToFind, set[Built] builds) {
  if (Built b <- builds, Module m := b.inlinedMod, m.modDef.fqn.modName@\loc.top > evntToFind, m has spec, EventDef evnt <- m.spec.events.events, evnt@\loc > evntToFind) {
    return just(evnt);
  } else {
    return nothing();
  } 
} 

private Maybe[EventRef] findEventRef(loc evntToFind, set[Built] builds) {
  if (Built b <- builds, Module m := b.inlinedMod, m@\loc > evntToFind, m has spec, EventRef evnt <- m.spec.eventRefs.events, evnt@\loc == evntToFind) {
    return just(evnt);
  } else {
    return nothing();
  } 
} 

private set[JsTransition] processLinksFromExternalMachines(Built orig, set[Built] otherSpecs) =
  {transFromExternal("<other.inlinedMod.modDef.fqn.modName>", "<callingEvnt.name>", "<syncedEvnt.eventRef>") | 
    Built other <- otherSpecs, 
    <loc ref, loc def> <- other.refs.syncedEventRefs, 
    just(EventDef callingEvnt) := findEventDef(ref, otherSpecs),
    just(EventRef syncedEvnt) := findEventRef(def, {orig})}; 

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

private Maybe[Module] findSpec(loc specDef, set[Built] mods) {
  println("Trying to find <specDef>");
  
  if (Built b <- mods, b.inlinedMod has spec, bprintln("Specdef of current mod = <b.inlinedMod.spec@\loc>"), b.inlinedMod.spec@\loc == specDef) {
    return just(b.inlinedMod);
  }
  else {
    return nothing();
  }
} 

private set[JsExternalMachine] processExternalMachines(Built current, set[Built] others) {
	bool inEventOfSpec(loc partOfEvent, Built b) = true
	  when <loc ref, loc def> <- b.refs.eventRefs,
	       ref < b.inlinedMod@\loc,
	       partOfEvent < def;
  default bool inEventOfSpec(loc partOfEvent, Built b) = false;
  	
	set[tuple[str,str]] og = {<"<m.modDef.fqn>", "<m.spec.name>"> | 
	                                   <loc ref, loc def> <- current.refs.specRefs, 
	                                   inEventOfSpec(ref, current), 
	                                   just(Module m) := findSpec(def, others)};
	
	set[tuple[str,str]] ic = {<"<b.inlinedMod.modDef.fqn>", "<b.inlinedMod.spec.name>"> |
	                                   Built b <- others,
	                                   b has spec,
	                                   <loc ref, loc def> <- b.refs.specRefs,
	                                   inEventOfSpec(ref, b),
	                                   def < current.inlinedMod@\loc};
	
	return {externalMachine(fqn, name, outgoing()) | e:<fqn, name> <- og, e notin ic} +
	       {externalMachine(fqn, name, incoming()) | e:<fqn, name> <- ic, e notin og} +
	       {externalMachine(fqn, name, both())     | e:<fqn, name> <- og, e in ic};
}
	
private set[JsTransition] processLinksToExternalMachines(str id, EventDef evnt) =
		{transToExternal(id, "<specName>", "<syncedEvnt>") | /(SyncExpr)`<TypeName specName>[<Expr _>].<VarName syncedEvnt>(<{Expr ","}* params>)` := evnt} +
		{transToExternal(id, "<specName>") | /(Expr)`<TypeName specName>[<Expr _>]` := evnt.pre} +
		{transToExternal(id, "<specName>") | /(Expr)`<TypeName specName>[<Expr _>]` := evnt.post};

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
