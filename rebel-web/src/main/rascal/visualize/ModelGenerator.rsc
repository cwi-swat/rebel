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

//import lang::Parser;
//import lang::Flattener;
//import lang::Importer;
//import lang::Resolver;
//import lang::Normalizer;
import lang::ExtendedSyntax;
import lang::Builder;

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

void toJs(loc base, loc output) { 
	// step 1, generate the internal machines
	set[JsSpec] specs = generateJsStructuresOfInternals(base, {});
	
	// step 2, augment with incoming links
	specs = {augmentWithIncomingExternalMachinesAndLinks(spc, specs) | spc <- specs};
	 
	// step 3, add extendedBy relations
	specs = {augmentWithExtendedByRelations(spc, specs) | spc <- specs};
	
	// step 3, link external machines
	specs = filterMissingLinks(specs);
	
	// step 4, generate json
	str jsJsonStringVar = asJsStringVar(specs);
	
	// step 5, save generated json
	writeFile(output, "var specs = <jsJsonStringVar>");
}

set[JsSpec] filterMissingLinks(set[JsSpec] specs) {
	bool imported(str specName, set[JsExternalMachine] ems) = true when /jsEM(_, specName, _) := ems;
	default bool imported(str specName, set[JsExternalMachine] ems) = false;
	
	bool included(str fqn, set[JsSpec] specs) = true when /jsSpec(fqn,_,_,_,_,_,_,_,_,_,_,_,_) := specs;
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
			ems += jsEM("?", t.toMachine, outgoing());
		}
		
		// the imported specification could not be found in the set of ported specifications
		ems = visit(ems) {
			case jsEM(str fqn, str name, JsReferenceType rt) => jsEM("?", name, rt) when fqn != "?" && !included(fqn, specs)
		}
		
		result += jsSpec(sp.fqn, sp.name, sp.doc, sp.specMod, sp.inheritsFrom, sp.extendedBy, sp.fields, sp.events, 
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

JsSpec augmentWithExtendedByRelations(jsSpec(str fqn, str name, str doc, JsSpecModifier specMod, JsInheritance inheritsFrom, 
		set[JsInheritance] _, set[JsField] fields, set[JsEvent] events, set[JsState] states, 
		set[JsTransition] transitions, set[JsExternalMachine] externalMachines, 
		set[JsTransition] transitionsToExternal, set[JsTransition] transitionsFromExternal), set[JsSpec] allSpecs) = 
	jsSpec(fqn, name, doc, specMod, inheritsFrom, extendedBy, fields, events, states, transitions, externalMachines, transitionsToExternal, transitionsFromExternal)
		when 
			set[JsInheritance] extendedBy := {extends(spc.name, spc.fqn) | JsSpec spc <- allSpecs, extends(name, fqn) := spc.inheritsFrom};

JsSpec augmentWithIncomingExternalMachinesAndLinks(JsSpec subject, set[JsSpec] allSpecs) {
	str name = subject.name;
	str fqn = subject.fqn;
		
	set[JsSpec] machinesWithLinksToSubject = {spc | JsSpec spc <- allSpecs, /jsEM(fqn, name, _) := spc};
	set[str] fqnOfIncomingLinks = {spc.fqn | spc <- machinesWithLinksToSubject};
	set[str] fqnOfOutgoingLinks = {em.fqn | em <- subject.externalMachines};
		
	set[JsTransition] incomingTransitions = {jsTransFromExternal(spc.name, fromEvent, id) | JsSpec spc <- machinesWithLinksToSubject, 
		/jsTransToExternal(str fromEvent, name, str toEvent) := spc.transitionsToExternal,
		/jsEvent(str id, toEvent, _,_,_,_,_,_) := subject};
	
	set[JsExternalMachine] merged = {em | em <- subject.externalMachines, em.fqn notin fqnOfIncomingLinks} + 
		{jsEM(spc.fqn, spc.name, incoming()) | JsSpec spc <- machinesWithLinksToSubject, spc.fqn notin fqnOfOutgoingLinks} +
		{jsEM(spc.fqn, spc.name, both()) | JsSpec spc <- machinesWithLinksToSubject, spc.fqn in fqnOfIncomingLinks && spc.fqn in fqnOfOutgoingLinks};
	
	return jsSpec(subject.fqn, subject.name, subject.doc, subject.specMod, subject.inheritsFrom, 
		subject.extendedBy, subject.fields, subject.events, subject.states, subject.transitions, 
		merged, subject.transitionsToExternal, incomingTransitions);
}

Maybe[JsSpec] generateJsStructureOfInternals(loc file) {
	
	println("Working on: <file>");

	try {		
		tuple[set[Message], Built] model = load(file); 
		
		if (/Specification spc := model<1>.inlinedMod) {
		  Module inlined = model<1>.inlinedMod;
		
			return just(jsSpec(
					"<inlined.modDef.fqn>", 
					"<inlined.modDef.fqn.modName>",
					processSpecDoc(inlined), 
					processSpecModifier(inlined), 
					processExtends(inlined.spec, inlined.imports), 
					{}, // specs that extend from this spec are filled later
					{jsField("<field.name>", "<field.tipe>") | /FieldDecl field := inlined.spec.fields}, 
					{jsEvent("<from.from>_<e.name>_<to.to>", 
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
					{jsTrans("<from.from>", "<to.to>", "<from.from>_<via>_<to.to>") | /StateFrom from := inlined.spec.lifeCycle, /StateTo to := from.destinations, /VarName via := to.via}, 
					({} | it + processExternalMachines(e, inlined) | /EventDef e := inlined.spec.events),  
					({} | it + processLinksToExternalMachines("<from.from>_<e.name>_<to.to>", e) | /StateFrom from := inlined.spec.lifeCycle, 
						  /StateTo to := from.destinations,
						  /VarName via := to.via, 
						  /EventDef e := inlined.spec.events,
						  "<e.name>" == "<via>"),
					{}));
		} else {
			return nothing();
		}
		
	} catch ex: {
		println("Could not create Javascript model of specification <file>, reason <ex>");
		return nothing();
	}
}

private str processSpecDoc(Module spc) = processDoc(spc.spec.annos);
private str processEventDoc(EventDef evnt) = processDoc(evnt.annos);

private str processDoc(&T<:Tree t) = trim("<doc.contents>")
	when /(Annotation)`@doc <TagString doc>` := t; 
private default str processDoc(&T<:Tree t) = "";

private set[JsExternalMachine] processExternalMachines(EventDef evnt, Module inlinedSpec) =
	{jsEM("<fqn>", "<specName>", outgoing()) | /(Ref)`<FullyQualifiedName specName>` := evnt, /fqn:(FullyQualifiedName)`<{VarName "."}+ _>.<TypeName modName>` := inlinedSpec.imports, "<specName.modName>" == "<modName>"} +
	{jsEM("<fqn>", "<specName>", outgoing()) | /(Parameter)`<VarName name> : <TypeName specName>` := evnt.transitionParams, /fqn:(FullyQualifiedName)`<{VarName "."}+ _>.<TypeName modName>` := inlinedSpec.imports, "<modName>" == "<specName>"};
	
private set[JsTransition] processLinksToExternalMachines(str id, EventDef evnt) {
	set[JsTransition] result = 
		{jsTransToExternal(id, "<specName>", "<syncedEvnt>") | /(SyncStatement)`<Annotations _> <TypeName specName>[<Expr _>].<VarName syncedEvnt>(<{Expr ","}* params>);` := evnt} +
		{jsTransToExternal(id, "<specName>", "<syncedEvnt>") | /(SyncStatement)`<Annotations _> not <TypeName specName>[<Expr _>].<VarName syncedEvnt>(<{Expr ","}* params>);` := evnt} +
		{jsTransToExternal(id, "<specName>") | /(Expr)`initialized <TypeName specName>[<Expr _>]` := evnt};
	
	result += {jsTransToExternal(id, "<specName>") | /(Expr)`<FullyQualifiedName specName>` := evnt, /jsTransToExternal(_,"<specName>",_) !:= result};
	
	return result;
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

private JsState processState((StateFrom)`initial <VarName name> <StateTo* _>`) = jsInitialState("<name>");
private JsState processState((StateFrom)`final <VarName name> <StateTo* _>`) = jsFinalState("<name>");
private default JsState processState((StateFrom)`<LifeCycleModifier? _> <VarName name> <StateTo* _>`) = jsState("<name>");

private list[JsStatement] processPreconditions(EventDef e) = [processToText(stat) | /Statement stat := e.pre];
private list[JsStatement] processPostconditions(EventDef e) = [processToText(stat) | /Statement stat := e.post];
private list[JsStatement] processSyncBlock(EventDef e) = [processToText(stat) | /SyncStatement stat := e.sync];

private JsStatement processToText((SyncStatement)`<Annotations annos><TypeName specName>[<Expr id>].<VarName event>(<{Expr ","}* params>);`) =
  (/(Annotation)`@doc<TagString doc>` := annos) ? jsDocAndCode("<doc.contents>", "<specName>[<id>].<event>(<params>)") : jsCodeOnly("<specName>[<id>].<event>(<params>)");

private JsStatement processToText((SyncStatement)`<Annotations annos> not <TypeName specName>[<Expr id>].<VarName event>(<{Expr ","}* params>);`) =
  (/(Annotation)`@doc<TagString doc>` := annos) ? jsDocAndCode("<doc.contents>", "<specName>[<id>].<event>(<params>)") : jsCodeOnly("<specName>[<id>].<event>(<params>)");

private JsStatement processToText((Statement)`@doc <TagString doc> <Expr e>;`) = jsDocAndCode("<doc.contents>", "<e>");
private default JsStatement processToText(Statement stat) = jsCodeOnly("<stat>");
