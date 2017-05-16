@license{
Copyright (c) 2016, CWI
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
@contributor{Jouke Stoel - jouke.stoel@cwi.nl - CWI}
module lang::Flattener

import lang::Resolver;
import lang::Syntax;

import ParseTree;
import util::Maybe;
import List;
import IO;
import Set;

import Message;

alias FlattenerResult = tuple[set[Message] msgs, Module flattenedModule];

FlattenerResult flatten(Module current, set[Module] imports) {
	tuple[set[Message], set[Module]] parents = findParents(current, imports);
	
	set[Import] allImports = {imp | /Import imp := parents<1>};  
	
	Module flattenedMod = visit(current) {
		case m:(Module)`<ModuleDef modDef> <Import* _> <Specification spec>` => 
			mergedImports
			when 
				Module mergedImports := ((Module)`<ModuleDef modDef> <Specification spec>`[@\loc=m@\loc] | mergeImports(it, imp) | /Import imp := allImports)
				
		case orig:(Specification)`<Annotations annos> <SpecModifier? sm> specification <TypeName name> <Extend? ext> { <Fields? fields> <EventRefs? events> <InvariantRefs? invariants> <LifeCycle? lifeCycle> }` => 
			(Specification)	`<Annotations annos> <SpecModifier? sm> specification <TypeName name> <Extend? ext> {
							'  <Fields mergedFields>
							'  <EventRefs mergedEventRefs>
							'  <InvariantRefs mergedInvariantRefs>
							'  <LifeCycle mergedLifeCycle>
							'}`[@\loc=orig@\loc]
			when 
				Fields mergedFields := (initFields(fields) | mergeFields(it, d) | /Fields parentFields := parents, /FieldDecl d := parentFields),
				EventRefs mergedEventRefs := (initEventRefs(events) | mergeEventRefs(it, er) | /EventRef er := parents),
				InvariantRefs mergedInvariantRefs := (initInvariantRefs(invariants) | mergeInvariantRefs(it, inv) | /InvariantRefs ir := parents, /FullyQualifiedVarName inv := ir),
				LifeCycle mergedLifeCycle := (initLifeCycle(lifeCycle) | mergeLifeCycle(it, from) | /StateFrom* from := parents)
 	};

  return <parents<0>,flattenedMod>; 			
}

tuple[set[Message] msgs, set[Module] parents] findParents(Module current, set[Module] modules) {
	if (/Extend ext := current) {
    list[Import] importsWithDef = [imp | Import imp <- current.imports, "<imp.fqn.modName>" == "<ext.parent>"];
    
    if (importsWithDef == []) {
      return <{error("Extended specification can not be found in imports", ext.parent@\loc)}, {}>;
    } else if (size(importsWithDef) > 1) {
      return <{error("Multiple modules of extended specification type in import", ext.parent@\loc)}, {}>;
    }
    
    list[Module] modsWithDef = [m | Module m <- modules, "<m.modDef.fqn>" == "<importsWithDef[0].fqn>"];
    if (size(modsWithDef) != 1) { throw "Somehow the imported extended specification can not be found while the importer could find it..."; }
    
    parents = findParents(modsWithDef[0], modules);
		return <parents<0>, current + parents<1>>;
	} else {
		return <{}, {current}>;
	}
}

Module mergeImports(orig:(Module)`<ModuleDef modDef> <Import* imports> <Specification spec>` , Import new) = 
	(Module)`<ModuleDef modDef> 
			'<Import* imports>
			'<Import new>
			'<Specification spec>`[@\loc=orig@\loc];

Fields initFields(Fields? f) = /Fields ff := f ? ff :  (Fields)`fields {}`;

Fields mergeFields(orig:(Fields) `fields { <FieldDecl* l> }`, FieldDecl d) = 
	(Fields) `fields { 
             '  <FieldDecl* l>
             '  <FieldDecl d>
             '}`[@\loc=orig@\loc]
  when /d !:= l;
default Fields mergeFields(Fields f, FieldDecl _) = f; 

EventRefs initEventRefs(EventRefs? e) = /EventRefs ee := e ? ee : (EventRefs)`events {}`;  

EventRefs mergeEventRefs(orig:(EventRefs)`events { <EventRef* evnts> }`, EventRef er) =
	(EventRefs) `events {
				      '  <EventRef* evnts>
				      '  <EventRef er> 
				      '}`[@\loc=orig@\loc]
  when /er !:= orig;     
default EventRefs mergeEventRefs(EventRefs ers, EventRef _) = ers;				 	

InvariantRefs initInvariantRefs(InvariantRefs? i) = /InvariantRefs ii := i ? ii : (InvariantRefs)`invariants {}`;

InvariantRefs mergeInvariantRefs(orig:(InvariantRefs)`invariants { <FullyQualifiedVarName* invs> }`, FullyQualifiedVarName new) =
	(InvariantRefs) `invariants {
					'  <FullyQualifiedVarName* invs>
					'  <FullyQualifiedVarName new>
					'}`[@\loc=orig@\loc];	

LifeCycle initLifeCycle(LifeCycle? lc) = /LifeCycle lcc := lc ? lcc : (LifeCycle)`lifeCycle {}`;

LifeCycle mergeLifeCycle(LifeCycle orig, StateFrom* newStates) =
	(LifeCycle)	`lifeCycle {
				      '  <StateFrom* mergedStates>
				      '}`[@\loc=orig@\loc]
	when 
		/StateFrom* origStates := orig,
		StateFrom* mergedStates := (origStates | mergeStates(it, n) | n <- newStates);	
	
StateFrom* mergeStates(StateFrom* orig, newState:(StateFrom)`<LifeCycleModifier? _> <VarName from> <StateTo* destinations>`) =
	(LifeCycle) `lifeCycle {
					    '	<StateFrom* orig>
					    '	<StateFrom newState>}`.from[@\loc=orig@\loc]
	when 
		!existingState(from, orig);

StateFrom* mergeStates(StateFrom* orig, (StateFrom)`<LifeCycleModifier? _> <VarName from> <StateTo* destinations>`) = 
	(LifeCycle) `lifeCycle {
					    '	<StateFrom* merged>
					    '}`.from[@\loc=orig@\loc]
	 when
	 	existingState(from, orig),
	 	StateFrom* merged := visit (orig) {
	 		case old:(StateFrom)`<LifeCycleModifier? _> <VarName otherFrom> <StateTo* _>` => mergeStateTo(old, destinations) 
	 			when otherFrom == from
	 	};  
		
bool existingState(VarName state, StateFrom* states) =
	/(StateFrom)`<LifeCycleModifier? _> <VarName st> <StateTo* _>` := states && st == state;

StateFrom mergeStateTo(StateFrom orig, StateTo* newDestinations) = 
	merged
	when
		StateFrom merged := (orig | mergeStateTo(it, newDest) | newDest <- newDestinations);
		
default StateFrom mergeStateTo(StateFrom orig, StateTo* newDestinations) = orig;

StateFrom mergeStateTo(orig:(StateFrom) `<LifeCycleModifier? lcm> <VarName from> <StateTo* dest>`, StateTo new) = 
	(StateFrom) `<LifeCycleModifier? lcm> <VarName from> <StateTo* dest> 
				'  <StateTo new>`[@\loc=orig@\loc]
	when
		!existingStateTo(new.to, dest);

StateFrom mergeStateTo(orig:(StateFrom) `<LifeCycleModifier? lcm> <VarName from> <StateTo* dest>`, StateTo new) = 
	(StateFrom) `<LifeCycleModifier? lcm> <VarName from> <StateTo* merged>`[@\loc = orig@\loc]
	when
		existingStateTo(new.to, dest),
		StateTo* merged := visit(dest) {
			case s:(StateTo)`-\> <VarName st> : <StateVia oldVia>` => (StateTo)`-\> <VarName st> : <StateVia merged>`[@\loc = s@\loc]
				when 
					st == new.to,
					StateVia merged := (oldVia | mergeStateVia(it, evnt) | /StateVia via := new.via, /VarName evnt := via.refs)
		};

		
bool existingStateTo(VarName state, StateTo* to) = 
	/(StateTo)`-\> <VarName st> : <StateVia _>` := to && st == state; 


StateVia mergeStateVia(orig:(StateVia)`<{VarName ","}+ via>`, VarName evnt) =
	(StateVia)`<{VarName ","}+ via>, <VarName evnt>`[@\loc=orig@\loc]
	when
		!existingStateVia(evnt, via);

default StateVia mergeStateVia(StateVia orig, VarName evnt) = orig;

bool existingStateVia(VarName evnt, {VarName ","}+ orig) =
	/VarName or := orig && or == evnt;
