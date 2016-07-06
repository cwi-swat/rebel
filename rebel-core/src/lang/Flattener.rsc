module lang::Flattener

import lang::Resolver;
import lang::Syntax;

import ParseTree;
import util::Maybe;
import List;
import IO;

Module flatten(Module current, set[Module] imports) {
	set[Module] parents = findParents(current, imports);
	
	set[Import] allImports = {imp | /Import imp := parents + current}; 
	
	return visit(current) {
		case m:(Module)`<ModuleDef modDef> <Import* _> <Specification spec>` => 
			mergedImports
			when 
				Module mergedImports := ((Module)`<ModuleDef modDef> <Specification spec>` | mergeImports(it, imp) | /Import imp := allImports)
				
		case (Specification)`<Annotations annos> <SpecModifier? sm> specification <TypeName name> <Extend? ext> { <Fields? fields> <EventRefs? events> <InvariantRefs? invariants> <LifeCycle? lifeCycle> }` => 
			(Specification)	`<Annotations annos> <SpecModifier? sm> specification <TypeName name> <Extend? ext> {
							'  <Fields mergedFields>
							'  <EventRefs mergedEventRefs>
							'  <InvariantRefs mergedInvariantRefs>
							'  <LifeCycle mergedLifeCycle>
							'}`
			when 
				Fields mergedFields := (initFields(fields) | mergeFields(it, d) | /Fields parentFields := parents, /FieldDecl d := parentFields),
				EventRefs mergedEventRefs := (initEventRefs(events) | mergeEventRefs(it, er) | /EventRef er := parents),
				InvariantRefs mergedInvariantRefs := (initInvariantRefs(invariants) | mergeInvariantRefs(it, inv) | /InvariantRefs ir := parents, /FullyQualifiedVarName inv := ir),
				LifeCycle mergedLifeCycle := (initLifeCycle(lifeCycle) | mergeLifeCycle(it, from) | /StateFrom* from := parents)
 	};
			
}

set[Module] findParents(Module current, set[Module] modules) {
	if (/Extend ext := current) {
		for(/Import imp := current, "<imp.fqn.modName>" == "<ext.parent>") {
			
			for(m <- modules, "<m.modDef.fqn>" == "<imp.fqn>") {
				return {m} + findParents(m, modules);
			}
			
			return {};
			
		}
	} else {
		return {};
	}
}

Module mergeImports((Module)`<ModuleDef modDef> <Import* imports> <Specification spec>` , Import new) = 
	(Module)`<ModuleDef modDef> 
			'<Import* imports>
			'<Import new>
			'<Specification spec>`;

Fields initFields(Fields? f) = /Fields ff := f ? ff :  (Fields)`fields {}`;

Fields mergeFields((Fields) `fields { <FieldDecl* l> }`, FieldDecl d) = 
	(Fields) `fields { 
             '  <FieldDecl* l>
             '  <FieldDecl d>
             '}`;

//Fields mergeFields(Fields? lhs, FieldDecl d) = 
//	(Fields)	`fields {
//			 	'  <FieldDecl d>
//			 	'}`
//	when /Fields _ !:= lhs;
//
//Fields mergeFields(Fields? lhs, FieldDecl d) = 
//	mergeFields(orig, d)
//	when /Fields orig := lhs;

EventRefs initEventRefs(EventRefs? e) = /EventRefs ee := e ? ee : (EventRefs)`events {}`;  

EventRefs mergeEventRefs((EventRefs)`events { <EventRef* orig> }`, EventRef ref) =
	(EventRefs) `events {
				'  <EventRef* orig>
				'  <EventRef ref>
				'}`;	

//EventRefs mergeEventRefs(EventRefs? refs, EventRef ref) =
//	(EventRefs) `events {
//				'  <EventRef ref>
//				'}`
//	when /EventRefs _ !:= refs;
//
//EventRefs mergeEventRefs(EventRefs? refs, EventRef ref) =
//	mergeEventRefs(orig, ref)
//	when /EventRefs orig := refs;

InvariantRefs initInvariantRefs(InvariantRefs? i) = /InvariantRefs ii := i ? ii : (InvariantRefs)`invariants {}`;

InvariantRefs mergeInvariantRefs((InvariantRefs)`invariants { <FullyQualifiedVarName* orig> }`, FullyQualifiedVarName new) =
	(InvariantRefs) `invariants {
					'  <FullyQualifiedVarName* orig>
					'  <FullyQualifiedVarName new>
					'}`;	

//InvariantRefs mergeInvariantRefs(InvariantRefs? refs, FullyQualifiedVarName new) =
//	(InvariantRefs) `invariants {
//					'  <VarName new>
//					'}`
//	when !(/InvariantRefs _ := refs);
//
//InvariantRefs mergeInvariantRefs(InvariantRefs? refs, FullyQualifiedVarName new) =
//	mergeInvariantRefs(orig, new)
//	when /InvariantRefs orig := refs;

LifeCycle initLifeCycle(LifeCycle? lc) = /LifeCycle lcc := lc ? lcc : (LifeCycle)`lifeCycle {}`;

//LifeCycle mergeLifeCycle(LifeCycle? orig, StateFrom* new) =
//	(LifeCycle)	`lifeCycle {
//				'  <StateFrom* new>
//				'}`
//	when !(/LifeCycle _ := orig);
//
//LifeCycle mergeLifeCycle(LifeCycle? orig, StateFrom* new) =
//	mergeLifeCycle(lc, new)
//	when /LifeCycle lc := orig;
		 
LifeCycle mergeLifeCycle(LifeCycle orig, StateFrom* new) =
	(LifeCycle)	`lifeCycle {
				'  <StateFrom* mergedStates>
				'}`
	when 
		/StateFrom* origStates := orig,
		StateFrom* mergedStates := (origStates | mergeStates(it, n) | n <- new);	
	
StateFrom* mergeStates(StateFrom* orig, new:(StateFrom)`<LifeCycleModifier? _> <VarName from> <StateTo* destinations>`) =
	(LifeCycle) 	`lifeCycle {
					'	<StateFrom* orig>
					'	<StateFrom new>}`.from
	when 
		!existingState(from, orig);

StateFrom* mergeStates(StateFrom* orig, new:(StateFrom)`<LifeCycleModifier? _> <VarName from> <StateTo* destinations>`) = 
	(LifeCycle) 	`lifeCycle {
					'	<StateFrom* merged>
					'}`.from
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
		StateFrom merged := (orig | mergeStateTo(it, new) | new <- newDestinations);
		
default StateFrom mergeStateTo(StateFrom orig, StateTo* newDestinations) = orig;

StateFrom mergeStateTo((StateFrom) `<LifeCycleModifier? lcm> <VarName from> <StateTo* dest>`, StateTo new) = 
	(StateFrom) `<LifeCycleModifier? lcm> <VarName from> <StateTo* dest> 
				'  <StateTo new>`
	when
		!existingStateTo(new.to, dest);

StateFrom mergeStateTo((StateFrom) `<LifeCycleModifier? lcm> <VarName from> <StateTo* dest>`, StateTo new) = 
	(StateFrom) `<LifeCycleModifier? lcm> <VarName from> <StateTo* merged>`
	when
		existingStateTo(new.to, dest),
		StateTo* merged := visit(dest) {
			case (StateTo)`-\> <VarName st> : <StateVia oldVia>` => (StateTo)`-\> <VarName st> : <StateVia merged>`
				when 
					st == new.to,
					StateVia merged := (oldVia | mergeStateVia(it, evnt) | /StateVia via := new.via, /VarName evnt := via.refs)
		};

		
bool existingStateTo(VarName state, StateTo* to) = 
	/(StateTo)`-\> <VarName st> : <StateVia _>` := to && st == state; 


StateVia mergeStateVia((StateVia)`<{VarName ","}+ via>`, VarName evnt) =
	(StateVia)`<{VarName ","}+ via>, <VarName evnt>`
	when
		!existingStateVia(evnt, via);

default StateVia mergeStateVia(StateVia orig, VarName evnt) = orig;

bool existingStateVia(VarName evnt, {VarName ","}+ orig) =
	/VarName or := orig && or == evnt;
