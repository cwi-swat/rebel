@license{
Copyright (c) 2016, CWI
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
@contributor{Jouke Stoel - jouke.stoel@cwi.nl - CWI}
module lang::Normalizer

import lang::ExtendedSyntax;
import lang::Resolver;
import lang::Flattener;

import IO;
import List;
import Set;
import String;
import ParseTree;
import ListRelation;

Module normalize(Module origSpec, set[Module] imports, Refs refs) = desugar(inline(origSpec, imports, refs), imports);

Module inline(Module origSpec, set[Module] modules, Refs refs) {
	Module flattenedSpec = flatten(origSpec, modules);

	// 1. find all referenced events, they are already in the eventRefs relation
	set[EventDef] events = resolveReferenceEvents(flattenedSpec, modules, refs.eventRefs);
	
	// 2. Merge the config values into the config params of the events	
	events = mergeConfig(events, flattenedSpec.spec, refs.keywordRefs);
	
	// 3. Inline all configured parameters
	events = inlineConfigurationParameters(events);

	// 4. Inline all the referenced functions 
	set[FunctionDef] functions = {func | <_, loc def> <- refs.functionRefs, /FunctionDef func := modules, func@\loc == def}; 

	// 5. Inline all referenced invariants
	set[InvariantDef] invariants = {inv | <_, loc def> <- refs.invariantRefs, /InvariantDef inv := modules, inv@\loc == def};

	// 6. Inline all the imports all directly imported files
	set[Import] allImports = inlineImports(flattenedSpec, modules);
	
	return visit(flattenedSpec) {
		case m:(Module)`<ModuleDef modDef> <Import* imports> <Specification spec>` => 
			mergedImports
			when 
				Module mergedImports := ((Module)`<ModuleDef modDef> <Specification spec>` | mergeImports(it, imp) | /Import imp := allImports)	
	
		case (Specification)`<Annotations annos> <SpecModifier? sm> specification <TypeName name> <Extend? ext> { <Fields fields> <EventRefs eventRefs> <InvariantRefs invariantRefs> <LifeCycle lifeCycle>}` =>
			(Specification)	`<Annotations annos> <SpecModifier? sm> specification <TypeName name> <Extend? ext> { 
							'  <Fields fields> 
							'  <FunctionDefs funcs>
							'  <EventRefs eventRefs> 
							'  <EventDefs ev>
							'  <InvariantRefs invariantRefs>
							'  <InvariantDefs invs>
							'  <LifeCycle lifeCycle>  
							'}`
				when
					FunctionDefs funcs := ((FunctionDefs)`functionDefs {}` | merge(it, f) | f <- functions),
					EventDefs ev := ((EventDefs)`eventDefs {}` | merge(it, e) | e <- events),
					InvariantDefs invs := ((InvariantDefs)`invariantDefs {}` | merge(it, i) | i <- invariants)					
	};	
}

Module desugar(Module inlinedSpec, set[Module] modules) {
	set[EventDef] events = {e | /EventDef e := inlinedSpec};
	set[FieldDecl] fields = {f | /FieldDecl f := inlinedSpec};
	
	// 1. Add frame conditions to the post conditions
	events = addFrameConditions(events, fields);			
	
	// 2. Label the events with a number and add the step to the specification
	// 2.1 add the _step field to the field list
	fields += (FieldDecl)`_step : Integer`;
	// 2.2 give each event a unique nr
	events = createEventMapping(events);
	
	set[StateFrom] states = {s | /StateFrom s := inlinedSpec.spec.lifeCycle};
	
	// 6. Desugar the lifecycle into the events pre- and post conditions
	// 6.1 add the _state field to the field list
	fields += (FieldDecl)`_state : Integer`;
	// 6.2 give each state a unique nr
	states = createStateMapping(states);
	// 6.3  desugar the life cycle information by strengthening the preconditions of the events with this information
	events = desugarStates(events, states);
	
	//// 7. Fully Qualify event, fucntion and invariant names and their references,
	//events = qualifyEventNames(events, modules); 
	
	// 8. Add the identity fields as transition parameters of the event
	events = {addIdentityAsTransitionParams(fields, e) | EventDef e <- events};
	
	// 9. Replace all the references to this with the name of the specification
	events = {replaceReferencesToThisWithSpecificationName(e, "<inlinedSpec.spec.name>", fields) | EventDef e <- events};
	
	
	return visit(inlinedSpec) {
		case (Specification)`<Annotations annos> <SpecModifier? sm> specification <TypeName name> <Extend? ext> { <Fields _> <FunctionDefs funcs> <EventRefs eventRefs> <EventDefs _> <InvariantRefs invariantRefs> <InvariantDefs invs> <LifeCycle lifeCycle>}` =>
			(Specification)	`<Annotations annos> <SpecModifier? sm> specification <TypeName name> <Extend? ext> { 
							'	<Fields mergedFields> 
							'	<FunctionDefs funcs>
							'	<EventRefs eventRefs> 
							'	<EventDefs mergedEv>
							'	<InvariantRefs invariantRefs>
							'	<InvariantDefs invs>
							'	<LifeCycle mergedLc>  
							'}`
				when
					Fields mergedFields := ((Fields)`fields {}` | merge(it, f) | f <- fields),
					EventDefs mergedEv := ((EventDefs)`eventDefs {}` | merge(it, e) | e <- events),
					LifeCycle mergedLc := ((LifeCycle)`lifeCycle {}` | merge(it, sf) | StateFrom sf <- states) 										
	};	
}

set[Module] importedModules(Module moi, set[Module] allMods) {
	set[str] impModNames = {"<imp.fqn>" | imp <- moi.imports};
	return {imp | imp <- allMods, "<imp.modDef.fqn>" in impModNames};
}

set[EventDef] resolveReferenceEvents(Module flattenedSpec, set[Module] imports, Ref eventRefs) =
	{evnt | <loc ref, loc def> <- eventRefs, /EventRef evntRef := flattenedSpec, ref == evntRef@\loc, /EventDef evnt := imports, evnt@\loc == def};

//set[FunctionDef] resolveReferencedFunctions(set[Module] allMods, set[EventDef] referencedEvents, Ref functionRefs) =
//	set[loc] eventLocs = {evnt@\};
//	return {func | <loc ref, loc def> <- functionRefs, ref};
//}

EventDef addIdentityAsTransitionParams(set[FieldDecl] fields, EventDef evnt)
  = (evnt | addTransitionParam(evnt, (Parameter)`<VarName paramName>: <Type tipe>`) | (FieldDecl)`<VarName field>: <Type tipe> @key` <- fields, VarName paramName := [VarName]"_<field>"); 

EventDef replaceReferencesToThisWithSpecificationName(EventDef evnt, str specName, set[FieldDecl] fields) {
  list[str] idFields = ["_<field>" | (FieldDecl)`<VarName field> : <Type _> @key` <- fields];
  
  return visit(evnt) {
    case (Expr)`this.<VarName n>` => [Expr]"<specName>[<intercalate(",", idFields)>].<n>"
  }
}

Module mergeImports((Module)`<ModuleDef modDef> <Import* imports> <Specification spec>` , Import new) = 
	(Module)`<ModuleDef modDef> 
			'<Import* imports>
			'<Import new>
			'<Specification spec>`;

Fields merge((Fields)`fields { <FieldDecl* orig> }`, FieldDecl new) = 
	(Fields) `fields { 
			     '  <FieldDecl* orig> 
			     '  <FieldDecl new> 
			     '}`;
			
FunctionDefs merge((FunctionDefs)`functionDefs {<FunctionDef* orig>}`, FunctionDef new) = 
	(FunctionDefs) `functionDefs {
					       '  <FunctionDef* orig>
				  	     '  <FunctionDef new>
				  	     '}`;
				  
EventDefs merge((EventDefs)`eventDefs {<EventDef* orig>}`, EventDef new) = 
	(EventDefs)	`eventDefs {
				'  <EventDef* orig>
			   	'  <EventDef new>
			   	'}`;
			   
InvariantDefs merge((InvariantDefs)`invariantDefs {<InvariantDef* orig>}`, InvariantDef new) = 
	(InvariantDefs)	`invariantDefs {
					'  <InvariantDef* orig>
				   	'  <InvariantDef new>
				   	'}`;
				   
LifeCycle merge((LifeCycle)`lifeCycle { <StateFrom* orig> }`, StateFrom new) = 
	(LifeCycle)	`lifeCycle { 
				'  <StateFrom* orig>
				'  <StateFrom new>
				'}`; 

set[Import] inlineImports(Module spc, set[Module] modules) {
	set[Import] getImports(Module m) = {imp | /Import imp := m};
	
	//set[Import] origImport = getImports(spc);
	//set[Import] direcTransitive = ({} | )
		
	return ({} | it + {imp} + getImports(m) | Import imp <- getImports(spc), m <- modules, "<m.modDef.fqn>" == "<imp.fqn>");
}

//set[EventDef] qualifyEventNames(set[EventDef] events, set[Module] modules) {
//	EventDef replaceName((EventDef)	`<Annotations annos> event <FullyQualifiedVarName orig> <EventConfigBlock? configParams>(<{Parameter ","}* transitionParams>) { <Preconditions? pre> <Postconditions? post> <SyncBlock? sync>}`, Module m) = 
//		(EventDef)	`<Annotations annos> event <FullyQualifiedVarName new> <EventConfigBlock? configParams>(<{Parameter ","}* transitionParams>) {
//					'  <Preconditions? pre> 
//					'  <Postconditions? post>
//					'  <SyncBlock? sync> 
//					'}`
//		when FullyQualifiedName fqn := m.modDef.fqn,
//			 VarName eventName := orig.name,
//			 FullyQualifiedVarName new := (FullyQualifiedVarName)`<FullyQualifiedName fqn>.<VarName eventName>`;
//
//	return {replaceName(e, m) | Module m <- modules, EventDef e <- events, e.name@\loc.top == m@\loc.top };		
//}
//
//tuple[set[FunctionDef], set[EventDefs], set[InvariantDef]] qualifyFunctionNames(set[FunctionDef] functions, set[EventDef] events, set[InvariantDef] invariants, Ref functionRefs) {
//	//FunctionDef
//	//for (FunctionDef f <- functions) {
//	//	
//	//}
//}

set[EventDef] addFrameConditions(set[EventDef] events, set[FieldDecl] fields) {
	EventDef addFrameConditionsToEvent(EventDef e) {
		set[VarName] fieldNames = {field.name | FieldDecl field <- fields};
		// Remove all the fields which are referenced
		visit(e.post) {
			case (Expr)`new this.<VarName field>`: fieldNames -= field;
			//case (Expr)`new this.<VarName field>[<Expr _>]`: fieldNames -= field;
		}
		
		// Create the framecondition statements 
		set[Statement] frameConditions = {(Statement)`new this.<VarName f> == this.<VarName f>;` | field <- fields, field.name in fieldNames, VarName f := field.name};
		 
		// Add the frameconditions to the postconditions of the event
		for (fc <- frameConditions, /Statement* origPostCon := e.post) {
			e = visit (e) {
				case Postconditions p => (Postconditions) 	`postconditions {
									 						'	<Statement* origPostCon>
									 						'	<Statement fc>
									 						'}`
			}
		}
			
		return e; 
	}	
	
	return {addFrameConditionsToEvent(e) | e <- events};
}

set[EventDef] createEventMapping(set[EventDef] events) {
	int index = 1;

	EventDef labelEvent(EventDef e) {
		Int i = [Int]"<index>";			

		Statement labeledEvent = (Statement)`new this._step == <Int i>;`;

		if (/Statement* origPostCon := e.post) {
			e = visit(e) {
				case Postconditions p =>
					(Postconditions)`postconditions {
									'  <Statement* origPostCon>
									'  <Statement labeledEvent>
									'}`
			};
		} else {
			e = visit(e) {
				case (EventDef)	`<Annotations annos> event <FullyQualifiedVarName name> <EventConfigBlock? configParams> (<{Parameter ","}* transitionParams>) { <Preconditions? pre> <Postconditions? post> <SyncBlock? sync> }` => 
					(EventDef)	`<Annotations annos> event <FullyQualifiedVarName name> <EventConfigBlock? configParams> (<{Parameter ","}* transitionParams>) { 
								'  <Preconditions? pre> 
								'  postconditions {
								'    <Statement labeledEvent>
								'  }
								'  <SyncBlock? sync> 
								'}`
			}			
		}
		
		index += 1;
						
		return e;	
	}		
	
	return {labelEvent(e) | e <- events};
}

set[StateFrom] createStateMapping(set[StateFrom] states) {
	int index = 1;
	
	StateFrom labelState((StateFrom)`<LifeCycleModifier? modi> <VarName from> <StateTo* destinations>`) {
		Int i = [Int]"<index>";
		index += 1;
		
		return (StateFrom)`<Int i>: <LifeCycleModifier? modi> <VarName from> <StateTo* destinations>`;	
	}
	
	return {labelState(s) | s <- states};
}

EventDef addTransitionParam((EventDef) `<Annotations annos> event <FullyQualifiedVarName name> <EventConfigBlock? configParams> (<{Parameter ","}* origParams>) { <Preconditions? pre> <Postconditions? post> <SyncBlock? sync> }`, Parameter newTransitionParam) =
  (EventDef)  `<Annotations annos> event <FullyQualifiedVarName name> <EventConfigBlock? configParams> (<{Parameter ","}* origParams>, <Parameter newTransitionParam>) {
              '  <Preconditions? pre>
              '  <Postconditions? post>
              '  <SyncBlock? sync>
              '}`;  
  

set[EventDef] desugarStates(set[EventDef] events, set[StateFrom] states) {
	int eventNr(VarName eventName) = stepNr
		when 
			/(EventDef)`<Annotations _> event <FullyQualifiedVarName name> <EventConfigBlock? _>(<{Parameter ","}* _>) { <Preconditions? _> <Postconditions? post> <SyncBlock? _>}` := events && "<name.name>" == "<eventName>",
			/(Statement)`new this._step == <Int i>;` := post,
			int stepNr := toInt("<i>");

	int eventNr(FullyQualifiedVarName eventName) = eventNr(eventName.name);
	
	default int eventNr(value tipe) { throw "Not implemented: <tipe>"; }				
				
	int stateNr(StateTo to) = stateNr
		when 
			/(StateFrom)`<Int i>: <LifeCycleModifier? _> <VarName from> <StateTo* _>` := states,
			"<from>" == "<to.to>",
			int stateNr := toInt("<i>");			

	int stateNr(StateFrom from) = toInt("<from.nr>");
	
	map[int, lrel[int, int]] eventStateMapping = (
		() | 
		eNr notin it ?
			it + (eNr
			 : [<stateNr(from), stateNr(to)>]) :
			it + (eNr : it[eNr] + [<stateNr(from), stateNr(to)>]) 
		| StateFrom from <- states, /StateTo to := from, /VarName via := to.via, int eNr := eventNr(via));

	Statement createInlinedPreconditionLifeCycleStatement(EventDef e) =
		[Statement] "<intercalate(" || ", statements)>;"
		when int eventNr := eventNr(e.name),
			 list[str] statements := ["(this._state == <from> && _toState == <to>)" | <int from, int to> <- eventStateMapping[eventNr]]; 		

	Statement createInlinedPostconditionLifeCycleStatement(EventDef e) = [Statement] "new this._state == _toState;";

	EventDef addTransitionToParam(EventDef orig) = addTransitionParam(orig, (Parameter)`_toState : Integer`);

	EventDef desugarLifeCycle(EventDef e) {
		e = addTransitionToParam(e);	
		
		if (/Statement* origPreCon := e.pre) { 
			e = visit(e) { 
				case Preconditions p => 
					(Preconditions) `preconditions {
									'  <Statement* origPreCon>
									'  <Statement inlinedLifeCycle>
									'}`
					when Statement inlinedLifeCycle := createInlinedPreconditionLifeCycleStatement(e)
			} 	 
		} else {
			e = visit(e) {
				case (EventDef)	`<Annotations annos> event <FullyQualifiedVarName name> <EventConfigBlock? configParams> (<{Parameter ","}* transitionParams>) { <Preconditions? pre> <Postconditions? post> <SyncBlock? sync> }` => 
					(EventDef)	`<Annotations annos> event <FullyQualifiedVarName name> <EventConfigBlock? configParams> (<{Parameter ","}* transitionParams>) { 
								'  preconditions {
								'    <Statement inlinedLifeCycle>
								'  } 
								'  <Postconditions? post>
								'  <SyncBlock? sync> 
								'}`
					when Statement inlinedLifeCycle := createInlinedPreconditionLifeCycleStatement(e)
			}			
		}
		
		if (/Statement* origPostCon := e.post) {
			e = visit(e) { 
				case Postconditions p => 
					(Postconditions) `postconditions {
									'  <Statement* origPostCon>
									'  <Statement inlinedLifeCycle>
									'}`
					when Statement inlinedLifeCycle := createInlinedPostconditionLifeCycleStatement(e)		
			}	
		} else {
			e = visit(e) {
				case (EventDef)	`<Annotations annos> event <FullyQualifiedVarName name> <EventConfigBlock? configParams> (<{Parameter ","}* transitionParams>) { <Preconditions? pre> <Postconditions? post> <SyncBlock? sync> }` => 
					(EventDef)	`<Annotations annos> event <FullyQualifiedVarName name> <EventConfigBlock? configParams> (<{Parameter ","}* transitionParams>) { 
								'  <Preconditions? pre>
								'  postconditions {
								'    <Statement inlinedLifeCycle>
								'  } 
								'  <SyncBlock? sync> 
								'}`
					when Statement inlinedLifeCycle := createInlinedPostconditionLifeCycleStatement(e)
			}			

		}
		
		return e;
	}
	
	return {desugarLifeCycle(e) | e <- events}; 
}
	

set[EventDef] inlineConfigurationParameters(set[EventDef] events) {
	EventDef rewriteEvent(EventDef e) {
		return visit(e) {
			case (Expr)`<Ref ref>` => (Expr)`<Expr resolvedField>`
				when /(Parameter)`<VarName f>: <Type tipe> = <Expr resolvedField>` := e.configParams,
					 /(Ref)`<VarName field>` := ref, 
					 f == field
				
			case (Expr)`<VarName function>(<{Expr ","}* params>)` => (Expr)`<VarName resolvedFunction>(<{Expr ","}* params>)`
				when /(Parameter)`<VarName f>: <Type tipe> = <Expr resolvedFunction>` := e.configParams && f == function
		}
	};
	
	return {rewriteEvent(e) | e <- events};
}

set[EventDef] mergeConfig(set[EventDef] events, Specification spc, Ref keywordRefs) {
	for (<loc ref, loc def> <- keywordRefs, /ConfigParameter overriddenConfig := spc, overriddenConfig@\loc == ref) {
		//rewrite event param
		events = visit(events) {
			case p:(Parameter)`<VarName name> : <Type tipe> = <Expr _>` => (Parameter)`<VarName name> : <Type tipe> = <Expr newVal>`
				when 
					def == p@\loc,
					Expr newVal := overriddenConfig.val

			case p:(Parameter)`<VarName name> : <Type tipe>` => (Parameter)`<VarName name> : <Type tipe> = <Expr newVal>`
				when 
					def == p@\loc,
					Expr newVal := overriddenConfig.val
		}
	}
	
	return events;
}