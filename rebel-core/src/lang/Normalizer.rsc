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
import lang::Finder;

import IO;
import List;
import Set;
import String;
import ParseTree;
import ListRelation;

import Message;
import util::Maybe;

alias NormalizeResult = tuple[set[Message] msgs, Module normalizedMod];

NormalizeResult inline(Module flattenedSpc, set[Module] modules, Refs refs) {
 	// Find all referenced events
	tuple[set[Message], set[EventDef]] resolvedEventsResult = resolveReferenceEvents(flattenedSpc, modules, refs.eventRefs);
	set[EventDef] events = resolvedEventsResult<1>;

  // Find all referenced invariants
  tuple[set[Message], set[InvariantDef]] resolvedInvariantsResult = resolveReferencedInvariants(flattenedSpc, modules, refs.invariantRefs);
	
	// Merge the config values into the config params of the events	
	tuple[set[Message], set[EventDef]] mergedConfigResult = mergeConfig(events, flattenedSpc.spec, refs.keywordRefs);
	events = mergedConfigResult<1>;
	
	// Inline all configured parameters
	events = inlineConfigurationParameters(events);

  // Find all the referenced functions 
  tuple[set[Message], set[FunctionDef]] resolvedFunctionsResult = resolveReferencedFunctions(modules, events, refs.functionRefs); 
  set[FunctionDef] functions = resolvedFunctionsResult<1>;

	// Inline all the imports all directly imported files
	set[Import] allImports = inlineImports(flattenedSpc, modules);
	
	Module inlined = visit(flattenedSpc) { 
		case m:(Module)`<ModuleDef modDef> <Import* imports> <Specification spec>` => 
			mergedImports
			when 
				Module mergedImports := ((Module)`<ModuleDef modDef> <Specification spec>`[@\loc=m@\loc] | mergeImports(it, imp) | /Import imp := allImports)	
	
		case orig:(Specification)`<Annotations annos> <SpecModifier? sm> specification <TypeName name> <Extend? ext> { <Fields fields> <EventRefs eventRefs> <InvariantRefs invariantRefs> <LifeCycle lifeCycle>}` =>
			(Specification)	`<Annotations annos> <SpecModifier? sm> specification <TypeName name> <Extend? ext> { 
							'  <Fields fields> 
							'  <FunctionDefs funcs>
							'  <EventRefs eventRefs> 
							'  <EventDefs ev>
							'  <InvariantRefs invariantRefs>
							'  <InvariantDefs invs>
							'  <LifeCycle lifeCycle>  
							'}`[@\loc=orig@\loc]
				when
					FunctionDefs funcs := ((FunctionDefs)`functionDefs {}` | merge(it, f) | f <- functions),
					EventDefs ev := ((EventDefs)`eventDefs {}` | merge(it, e) | e <- events),
					InvariantDefs invs := ((InvariantDefs)`invariantDefs {}` | merge(it, i) | i <- resolvedInvariantsResult<1>)					
	};
	
	return <resolvedEventsResult<0> + resolvedFunctionsResult<0> + mergedConfigResult<0>, inlined>;	
}

NormalizeResult desugar(Module inlinedSpc, set[Module] modules, Refs refs, map[loc, Type] resolvedInlinedTypes) {
	set[EventDef] events = {e | EventDef e <- inlinedSpc.spec.events.events};
	set[FunctionDef] functions = {f | FunctionDef f <- inlinedSpc.spec.functions.defs};
	set[FieldDecl] fields = {f | FieldDecl f <- inlinedSpc.spec.fields.fields};
  set[StateFrom] states = {s | /LifeCycle lc := inlinedSpc.spec.lifeCycle, StateFrom s <- lc.from};
  set[InvariantDef] invariants = {i | InvariantDef i <- inlinedSpc.spec.invariants.defs};
	
	// Add frame conditions to the post conditions
	events = addFrameConditions(events, fields);			
	
	// Label the events with a number and add the step to the specification
	fields += (FieldDecl)`_step : Integer`;
		
	// Desugar the lifecycle into the events pre- and post conditions
	// add the _state field to the field list
	fields += (FieldDecl)`_state : Integer`;

	// Desugar the life cycle information by strengthening the preconditions of the events with this information
	tuple[set[Message], set[EventDef], set[StateFrom]] desugaringStatesResult = desugarStates(events, states);
	events = desugaringStatesResult<1>;
	states = desugaringStatesResult<2>;
	
	// 8. Add the identity fields as transition parameters of the event
	events = {addIdentityAsTransitionParams(fields, e) | EventDef e <- events};
	
  // 9. Replace all the references to this with the name of the specification
  tuple[set[Message], set[EventDef]] thisReplacingResult = replaceReferencesToThisWithSpecificationName(events, inlinedSpc.spec.eventRefs, "<inlinedSpc.spec.name>", fields);
  events = thisReplacingResult<1>;
  
  // Rewrite percentage arithmetics
  resultRewritePercentage = rewritePercentageArithmetics(events, functions, resolvedInlinedTypes);
  events = resultRewritePercentage<0>;
  functions = resultRewritePercentage<1>;
  
  invariants = replaceReferencesToThisWithSpecificationName(invariants, inlinedSpc);
	
	Module normalized = visit(inlinedSpc) {
		case orig:(Specification)`<Annotations annos> <SpecModifier? sm> specification <TypeName name> <Extend? ext> { <Fields fds> <FunctionDefs funcs> <EventRefs eventRefs> <EventDefs _> <InvariantRefs invariantRefs> <InvariantDefs invs> <LifeCycle lifeCycle>}` =>
			(Specification)	`<Annotations annos> <SpecModifier? sm> specification <TypeName name> <Extend? ext> { 
							'	<Fields mergedFields> 
							'	<FunctionDefs mergedFunctions>
							'	<EventRefs eventRefs> 
							'	<EventDefs mergedEv>
							'	<InvariantRefs invariantRefs>
							'	<InvariantDefs mergedInvariants>
							'	<LifeCycle mergedLc>  
							'}`[@\loc=orig@\loc]
				when
					Fields mergedFields := ((Fields)`fields {}` | merge(it, f) | f <- fields),
					EventDefs mergedEv := ((EventDefs)`eventDefs {}` | merge(it, e) | e <- events),
					FunctionDefs mergedFunctions := ((FunctionDefs)`functionDefs {}` | merge(it, f) | f <- functions),
					InvariantDefs mergedInvariants := ((InvariantDefs)`invariantDefs {}` | merge(it, i) | i <- invariants),
					LifeCycle mergedLc := ((LifeCycle)`lifeCycle {}` | merge(it, sf) | StateFrom sf <- states) 										
	};
	
	return <desugaringStatesResult<0> + thisReplacingResult<0>, normalized>;	
}


tuple[set[EventDef], set[FunctionDef]] rewritePercentageArithmetics(set[EventDef] events, set[FunctionDef] functions, map[loc, Type] types) {
  EventDef rewrite(EventDef orig) = bottom-up visit(orig) {
    case e:(Expr)`<Expr lhs> * <Expr rhs>` => (Expr)`(<Expr lhs> * <Expr rhs>) / 100`[@\loc=e@\loc] when types[lhs@\loc] == (Type)`Percentage` || types[rhs@\loc] == (Type)`Percentage`
  };
  FunctionDef rewrite(FunctionDef orig) = bottom-up visit(orig) {
    case e:(Expr)`<Expr lhs> * <Expr rhs>` => (Expr)`(<Expr lhs> * <Expr rhs>) / 100`[@\loc=e@\loc] when types[lhs@\loc] == (Type)`Percentage` || types[rhs@\loc] == (Type)`Percentage`
  };
      
  return <{rewrite(e) | e <- events}, {rewrite(f) | f <- functions}>;
} 

set[InvariantDef] replaceReferencesToThisWithSpecificationName(set[InvariantDef] invariants, Module spc) {
  list[str] idFields = ["_<f.name>" | FieldDecl f <- spc.spec.fields.fields, /(Annotation)`@key` := f.meta];
  
  InvariantDef rewrite(InvariantDef inv) = visit(inv) {
      case (Expr)`this.<VarName n>` => [Expr]"<spc.spec.name>[<intercalate(",", idFields)>].<n>"
  };
  
  return {rewrite(inv) | InvariantDef inv <- invariants};
}

set[Module] importedModules(Module moi, set[Module] allMods) {
	set[str] impModNames = {"<imp.fqn>" | imp <- moi.imports};
	return {imp | imp <- allMods, "<imp.modDef.fqn>" in impModNames};
}

private set[EventDef] allEventDefs(set[Module] mods) =
  {e | Module m <- mods, m has decls, /EventDef e <- m.decls};

tuple[set[Message], set[EventDef]] resolveReferenceEvents(Module flattenedSpec, set[Module] imports, Reff eventRefs) {
  set[EventDef] events = {};
  set[Message] msgs = {};
  
  for (/EventRef evntRef := flattenedSpec) {
    if (EventDef evnt <- allEventDefs(imports), {evnt@\loc} == eventRefs[evntRef@\loc]) {
      events += evnt;
    } else {
      msgs += error("Unable to find referenced event", evntRef@\loc);
    }
  }
  
  return <msgs, events>;  
}

tuple[set[Message], set[FunctionDef]] resolveReferencedFunctions(set[Module] modules, set[EventDef] referencedEvents, Reff functionRefs) {
  set[FunctionDef] resolvedFunctions = {};
  set[Message] msgs = {};
  
  for (EventDef evnt <- referencedEvents, /f:(Expr)`<VarName _>(<{Expr ","}* _>)` := evnt) {
    if (functionRefs[f@\loc] != {}, FunctionDef function <- allFunctionDefs(modules), {function@\loc} == functionRefs[f@\loc]) {
      resolvedFunctions += function; 
    } else {
      msgs += error("Referrenced function can not be found", f@\loc);
    }
  }
  
	return <msgs, resolvedFunctions>;
}

tuple[set[Message], set[InvariantDef]] resolveReferencedInvariants(Module spc, set[Module] modules, Reff invariantRefs) {
  set[InvariantDef] resolvedInvariants = {};
  set[Message] msgs = {};
  
  for (/InvariantRefs invRefs := spc, FullyQualifiedVarName invRef <- invRefs.invariants) {
    if (/InvariantDef inv := modules, {inv@\loc} == invariantRefs[invRef@\loc]) {
      resolvedInvariants += inv; 
    } else {
      msgs += error("Referrenced invariant can not be found", invRef@\loc);
    }
  }
  
  return <msgs, resolvedInvariants>;
}

EventDef addIdentityAsTransitionParams(set[FieldDecl] fields, EventDef evnt)
  = (evnt | addTransitionParam(evnt, (Parameter)`<VarName paramName>: <Type tipe>`) | (FieldDecl)`<VarName field>: <Type tipe> @key` <- fields, VarName paramName := [VarName]"_<field>"); 

tuple[set[Message], set[EventDef]] replaceReferencesToThisWithSpecificationName(set[EventDef] events, EventRefs eventRefs, str specName, set[FieldDecl] fields) {
  set[Message] msgs = {};
    
  bool hasField(VarName name) = true
    when FieldDecl f <- fields, "<f.name>" == "<name>";
  default bool hasField(VarName name) = false;
  
  EventRef findEventRef(EventDef evnt) = er
    when EventRef er <- eventRefs.events, "<er.eventRef>" == "<evnt.name>";
  bool addMsg(VarName n, EventDef evnt) { msgs += error("Event references field with name \'<n>\' but this field is not declared in the specification", findEventRef(evnt)@\loc); return true; }

  set[EventDef] altered = {};
  
  list[str] idFields = ["_<field>" | (FieldDecl)`<VarName field> : <Type _> @key` <- fields];
  
  if (idFields == []) {
    msgs += error("No id field declared", getOneFrom(fields)@\loc);
  } else {
    for (EventDef evnt <- events) {
      altered += visit(evnt) {
        case (Expr)`this.<VarName n>` => [Expr]"<specName>[<intercalate(",", idFields)>].<n>" when hasField(n)
        case (Expr)`this.<VarName n>` => (Expr)`this.<VarName n>` when !hasField(n), addMsg(n, evnt)
      }
    }
  }
  
  return <msgs, altered>;
}

Module mergeImports(orig:(Module)`<ModuleDef modDef> <Import* imports> <Specification spec>` , Import new) = 
	(Module)`<ModuleDef modDef> 
			'<Import* imports>
			'<Import new>
			'<Specification spec>`[@\loc=orig@\loc];

Fields merge(f:(Fields)`fields { <FieldDecl* orig> }`, FieldDecl new) = 
	(Fields) `fields { 
			     '  <FieldDecl* orig> 
			     '  <FieldDecl new> 
			     '}`[@\loc=f@\loc];
			
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
			
	return ({} | it + {imp} + getImports(m) | Import imp <- getImports(spc), m <- modules, "<m.modDef.fqn>" == "<imp.fqn>");
}

set[EventDef] addFrameConditions(set[EventDef] events, set[FieldDecl] fields) {
	EventDef mergePost(EventDef evnt, Statement fc) 
	  =  visit(evnt) {
	       case (Postconditions) `postconditions { <Statement* origPostCon> }` => 
              (Postconditions)  `postconditions {
                                ' <Statement* origPostCon>
                                ' <Statement fc>
                                '}`
    } when /Statement* _ := evnt.post;          
	
	EventDef mergePost(orig:(EventDef)`<Annotations annos> event <FullyQualifiedVarName name><EventConfigBlock? configParams>(<{Parameter ","}* transitionParams>){<Preconditions? pre> <Postconditions? post> <SyncBlock? sync>}`, Statement fc) 
	  =  (EventDef)
	       `<Annotations annos> event <FullyQualifiedVarName name><EventConfigBlock? configParams>(<{Parameter ","}* transitionParams>) {
	       '  <Preconditions? pre> 
	       '  postconditions {
         '    <Statement fc>
         '  }
         '  <SyncBlock? sync>
         '}`[@\loc = orig@\loc]
       when /Statement* _ !:= post;
	
	EventDef addFrameConditionsToEvent(EventDef e) {
		set[VarName] fieldNames = {field.name | FieldDecl field <- fields, /(Annotation)`@key` !:= field.meta};
		set[VarName] keyFields = {field.name | FieldDecl field <- fields, /(Annotation)`@key` := field.meta};
		
		// Remove all the fields which are referenced
		visit(e.post) {
			case (Expr)`new this.<VarName field>`: fieldNames -= field;
		}
		
		// Create the framecondition statements 
		set[Statement] frameConditions = {(Statement)`new this.<VarName f> == this.<VarName f>;` | field <- fields, field.name in fieldNames, VarName f := field.name};
		// Add extra condition to frame id field to transition id field
		frameConditions += {(Statement)`new this.<VarName f> == <VarName pf>;` | f <- keyFields, VarName pf := [VarName]"_<f>"};
	 	
		return (e | mergePost(it, fc) | Statement fc <- frameConditions); 
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
				case orig:(EventDef)	`<Annotations annos> event <FullyQualifiedVarName name> <EventConfigBlock? configParams> (<{Parameter ","}* transitionParams>) { <Preconditions? pre> <Postconditions? post> <SyncBlock? sync> }` => 
					(EventDef)	`<Annotations annos> event <FullyQualifiedVarName name> <EventConfigBlock? configParams> (<{Parameter ","}* transitionParams>) { 
								'  <Preconditions? pre> 
								'  postconditions {
								'    <Statement labeledEvent>
								'  }
								'  <SyncBlock? sync> 
								'}`[@\loc = orig@\loc]
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

EventDef addTransitionParam(orig:(EventDef) `<Annotations annos> event <FullyQualifiedVarName name> <EventConfigBlock? configParams> (<{Parameter ","}* origParams>) { <Preconditions? pre> <Postconditions? post> <SyncBlock? sync> }`, Parameter newTransitionParam) =
  (EventDef)  `<Annotations annos> event <FullyQualifiedVarName name> <EventConfigBlock? configParams> (<{Parameter ","}* origParams>, <Parameter newTransitionParam>) {
              '  <Preconditions? pre>
              '  <Postconditions? post>
              '  <SyncBlock? sync>
              '}`[@\loc = orig@\loc];  
  

tuple[set[Message], set[EventDef], set[StateFrom]] desugarStates(set[EventDef] events, set[StateFrom] states) {
	 EventDef labelEvent(EventDef e, int index) {
    Int i = [Int]"<index>";     

    Statement labeledEvent = (Statement)`new this._step == <Int i>;`;

    if (/Statement* origPostCon := e.post) {
      return visit(e) {
        case Postconditions p =>
          (Postconditions)`postconditions {
                  '  <Statement* origPostCon>
                  '  <Statement labeledEvent>
                  '}`
      };
    } else {
      return visit(e) {
        case orig:(EventDef) `<Annotations annos> event <FullyQualifiedVarName name> <EventConfigBlock? configParams> (<{Parameter ","}* transitionParams>) { <Preconditions? pre> <Postconditions? post> <SyncBlock? sync> }` => 
          (EventDef)  `<Annotations annos> event <FullyQualifiedVarName name> <EventConfigBlock? configParams> (<{Parameter ","}* transitionParams>) { 
                '  <Preconditions? pre> 
                '  postconditions {
                '    <Statement labeledEvent>
                '  }
                '  <SyncBlock? sync> 
                '}`[@\loc = orig@\loc]
      }     
    }
  }  
  
  StateFrom labelState((StateFrom)`<LifeCycleModifier? modi> <VarName from> <StateTo* destinations>`, int index) {
    Int i = [Int]"<index>";

    return (StateFrom)`<Int i>: <LifeCycleModifier? modi> <VarName from> <StateTo* destinations>`;  
  }
  
	set[Message] msgs = {};
	
	map[str, int] stateMapping = ();
	int i = 1;
	set[StateFrom] labeledStates = {};
	for (StateFrom sf <- states) {
	  stateMapping += ("<sf.from>" : i);
	  labeledStates += labelState(sf, i);
	  i += 1;
	}
	
	map[str, int] eventMapping = ();
  i = 0;
  set[EventDef] labeledEvents = {};
  for (EventDef e <- events) {
    eventMapping += ("<e.name>" : i);
    labeledEvents += labelEvent(e, i);
    i += 1;
  }
  		
  bool inEventMap(VarName name) {
    if ("<name>" notin eventMapping) {
      msgs += error("Undeclared event", name@\loc);
      return false;
    } else {
      return true;
    }
  }		
  
  bool inStateMap(VarName name) {
    if ("<name>" notin stateMapping) {
      msgs += error("Undeclared event", name@\loc);
      return false;
    } else {
      return true;
    }
  }
    		
	map[int, lrel[int, int]] eventStateMapping = (
		() | 
		eventMapping["<via>"] notin it ?
			it + (eventMapping["<via>"] : [<stateMapping["<from.from>"], stateMapping["<to.to>"]>]) :
			it + (eventMapping["<via>"] : it[eventMapping["<via>"]] + [<stateMapping["<from.from>"], stateMapping["<to.to>"]>]) 
		| StateFrom from <- states, StateTo to <- from.destinations, VarName via <- to.via.refs, inEventMap(via) && inStateMap(from.from) && inStateMap(to.to));

	Statement createInlinedPreconditionLifeCycleStatement(EventDef e) =
		[Statement] "<intercalate(" || ", statements)>;"
		when int eventNr := eventMapping["<e.name>"],
			   list[str] statements := ["(this._state == <from> && _toState == <to>)" | <int from, int to> <- eventStateMapping[eventNr]]; 		

	EventDef addTransitionToParam(EventDef orig) = addTransitionParam(orig, (Parameter)`_toState : Integer`);

  Statement postCon = [Statement] "new this._state == _toState;";

	EventDef desugarLifeCycle(EventDef e) {
		e = addTransitionToParam(e);	

    if ("<e.name>" in eventMapping, eventMapping["<e.name>"] in eventStateMapping) {
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
  				case orig:(EventDef)	`<Annotations annos> event <FullyQualifiedVarName name> <EventConfigBlock? configParams> (<{Parameter ","}* transitionParams>) { <Preconditions? pre> <Postconditions? post> <SyncBlock? sync> }` => 
  					(EventDef)	`<Annotations annos> event <FullyQualifiedVarName name> <EventConfigBlock? configParams> (<{Parameter ","}* transitionParams>) { 
  								'  preconditions {
  								'    <Statement inlinedLifeCycle>
  								'  } 
  								'  <Postconditions? post>
  								'  <SyncBlock? sync> 
  								'}`[@\loc = orig@\loc]
  					when Statement inlinedLifeCycle := createInlinedPreconditionLifeCycleStatement(e)
  			}			
  		}
    }
    		
		if (/Statement* origPostCon := e.post) {
			e = visit(e) { 
				case Postconditions p => 
					(Postconditions) `postconditions {
									'  <Statement* origPostCon>
									'  <Statement postCon>
									'}`
			}	
		} else {
			e = visit(e) {
				case orig:(EventDef)	`<Annotations annos> event <FullyQualifiedVarName name> <EventConfigBlock? configParams> (<{Parameter ","}* transitionParams>) { <Preconditions? pre> <Postconditions? post> <SyncBlock? sync> }` => 
					(EventDef)	`<Annotations annos> event <FullyQualifiedVarName name> <EventConfigBlock? configParams> (<{Parameter ","}* transitionParams>) { 
								'  <Preconditions? pre>
								'  postconditions {
								'    <Statement postCon>
								'  } 
								'  <SyncBlock? sync> 
								'}`[@\loc = orig@\loc]
			}			

		}
		
		return e;
	}
	
	if (-1 in eventStateMapping) {
	 return <msgs, events, states>;
	} else {
  	return <msgs, {desugarLifeCycle(e) | e <- labeledEvents}, labeledStates>;
  } 
}
	

set[EventDef] inlineConfigurationParameters(set[EventDef] events) {
	EventDef rewriteEvent(EventDef e) {
		return visit(e) {
			case (Expr)`<Ref ref>` => (Expr)`<Expr resolvedField>`
				when /(Parameter)`<VarName f>: <Type tipe> = <Expr resolvedField>` := e.configParams,
					 /(Ref)`<VarName field>` := ref, 
					 "<f>" == "<field>"
				
			case (Expr)`<VarName function>(<{Expr ","}* params>)` => (Expr)`<VarName resolvedFunction>(<{Expr ","}* params>)`
				when /(Parameter)`<VarName f>: <Type tipe> = <Expr resolvedFunction>` := e.configParams && "<f>" == "<function>"
		}
	};
	
	return {rewriteEvent(e) | e <- events};
}

tuple[set[Message], set[EventDef]] mergeConfig(set[EventDef] events, Specification spc, Reff keywordRefs) {
  Maybe[Expr] findConfigParameterValue(loc def) {
    if (<def, loc ref> <- keywordRefs, /EventRef er := spc.events, ConfigParameter overriddenConfig <- er.config, overriddenConfig@\loc == ref) {
      return just(overriddenConfig.val);
    } else {
      return nothing();
    } 
  }
  
  Maybe[loc] findEventRef(loc configParam) = just(er@\loc)
    when 
      EventDef evnt <- events, 
      configParam <= evnt@\loc, 
      /EventRef er := spc.events, 
      "<er.eventRef>" == "<evnt.name>";
  default Maybe[loc] findEventRef(loc configParam) = nothing();  
  
  set[Message] msgs = {};
  bool addMsg(Message m) { msgs += m; return true; }
  
  //rewrite event params
  set[EventDef] mergedEvents = {};
  for (EventDef evnt <- events) {
  	evnt.configParams = visit(evnt.configParams) {
  	  // When the config parameter already has a default value it is not necessary to have a override
      case p:(Parameter)`<VarName name> : <Type tipe> = <Expr _>` => (Parameter)`<VarName name> : <Type tipe> = <Expr newVal>`
        when 
          just(loc _) := findEventRef(p@\loc),
          just(Expr newVal) := findConfigParameterValue(p@\loc)
  
      // When the config parameter does not have a default value a override needs to be given
      case p:(Parameter)`<VarName name> : <Type tipe>` => (Parameter)`<VarName name> : <Type tipe> = <Expr newVal>`
  			when 
          just(loc _) := findEventRef(p@\loc),
          just(Expr newVal) := findConfigParameterValue(p@\loc)
  
      case p:(Parameter)`<VarName name> : <Type tipe>` => (Parameter)`<VarName name> : <Type tipe>`
        when 
          just(loc eventRef) := findEventRef(p@\loc),
          nothing() := findConfigParameterValue(p@\loc),
          addMsg(error("No value assigned to configuration parameter", eventRef))
  	};
  	
  	mergedEvents += evnt;
  }
  	
	return <msgs,mergedEvents>;
}