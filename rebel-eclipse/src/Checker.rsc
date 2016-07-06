module Checker

import lang::Syntax;
import lang::Resolver;

import Message;
import IO;
import Set;
import ParseTree;

set[Message] check(Module current, set[Module] imports, Refs refs) =
	checkUnresolvedImports(current, refs.imports) +
	checkUnresolvedEvents(current, refs.eventRefs) +
	checkUnresolvedFunctions(current, refs.functionRefs) +
	checkUnresolvedInvariants(current, refs.invariantRefs) + 	
	checkUnresolvedLifeCycleEvents(current, refs.lifeCycleRefs) + 
	checkUnresolvedLifeCycleStates(current, refs.stateRefs) +
	checkExternalSpecIsEmpty(current);
	//checkUniqueStates(current) +
	//checkIncompatibleEventIncluded(current, imports, refs.eventRefs, refs.inheritance) +
	//checkSpecificationNameMatchedModuleName(current) +
	//checkInheritance(current, refs.inheritance) +
	//checkKeywordReferences(current, refs.keywordRefs) + 
	//checkNoCustomTypeReferencesBySpecificationFields(current) +
	//checkReferencedSpecifications(current, refs.specRefs) + 
	//checkUnresolvedRaisedEvents(current, refs.eventRefs);
		
set[Message] checkUnresolvedImports(Module current, Ref resolvedImports) =
	{error("Imported module not found or error while parsing imported module", imp.fqn@\loc) | /Import imp <- current.imports, resolvedImports[imp.fqn@\loc] == {}};

set[Message] checkUnresolvedEvents(Module current, Ref resolvedRefs) =
	{error("Event not found", e@\loc) | /Specification spc := current, /(SpecModifier)`abstract` !:= spc, /EventRef e := current, resolvedRefs[e@\loc] == {}};
	
//set[Message] checkUnresolvedRaisedEvents(Module current, Ref eventRefs) =
//	{error("Raised event not found in specification", e.origin) | /e:raise(_,_,_,_) := current, eventRefs[e.origin] == {}}; 	
	
set[Message] checkExternalSpecIsEmpty(Module current) =
	{error("External specification can not contain field declarations", fd@\loc) | /(SpecModifier)`external` := current, /Fields fd := current} +
	{error("External specification can not contain event references", ev@\loc) | /(SpecModifier)`external` := current, /EventRefs ev := current} +
	{error("External specification can not contain invariant references", inv@\loc) | /(SpecModifier)`external` := current, /InvariantRefs inv := current} +
	{error("External specification can not contain a life cycle", lc@\loc) | /(SpecModifier)`external` := current, /LifeCycle lc := current}; 	
	
set[Message] checkUnresolvedFunctions(Module modules, Ref resolvedRefs) {
	set[Message] checkReferencedFunctions(Statements* stats) = 
		{error("Function not found", fc@\loc) | /fc:(Expr)`<VarName _>(<{Expr ","}* _>)` := stats, resolvedRefs[fc@\loc] == {}}; 
	
	errors = {};
	
	for (/EventDef evnt := modules) {
		// check function calls in the events pre and post conditions
		errors += /Statements* stats := evnt.pre ? checkReferencedFunctions(stats) : {};
		errors += /Statements* stats := evnt.post ? checkReferencedFunctions(stats) : {};
		
		// check the configured functions in the default value expressions of the config parameters
		errors += {error("Function not found", funcRef@\loc) | /(Parameter)`<VarName _>: <Type _> -\> <Type _> = <Ref funcRef>` := evnt.configParams, resolvedRefs[funcRef@\loc] == {}};
	}

	// check configured functions in the event references
	// TODO: We should also check if the parameter referenced is actually of function type. Need a true type checker for this
	errors += {error("Function not found", funcRef@\loc) | /EventRef er := modules, /(ConfigParameter)`<VarName _> = <Ref funcRef>` := er.config, resolvedRefs[funcRef@\loc] == {}};	
		
	return errors;	
}

set[Message] checkUnresolvedInvariants(Module current, Ref resolvedInvariants) =
	{error("Invariant not found", inv@\loc) | /InvariantRefs invs := current, /VarName inv := invs, resolvedInvariants[inv@\loc] == {}};

set[Message] checkUnresolvedLifeCycleEvents(Module current, Ref resolvedLifeCycleEvents) =
	{error("Event not found", evnt@\loc) | /StateVia via := current, /VarName evnt := via, resolvedLifeCycleEvents[evnt@\loc] == {}};

set[Message] checkUnresolvedLifeCycleStates(Module current, Ref resolvedStates) =
	{error("State not found", to.to@\loc) | /StateTo to := current, resolvedStates[to.to@\loc] == {}};	

//set[Message] checkIncompatibleEventIncluded(Module current, set[Module] imports, Ref eventRefs, Ref inheritance) {
//	chain = findParents(current, imports, inheritance) + {current};
//	mLocs = {spec.origin.top | /Specification spec <- chain};
//	fields = {f.name | /Specification spec := chain, f <- spec.fields};
//	referencedEvents = (r : findEventAt(d, imports) | <r, d> <- eventRefs, r.top in mLocs);
//	
//	return {error("Incompatible event reference. The event references a field called \'<field>\' but this field is not declared in the specification", r) |
//		r <- referencedEvents, /accessor(lhs:_, rhs:_) := referencedEvents[r], /this() := lhs, /ref(field:_) := rhs, field notin fields};
//}
//
//set[Message] checkInheritance(Module current, Ref inheritance) {
//	if (/specModule(_,_,spec(n:_,p:_,_,_,_,_),_) := current, inheritance[p.name.origin] == {}) {
//		return {error("Parent module with the identifier \'<unparse(p.name)>\' could not be found", p.name.origin)};
//	} else {
//		return {};
//	}
//}   
//
//set[Message] checkKeywordReferences(Module current, Ref keywordRef) =
//	{error("Keyword param not found", p.origin) | /KeywordParam p := current, keywordRef[p.origin] == {}};
//	
//set[Message] checkSpecificationNameMatchedModuleName(Module current) =
//	{error("Name of the specification must match the module name", s.origin) | /Specification s := current, s.name !=  current.modul.name.name};
//
//set[Message] checkNoCustomTypeReferencesBySpecificationFields(Module current) =
//	{error("Field can not be of a custom specification type, only primitive types are allowed", t.origin) | /Specification s := current, /t:customType(_) := s.fields}; 
//
//set[Message] checkReferencedSpecifications(Module current, Ref specRefs) =
//	{error("Referenced Specification can not be found, did you import it?", r.origin) | /r:typeRef(_) := current, specRefs[r.origin] == {}};
//
//set[Message] checkUniqueStates(Module current) {
//	errors = {};
//	declaredStates = {};
//	
//	for (/State s := current) {
//		if (s.name in declaredStates) {
//			errors += error("State \'<s.name>\' can only be defined once", s.origin);
//		}
//		declaredStates += s.name;
//	}
//	
//	return errors;
//} 


