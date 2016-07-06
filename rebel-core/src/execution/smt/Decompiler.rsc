module execution::Decompiler

import Map;
import List;
import String;

import execution::DataTypes;

import execution::AST;

import execution::smtlib2::theory::core::Ast;
import execution::smtlib2::theory::ints::Ast;

import execution::smtlib2::command::response::Ast;

SimStep convertToSimState(int stepNr, bool successfulStep, FoundValue rawState, NormalizedSpecification normalizedSpec) {
	Event getEventByName(str eventName, set[Event] events) {
		for (e <- events, e.name == eventName) {
			return e;
		}
		
		throw "Event <eventName> not found";
	}
	
	list[Variable] getStateVars(list[Declaration] fields, list[Expr] foundValues) {
		list[Variable] stateVars = [];

		if (cons(str _, list[Expr] values) := foundValues[0]) {

			for(i <- [0..size(normalizedSpec.extendedFields)]) {
				stateVars += variable(normalizedSpec.extendedFields[i].name, 
					normalizedSpec.extendedFields[i].tipe, 
					parseNthValue(normalizedSpec.extendedFields[i].tipe, values, i)); 
			}

		}
		
		return stateVars;
	}
	
	list[Variable] getEventVars(Event event, list[Expr] foundValues) {
		list[Variable] vars = [];
		
		if (/cons(str eventParams, list[Expr] values) := foundValues, startsWith(eventParams, "cons") && endsWith(eventParams, "Params")) {
			
			// only parse the runtime parameters and skip the config ones
			for(i <- [0..size(event.params)]) {
				vars += variable(event.params[i].name, 
					event.params[i].tipe, 
					parseNthValue(event.params[i].tipe, values, size(event.configParams) + i)); 
			}

		}
		
		return vars;
	}
	
	map[int, set[str]] invEvMap = invert(normalizedSpec.eventMapping);
	
	if (/cons("consState", list[Expr] vals) := rawState) {
		// Could be an unintialized state
		if (var("no<normalizedSpec.name>") := vals[0]) {
			// the spec is not yet initialized
			return <stepNr, "new", [], <"",[], true,true>>;
		} else {
			// state is initialized, lets build it up
			list[Variable] stateVars = getStateVars(normalizedSpec.extendedFields, vals);
			
			// vars also contain state and step int fields, convert back to string and remove from fields
			str getStateName(integer(int stateNr)) = name
				when /state(LifeCycle _, str name, stateNr, list[StateRef] _) := normalizedSpec.states;
			
			str getEventName(integer(int eventNr)) = eventName
				when {str eventName} := invEvMap[eventNr];
						
			str stateName = getStateName(quickLookup("_state", stateVars).scalarVal);
			str eventName = getEventName(quickLookup("_step", stateVars).scalarVal);			
							
			stateVars = [v | v <- stateVars, v.name != "_state", v.name != "_step"];				
			
			list[Variable] eventVars = getEventVars(getEventByName(eventName, normalizedSpec.resolvedEvents), vals);
			eventVars = [v | v <- eventVars, v.name != "_toState"];
							
			return <stepNr, stateName, stateVars, <eventName, eventVars, successfulStep, true>>; 
		}
	}
	
	throw "Found SMT value is not of \'State\' sort"; 
}

private Literal parseNthValue(integerType(), list[Expr] expr, int n) = integer(val)
	when lit(intVal(val)) := expr[n];
private Literal parseNthValue(integerType(), list[Expr] expr, int n) = integer(negVal)
	when 
		lit(negInt(val)) := expr[n],
		negVal := -val;
	
private Literal parseNthValue(percentageType(), list[Expr] expr, int n) = percentage(val)
	when lit(intVal(val)) := expr[n];
private Literal parseNthValue(percentageType(), list[Expr] expr, int n) = percentage(negVal)
	when 
		lit(negInt(val)) := expr[n],
		negVal := -val;

private Literal parseNthValue(moneyType(), list[Expr] expr, int n) = money(euro(), (val - (val % 100)) / 100, val % 100)
	when lit(intVal(val)) := expr[n];
private Literal parseNthValue(moneyType(), list[Expr] expr, int n) = money(euro(), (negVal - (negVal % 100)) / 100, negVal % 100)
	when 
		lit(negInt(val)) := expr[n],
		negVal := -val;

private Literal parseNthValue(currencyType(), list[Expr] expr, int n) = currency(euro())
	when lit(intVal(0)) := expr[n];
private Literal parseNthValue(currencyType(), list[Expr] expr, int n) = currency(usDollar())
	when lit(intVal(1)) := expr[n];
private Literal parseNthValue(currencyType(), list[Expr] expr, int n) = currency(custom("unknown"))
	when lit(intVal(999)) := expr[n];

private Literal parseNthValue(booleanType(), list[Expr] expr, int n) = boolean(val)
	when lit(boolVal(val)) := expr[n];

private default Literal parseNthValue(Type t, list[Expr] expr, int n) { throw "Could not parse val of type <t> at \'<n>\', raw: <expr[n]>";}

