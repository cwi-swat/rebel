module execution::DataTypes

import String;
import List;

import AST;

data Variable 
	= variable(str name, Type tipe)
	| variable(str name, Type tipe, Literal scalarVal)
	| variable(str name, Type tipe, set[Literal] setVal)
	| variable(str name, Type tipe, map[Literal, Literal] mapVal)
	; 
	
data Reference
	= scalarRef(Variable var)
	| fieldRef(Variable var, str field)
	| collRef(Variable var, Expr index)
	| funcRef(Variable var, Expr param)
	;

data LookupResult 
	= found(Variable v)
	| notFound()
	;

data Mode 
	= simulation()
	| trace()
	;
	
alias DisplayOptions = tuple[real zoom, bool traceLogVisible]; 	
	
alias TestRunner = bool (str specification, SimStep prevState, SimStep currentState);	
alias RunnerEnvironment = tuple[Mode mode, DisplayOptions displayOptions, TestRunner runner];

LookupResult lookup(str name, list[Variable] vars) = (notFound() | name == v.name ? found(v) : it | v <- vars);
Variable quickLookup(str name, list[Variable] vars) = v 
	when /found(Variable v) := lookup(name, vars);
default Variable quickLookup(str name, list[Variable] vars) { throw "Variable \'<name>\' not found";} 
	
list[Variable] getVars(list[Reference] references) = dup([r.var | r <- references]);

alias SimTransition = tuple[str eventName, list[Variable] eventInputValues, bool successful, bool successfulInTestRunner];

alias SimStep = tuple[SimTime time, str name, list[Variable] values, SimTransition transition];
alias SimSteps = list[SimStep];
SimStep getCurrentStep(SimSteps steps) = head(steps);

SimStep getStepAt(SimSteps steps, int n) = steps[n];
	
alias SimTime = int;