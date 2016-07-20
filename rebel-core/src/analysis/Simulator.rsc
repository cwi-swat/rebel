module analysis::Simulator

import lang::ExtendedSyntax;

import lang::smtlib25::AST;

import IO;
import Set;

data TransitionResult
	= failed(str reason)
	| successful(State new)
	;

data Variable = var(str name, Type tipe, value val);
data State = state(int nr, list[EntityInstance] instances);
data EntityInstance = instance(str entityType, value id, list[Variable] vals);  

data Setup = setup(map[str, int] maxAllowedInstances);

TransitionResult initialize(str entity, str transitionToFire, list[Variable] transitionParams, State current, set[Module] spcs) {  
  list[Command] smt = declareSmtTypes(spcs);
  
  return failed("Not yet completed implementation"); 
}  

TransitionResult transition(str entity, str id, str transitionToFire, list[Variable] transitionParams, State current, set[Module] spcs) {	
  list[Command] smt = declareSmtTypes(specs);
  
  return failed("Not yet completed implementation"); 
}  

list[Command] declareSmtTypes(set[Module] specs) {
  // first declare the build in Rebel types
  list[Command] smt = declareRebelTypesAsSmtSorts();
  
  // Add the state sort as undefined sort
  smt += declareSort("State");
  
  // Add 'specification' types as undefined sorts
  smt += toList({declareSort("<spc.name>") | /Specification spc := specs});
  
  return smt; 
}

list[Command] declareSmtVariables(str entity, str transitionToFire, list[Variable] transitionParams, State current) {
  // declare functions for all entity fields
  set[Command] smt = {declareFunction("<ei.entityType>_<v.name>", [custom("State")], toSort(v.tipe)) | EntityInstance ei <- current.instances, Variable v <- ei.vals};
  
  smt += {declareFunction("<entity>_<transitionToFire>_<v.name>", [custom("State")], toSort(v.tipe)) | Variable v <- transitionParams};
  
  return smt; 
}

Sort toSort((Type)`Currency`) = \int();
Sort toSort((Type)`Date`) = custom("Date");

list[Command] declareRebelTypesAsSmtSorts() {   
  set[tuple[str,Sort]] rebelTypes = {<"Currency", \int()>,
                                     <"Frequency", \int()>,
                                     <"Percentage", \int()>,
                                     <"Period", \int()>,
                                     <"Term", \int()>,
                                     <"Time", \int()>};
                             
  return [defineSort(name, [], sort) | <str name, Sort sort> <- rebelTypes] +
         [declareDataTypes([], [dataTypeDef("IBAN", [combinedCons("consIBAN", [sortedVar("countryCode", \int()), sortedVar("checksum",\int()), sortedVar("accountNumber", \int())])])]),
          declareDataTypes([], [dataTypeDef("Money", [combinedCons("consMoney", [sortedVar("currency", \int()), sortedVar("amount", \int())])])]),
          declareDataTypes([], [dataTypeDef("Date", [combinedCons("consDate", [sortedVar("date", \int()), sortedVar("month", \int()), sortedVar("year", \int())]), cons("undefDate")])])                                  
          ];                                  
}

