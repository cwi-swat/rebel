module analysis::Simulator

import lang::ExtendedSyntax;

import lang::smtlib25::AST;

import IO;
import Set;
import String;
import List;

data TransitionResult
	= failed(str reason)
	| successful(State new)
	;

data Variable = var(str name, Type tipe, value val);
data State = state(int nr, list[EntityInstance] instances);
data EntityInstance = instance(str entityType, value id, list[Variable] vals);  

data Setup = setup(map[str, int] maxAllowedInstances);

TransitionResult initialize(str entity, str transitionToFire, list[Variable] transitionParams, State current, set[Module] spcs) {  
  list[Command] smt = declareSmtTypes(spcs) + 
                      declareSmtVariables(entity, transitionToFire, transitionParams, spcs) +
                      declareSmtSpecLookup(spcs);
  
  return failed("Not yet completed implementation"); 
}  

TransitionResult transition(str entity, str id, str transitionToFire, list[Variable] transitionParams, State current, set[Module] spcs) {	
  list[Command] smt = declareSmtTypes(specs);
  
  return failed("Not yet completed implementation"); 
}  

list[Command] declareSmtSpecLookup(set[Module] mods) {
  list[Command] smt =[];
  
  for (/Specification spc := mods) {
    // lookup @key fields
    list[Sort] sortsOfKey = [toSort(tipe) | /(FieldDecl)`<VarName _>: <Type tipe> @key` := spc.fields];
    smt += declareFunction("spec_<spc.name>", [custom("State")] + sortsOfKey, custom("<spc.name>"));  
    smt += declareFunction("spec_<spc.name>_initialized", [custom("<spc.name>")], \bool());
  }
  
  return smt;
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

list[Command] declareSmtVariables(str entity, str transitionToFire, list[Variable] transitionParams, set[Module] spcs) {
  // declare functions for all entity fields
  list[Command] smt = [declareFunction("field_<spc.name>_<f.name>", [custom("<spc.name>")], toSort(f.tipe)) | /Specification spc := spcs, /FieldDecl f := spc.fields];
  
  smt += [declareFunction("eventParam_<entity>_<transitionToFire>_<v.name>", [custom("State")], toSort(v.tipe)) | Variable v <- transitionParams];
  
  return smt; 
}

Sort toSort((Type)`Currency`) = \int();
Sort toSort((Type)`Date`) = custom("Date");
Sort toSort((Type)`Time`) = custom("Time");
Sort toSort((Type)`DateTime`) = custom("DateTime");
Sort toSort((Type)`IBAN`) = custom("IBAN");
Sort toSort((Type)`Money`) = custom("Money");
Sort toSort((Type)`Integer`) = \int();
Sort toSort((Type)`Frequency`) = \int();

default Sort toSort(Type t) { throw "Sort conversion for <t> not yet implemented"; }

list[Command] declareRebelTypesAsSmtSorts() {   
  set[tuple[str,Sort]] rebelTypes = {<"Currency", \int()>,
                                     <"Frequency", \int()>,
                                     <"Percentage", \int()>,
                                     <"Period", \int()>,
                                     <"Term", \int()>};
                             
  return [defineSort(name, [], sort) | <str name, Sort sort> <- rebelTypes] +
         [declareDataTypes([], [dataTypeDef("IBAN", [combinedCons("consIBAN", [sortedVar("countryCode", string()), sortedVar("checksum",\int()), sortedVar("accountNumber", \int())])])]),
          declareDataTypes([], [dataTypeDef("Money", [combinedCons("consMoney", [sortedVar("currency", string()), sortedVar("amount", \int())])])]),
          declareDataTypes([], [dataTypeDef("Date", [combinedCons("consDate", [sortedVar("date", \int()), sortedVar("month", \int()), sortedVar("year", \int())]), cons("undefDate")])]),
          declareDataTypes([], [dataTypeDef("Time", [combinedCons("consTime", [sortedVar("hour", \int()), sortedVar("minutes", \int()), sortedVar("seconds", \int())]), cons("undefTime")])]),
          declareDataTypes([], [dataTypeDef("DateTime", [combinedCons("consDateTime", [sortedVar("date", custom("Date")), sortedVar("time", custom("Time"))]), cons("undefDateTime")])])                                   
          ];                                  
}

