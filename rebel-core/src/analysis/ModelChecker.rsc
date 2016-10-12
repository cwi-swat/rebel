module analysis::ModelChecker

import analysis::CommonAnalysisFunctions;

import lang::Builder;
import lang::ExtendedSyntax;
import lang::Finder;

import lang::smtlib25::AST;
import lang::smtlib25::Compiler;

import IO;
import List;
import ParseTree;
import util::Maybe;
import analysis::graphs::Graph;

data StepConfig
  = max(int nrOfSteps)
  | exact(int nrOfSteps)
  | between(int lower, int upper)
  ;

bool checkIfStateIsReachable(State state, StepConfig config, set[Built] allBuilts) {
  set[Module] specs = {b.normalizedMod | Built b <- allBuilts}; 
   
  map[str,str] specLookup = ("<m.modDef.fqn.modName>":"<m.modDef.fqn>" | m <- specs);
  map[loc, Type] types = (() | it + b.resolvedTypes | b <- allBuilts);
  
  list[FunctionDef] functions = getAllFunctionsOrderedByCallOrder(allBuilts);
  lrel[Built, EventDef] events = getAllEventsOrderedByCallOrder(allBuilts);
 
  map[str, int] eventMapping = getEventMapping(events); 
   
  list[Command] smt = comment("Declare needed sorts") +
                      declareSmtTypes(specs) +
                      comment("Declare all fields") +
                      translateFields(specs) +
                      comment("Declare all transition paramters") +
                      translateAllTransitionParameters(specs) +
                      comment("Declare specification entity instance functions") +
                      declareSmtSpecLookup(specs) +
                      comment("Declare now") + 
                      declareNow() + 
                      comment("Declare step function") +
                      declareStepFunction() +
                      comment("Declare frame functions") +
                      translateEntityFrameFunctions(allBuilts) +
                      comment("Declare all functions") +
                      translateFunctions(functions, function(types=types)) + 
                      comment("Declare functions for every event") +
                      translateEventsToFunctions(events, eventAsFunction(specLookup = specLookup, types = types)) +
                      comment("Declare initial function") +
                      declareInitialFunction(allBuilts, state) +
                      comment("Declare transition function") + 
                      declareTransitionFunction(events, state, allBuilts, specLookup, types, eventMapping) +
                      comment("Declare the goal state") +
                      declareGoalFunction(state) +
                      comment("Unroll unbounded check") +
                      unrollBoundedCheck(config);
   
   writeFile(|project://rebel-core/examples/output-reachable.smt2|, intercalate("\n", compile(smt)));
}

map[str, int] getEventMapping(lrel[Built,EventDef] events) {
  int i = 1;
  
  map[str, int] mapping = ();
  for (<Built b, EventDef e> <- events) {
    mapping += ("<b.normalizedMod.modDef.fqn>.<e.name>":i);
    i+=1;
  }
  
  return mapping;  
}

list[FunctionDef] getAllFunctionsOrderedByCallOrder(set[Built] specs) {
  Graph[FunctionDef] callOrder = ({} | it + getFunctionCallOrder(f, b, specs) | Built b <- specs, b.normalizedMod has spec, FunctionDef f <- b.normalizedMod.spec.functions.defs);
  
  return reverse(dup(order(callOrder)));
}

lrel[Built, EventDef] getAllEventsOrderedByCallOrder(set[Built] specs) {
  Graph[EventDef] callOrder = ({} | it + getSyncedEvents(e, b, specs) | Built b <- specs, b.normalizedMod has spec, EventDef e <- b.normalizedMod.spec.events.events);
  
  list[EventDef] ordered = reverse(dup(order(callOrder)));

  lrel[Built, EventDef] events = [<b, e> | EventDef e <- ordered, just(Built b) := findBuiltBeloningToEvent(e@\loc, specs)];
  
  events = [<b, addToStateAndIdToSyncedEventCalls(e, b, specs)> | <Built b, EventDef e> <- events];
  
  return events; 
}

Command declareStepFunction() = declareFunction("step", [custom("State")], \integer()); 

Command declareTransitionFunction(lrel[Built, EventDef] events, State state, set[Built] allBuilts, map[str, str] specLookup, map[loc, Type] types, map[str, int] eventMapping) {
  events = [<b, addSyncedInstances(e, b, allBuilts)> | <Built b, EventDef e> <- events];
  
  list[Formula] body = [];
  
  for (<Built b, EventDef e> <- events) {
    body += \and(
      [functionCall(simple("event_<b.normalizedMod.modDef.fqn>_<e.name>"), [var(simple("current")), var(simple("next"))] + 
        [functionCall(simple("eventParam_<b.normalizedMod.modDef.fqn>_<e.name>_<p.name>"), [var(simple("next"))]) | Parameter p <- e.transitionParams]
      )] +
      [equal(functionCall(simple("step"), [var(simple("next"))]), lit(intVal(eventMapping["<b.normalizedMod.modDef.fqn>.<e.name>"])))] + 
      translateFrameConditionsForUnchangedInstances(e, state, flattenedEvent("<b.normalizedMod.modDef.fqn>", "<e.name>", specLookup = specLookup, types = types))
      );
  }
  
  return defineFunction("transition", [sortedVar("current", custom("State")), sortedVar("next", custom("State"))], \boolean(), \or(body));
}

Command declareInitialFunction(set[Built] allBuilts, State state) {
  list[Formula] body = [];
  
  for (Built b <- allBuilts, b.normalizedMod has spec) {
    if (/(StateFrom)`<Int nr>: <LifeCycleModifier? lc> <VarName _> <StateTo* _>` := b.normalizedMod.spec.lifeCycle, "<lc>" == "initial") {
      for (EntityInstance ei <- state.instances, ei.entityType ==  "<b.normalizedMod.modDef.fqn>") {
        body += equal(functionCall(simple("field_<b.normalizedMod.modDef.fqn>__state"), [functionCall(simple("spec_<b.normalizedMod.modDef.fqn>"), [var(simple("state"))] + [translateLit(id) | RebelLit id <- ei.id])]),
                      translateLit(nr));
      }  
    } else {
      println("No initial state?!?!?!");
    }
  }
  
  return defineFunction("initial", [sortedVar("state", custom("State"))], boolean(), and(body));
}

Command declareGoalFunction(State goalState) {
  list[Formula] body = [];
  
  for (EntityInstance ei <- goalState.instances, Variable v <- ei.vals) {
    //body += functionCall(simple("spec_<ei.entityType>_initialized"), [functionCall(simple("spec_<ei.entityType>"), [var(simple("state"))] + [translateLit(id) | RebelLit id <- ei.id])]);
    
    if (uninitialized(_,_) !:= v, (Literal)`ANY` !:= v.val) {
      body += equal(functionCall(simple("field_<ei.entityType>_<v.name>"), [functionCall(simple("spec_<ei.entityType>"), [var(simple("state"))] + [translateLit(id) | RebelLit id <- ei.id])]), translateLit(v.val));
    }
  }
  
  return defineFunction("goal", [sortedVar("state", custom("State"))], boolean(), \and(body));  
}

list[Command] unrollBoundedCheck(StepConfig config) {
  list[Command] result = [];
  
  if (max(int nrOfSteps) := config) {
    if (nrOfSteps < 1) { throw "Cannot perform check with less than 1 step"; }
    
    list[Formula] possibleTraces = [\and([functionCall(simple("transition"), [var(simple("S<j>")), var(simple("S<j+1>"))]) | int j <- [0..i]] + [functionCall(simple("goal"), [var(simple("S<i>"))])]) | int i <- [1..nrOfSteps]];
    
    result = [declareConst("S<i>", custom("State")) | int i <- [0 .. nrOfSteps]] +
      [\assert(functionCall(simple("initial"), [var(simple("S0"))]))] +
      [\assert(\or(possibleTraces))];
  }    
  
  return result;   
}