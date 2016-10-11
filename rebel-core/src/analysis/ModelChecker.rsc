module analysis::ModelChecker

import analysis::CommonAnalysisFunctions;

import lang::Builder;
import lang::ExtendedSyntax;

import IO;

bool checkIfStateIsReachable(State state, set[Built] specs) {
  set[Module] normalizedSpecs = {b.normalizedMod | Built b <- specs}; 
   
  map[str,str] specLookup = ("<m.modDef.fqn.modName>":"<m.modDef.fqn>" | m <- normalizedSpecs);
  map[loc, Type] types = (() | it + b.resolvedTypes | b <- specs);
  
  lrel[Built,EventDef] allEventsNeeded = filterSynchronizedEventsOnly(origSpec, transitionToFire, builtSpecs, {});
  for (<_, EventDef e> <- allEventsNeeded) println("<e.name>");

  eventToRaise = addSyncedInstances(eventToRaise, origSpec, builtSpecs);
  
  println(eventToRaise);
  
  list[Command] smt = declareSmtTypes(normalizedSpecs) +
                      declareSmtVariables(entity, transitionToFire, transitionParams, normalizedSpecs) +
                      declareSmtSpecLookup(normalizedSpecs) +
                      translateEntityFrameFunctions(builtSpecs) +
                      translateFunctions(([] | it + f | s <- builtSpecs, FunctionDef f <- s.normalizedMod.spec.functions.defs), function(types=types)) + 
                      translateEventsToFunctions(allEventsNeeded, eventAsFunction(specLookup = specLookup, types = types)) +
                      translateFrameConditionsForUnchangedInstances(eventToRaise, current, flattenedEvent(entity, "<eventToRaise.name>", specLookup = specLookup, types = types));
    
} 