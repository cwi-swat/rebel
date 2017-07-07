module analysis::Simulator

import lang::ExtendedSyntax;
import lang::Builder;
import lang::Resolver;
import lang::Finder;

import lang::smtlib25::AST;
import lang::smtlib25::Compiler; 
import solver::SolverRunner;

import analysis::CommonAnalysisFunctions;
import analysis::PreProcessor;
import analysis::SmtResponseTranslator;
import analysis::LocTranslator;
 
import IO;
import Set; 
import String;
import List;
import util::Maybe;

import ParseTree;

alias RebelLit = lang::ExtendedSyntax::Literal;

data TransitionResult
	= failed(list[str] reasons)
	| successful(State new)
	;
	
data Param = param(str name, Type tipe);

list[Param] getTransitionParams(loc spec, str transitionToFire) = 
  [param("<p.name>", p.tipe) | p <- evnt.transitionParams]
  when <_, just(Built b)> := load(spec),
       EventDef evnt <- b.normalizedMod.spec.events.events,
       "<evnt.name>" == transitionToFire;

default list[Param] getTransitionParams(loc spec, str transitionToFire) {throw "Unable to locate transition \'<transitionToFire>\' in specification \'<spec>\'. Does the transition exist?";}

TransitionResult step(str entity, str transitionToFire, list[Variable] transitionParams, State current, set[Built] allBuilts, map[loc, Type] resolvedTypes) {	
    map[str, int] stringIntMapping = ();
    
  int convertToInt(str astr) {
    tuple[int, map[str,int]] result = fromStrToInt(astr, stringIntMapping);
    stringIntMapping = result<1>;
    return result<0>;
  }
   
  str convertToStr(int anint) {
    tuple[str, map[str,int]] result = fromIntToStr(anint, stringIntMapping);
    stringIntMapping = result<1>;
    return result<0>;
  }
  
  StringConstantPool scp = scp(convertToStr, convertToInt);
  
  set[Module] specs = {b.normalizedMod | Built b <- allBuilts}; 
   
  map[str,str] specLookup = ("<m.modDef.fqn.modName>":"<m.modDef.fqn>" | m <- specs);
  
  PreProcessorResult ppr = preprocess(allBuilts);
  
  list[FunctionDef] functions = ppr.functions;
  lrel[Built, EventDef] events = ppr.events;
  
  EventDef eventToRaise = findEventToRaise(transitionToFire, events<1>);
 
  list[Command] smt = comment("Declare needed sorts") +
                      declareSmtTypes(specs) +
                      comment("Declare all fields") +
                      translateFields(specs) +
                      comment("Declare all transition paramters") +
                      translateAllTransitionParameters(specs) +
                      comment("Declare specification entity instance functions") +
                      declareSmtSpecLookup(specs, current) +
                      comment("Declare now") + 
                      declareNow() + 
                      comment("Declare step function") +
                      declareStepFunction() + 
                      comment("Declare frame functions") +
                      translateEntityFrameFunctions(allBuilts) +
                      comment("Declare all functions") +
                      translateFunctions(functions, function(types = resolvedTypes)) + 
                      comment("Declare functions for every event") +
                      translateEventsToFunctions(events, eventAsFunction(specLookup = specLookup, types = resolvedTypes)) +
                      // END OF GENERIC PART
                      
                      // SIMULATION SPECIFIC CHECKS
                      comment("Declare current and next state") +
                      declareStates() +
                      comment("Assert current state values") +
                      assertCurrentState(current) +
                      comment("Assert transition parameters") +
                      assertTransitionParams(entity, transitionToFire, transitionParams) +
                      comment("Assert event constraints") +
                      translateEventToSingleAsserts(entity, eventToRaise, current, flattenedEvent(entity, transitionToFire, specLookup = specLookup, types = resolvedTypes)) +
                      comment("Assert frame conditions for unchanged entities") +
                      assertFrameConditions(eventToRaise, current, flattenedEvent(entity, transitionToFire, specLookup = specLookup, types = resolvedTypes));
  
  smt = replaceStringsWithInts(smt, scp);

  SolverPID pid = startSolver();
  TransitionResult result;
  
  try { 
    writeFile(|project://rebel-core/examples/last-output-simulator.smt2|, intercalate("\n", compile(smt + checkSatisfiable(), skipComments=false))); 

    list[str] rawSmt = compile(smt);
    for (s <- rawSmt) {
      runSolver(pid, s, wait = 1);
    }
    
    if (checkSat(pid)) {
      result = successful(getNextStateModel(pid, current, "next", specLookup, scp, allBuilts));
    } else {
      result = failed(getUnsatCoreStatements(pid, eventToRaise));
    }
  } 
  catch ex: throw (ex);
  finally {
    stopSolver(pid);
  }
   
  return result; 
}  

EventDef findEventToRaise(str eventName, list[EventDef] events) {
  if (EventDef evnt <- events, "<evnt.name>" == eventName) {
    return evnt;
  } 
  
  throw "Unable to locate event to raise";
}

list[str] getUnsatCoreStatements(SolverPID pid, EventDef raisedEvent) {
  str smtResponse = runSolver(pid, compile(getUnsatCore()), wait = 20);
  list[loc] unsatCoreLocs = [strToLoc(l) | str l <- parseSmtUnsatCore(smtResponse)];
  
  list[str] unsatCoreStats = ["<s>" | /Statement s := raisedEvent, s@\loc in unsatCoreLocs] +
                             ["<s>" | /SyncStatement s := raisedEvent, s@\loc in unsatCoreLocs];

  return unsatCoreStats;
} 

list[Command] declareStates() = [declareConst("current", custom("State")), declareConst("next", custom("State"))]; 

list[Command] assertCurrentState(State current) {
  return [\assert(\equal(
    functionCall(simple("field_<ei.entityType>_<name>"), [functionCall(simple("spec_<ei.entityType>"), [var(simple("current"))] + [translateExpr(id, emptyCtx()) | Expr id <- ei.id])]), translateExpr(val, emptyCtx())))
     | EntityInstance ei <- current.instances, var(str name, Type tipe, Expr val) <- ei.vals, (Expr)`ANY` !:= val];
}

list[Command] assertTransitionParams(str entity, str transitionToFire, list[Variable] params) =
  [\assert(equal(functionCall(simple("eventParam_<entity>_<transitionToFire>_<p.name>"), [var(simple("next"))]), translateExpr(p.val, emptyCtx()))) | Variable p <- params, (Expr)`ANY` !:= p.val] +
  [\assert(equal(functionCall(simple("step_entity"), [var(simple("next"))]), lit(strVal(entity))))] +
  [\assert(equal(functionCall(simple("step_transition"), [var(simple("next"))]), lit(strVal(transitionToFire))))] ; 

list[Command] translateEventToSingleAsserts(str entity, EventDef evnt, State current, Context ctx) =
  [\assert(labelIfOriginal(s, ctx)) | /Statement s := evnt.pre] +
  [\assert(labelIfOriginal(s, ctx)) | /Statement s := evnt.post] +
  [\assert(attributed(translateSyncStat(s, ctx), [named(locToStr(s@\loc))])) | /SyncStatement s := evnt] +
  [\assert(\and(translateFrameConditionsForUnchangedInstances(evnt, current, ctx)))];

Formula labelIfOriginal(Statement s, Context ctx) = translateStat(s, ctx) when s@\loc.file == "Normalizer.rsc";
default Formula labelIfOriginal(Statement s, Context ctx) = attributed(translateStat(s, ctx), [named(locToStr(s@\loc))]);

list[Command] assertFrameConditions(EventDef evnt, State current, Context ctx) =
  [\assert(\and(translateFrameConditionsForUnchangedInstances(evnt, current, ctx)))];