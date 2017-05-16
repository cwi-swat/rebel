module analysis::ModelChecker

extend analysis::CommonAnalysisFunctions;
import analysis::SmtResponseTranslator;
import analysis::PreProcessor;

import lang::Builder;
import lang::ExtendedSyntax;
import lang::Finder;

import solver::SolverRunner;

import lang::smtlib25::AST;
import lang::smtlib25::Compiler;

import IO;
import List;
import ParseTree;
import util::Maybe;
import Boolean;
import analysis::graphs::Graph;

data Context(map[str,str] specLookup = (), map[loc, Type] types = ())
 = inGoalState(str spec, list[Expr] ids)
 ;

data StepConfig 
  = max(int nrOfSteps)
  | exact(int nrOfSteps) 
  | between(int lower, int upper)
  ;

data ReachabilityResult
  = reachable(list[State] trace)
  | reachable()
  | unreachable()
  ;

ReachabilityResult checkIfStateIsReachable(State state, StepConfig config, set[Built] allBuilts, map[loc, Type] resolvedTypes, bool requireTrace) {
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
 
  list[Command] smt = comment("Declare needed sorts") +
                      declareSmtTypes(specs) +
                      comment("Declare all fields") +
                      translateFields(specs) +
                      comment("Declare all transition paramters") +
                      translateAllTransitionParameters(specs) +
                      comment("Declare specification entity instance functions") +
                      declareSmtSpecLookup(specs, state) +
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
                      comment("Declare initial function") +
                      declareInitialFunction(allBuilts, state) +
                      comment("Declare transition function") + 
                      declareTransitionFunction(events, state, allBuilts, specLookup, resolvedTypes) +
                      comment("Declare the goal state") +
                      declareGoalFunction(state, specLookup, resolvedTypes) +
                      comment("Unroll unbounded check") +
                      unrollBoundedCheck(config);
  
  smt = replaceStringsWithInts(smt, scp);

  SolverPID pid = startSolver();
  ReachabilityResult result;
  
  try { 
    writeFile(|project://rebel-core/examples/last-output-modelchecker.smt2|, intercalate("\n", compile(smt + checkSatisfiable(), skipComments=false)));
    
    list[str] rawSmt = compile(smt);
    for (s <- rawSmt) {
      runSolver(pid, s, wait = 1);
    }
    
    if (checkSat(pid)) {
      if (requireTrace) {
        result = reachable(getTrace(pid, createInitialState(state), config, specLookup, scp, allBuilts));
      } else {
        result = reachable();
      }
    } else {
      result = unreachable();
    }
  } 
  catch ex: throw (ex);
  finally {
    stopSolver(pid);
  }
   
  return result; 
}

list[State] getTrace(SolverPID pid, State initialState, StepConfig cfg, map[str, str] specLookup, StringConstantPool scp, set[Built] allBuilts) {
  int getLower(between(int lower, int _)) = lower == 0 ? 1 : lower;
  default int getLower(StepConfig _) = 1;
  
  int getUpper(max(int nr)) = nr+1;
  int getUpper(exact(int nr)) = nr+1;
  int getUpper(between(int _, int upper)) = upper+1;
  
  list[State] trace = [initialState];

  bool goalReached = false; 
  
  for (int i <- [getLower(cfg) .. getUpper(cfg)]) {
    if (!goalReached) {
      goalReached = isGoalState(pid, "S<i>");    
      trace = getNextStateModel(pid, trace[0], "S<i>", specLookup, scp, allBuilts) + trace;
    }
  }
  
  return reverse(trace);    
}
 
State createInitialState(State objective) = 
  state(0, 
    objective.now,
    [instance(ei.entityType, ei.id, [uninitialized(v.name, v.tipe) | Variable v <- ei.vals]) | EntityInstance ei <- objective.instances],
    noStep());

bool isGoalState(SolverPID pid, str currentStateLabel) {
  Command isGoalStateCmd = getValue([functionCall(simple("goal"), [var(simple(currentStateLabel))])]);
  
  str smtOutput = runSolver(pid, compile(isGoalStateCmd), wait = 2);
  return fromString(parseSmtResponse(smtOutput, emptyLookup));
}

Command declareInitialFunction(set[Built] allBuilts, State state) {
  list[Formula] body = [];
  
  for (Built b <- allBuilts, b.normalizedMod has spec) {
    if (/(StateFrom)`<Int nr>: <LifeCycleModifier? lc> <VarName _> <StateTo* _>` := b.normalizedMod.spec.lifeCycle, "<lc>" == "initial") {
      for (EntityInstance ei <- state.instances, ei.entityType ==  "<b.normalizedMod.modDef.fqn>") {
        body += equal(functionCall(simple("field_<b.normalizedMod.modDef.fqn>__state"), [functionCall(simple("spec_<b.normalizedMod.modDef.fqn>"), [var(simple("state"))] + [translateExpr(id, emptyCtx()) | Expr id <- ei.id])]),
                      translateLit(nr));
      }   
    } else {
      println("No initial state?!?!?!");
    }
  }
  
  return defineFunction("initial", [sortedVar("state", custom("State"))], boolean(), and(body));
}

Command declareGoalFunction(State goalState, map[str,str] specLookup, map[loc, Type] types) {
  list[Formula] body = [];
  
  for (EntityInstance ei <- goalState.instances, Variable v <- ei.vals) {
    switch(v) {
      case var(str name, Type tipe, Expr val): {
        if ((Expr)`ANY` !:= val) {
          body += equal(functionCall(simple("field_<ei.entityType>_<name>"), [functionCall(simple("spec_<ei.entityType>"), [var(simple("state"))] + [translateExpr(id, emptyCtx()) | Expr id <- ei.id])]), translateExpr(val, emptyCtx()));
        }
      } 
      case constraintedVar(str name, Type tipe, Expr constraint): {
        body += translateExpr(constraint, inGoalState("<ei.entityType>", ei.id, specLookup = specLookup, types = types));
      }
    }
  }
  
  return defineFunction("goal", [sortedVar("state", custom("State"))], boolean(), \and(body));  
}

list[Command] unrollBoundedCheck(StepConfig config) {
  list[Command] result = [];
  
  if (max(int nrOfSteps) := config) {
    if (nrOfSteps < 1) { throw "Cannot perform check with less than 1 step"; }
    
    list[Formula] possibleTraces = [functionCall(simple("goal"), [var(simple("S0"))])] + 
      [\and([functionCall(simple("transition"), [var(simple("S<j>")), var(simple("S<j+1>"))]) | int j <- [0..i]] + [functionCall(simple("goal"), [var(simple("S<i>"))])]) | int i <- [1..nrOfSteps+1]];
    
    result = [declareConst("S<i>", custom("State")) | int i <- [0 .. nrOfSteps+1]] +
      [\assert(functionCall(simple("initial"), [var(simple("S0"))]))] +
      [\assert(\or(possibleTraces))];
  }    
  
  return result;   
}

Formula translateExpr((Expr)`<Ref r>`, Context ctx) 
  = functionCall(simple("field_<spec>_<r>"), [functionCall(simple("spec_<spec>"), [var(simple("state"))] + [translateExpr(id, emptyCtx()) | Expr id <- ids])])
  when inGoalState(str spec, list[Expr] ids) := ctx;
