module testlang::Interpreter

import testlang::Syntax;
import testlang::Loader;
import testlang::TestPreparer;

import lang::Finder;
import lang::Builder;

import ParseTree;
import util::Maybe;
import String;

import analysis::ModelChecker;
import analysis::CommonAnalysisFunctions;

Maybe[StateSetup] isStateDefinition(loc l, TestModule tm) = just(setup)
  when /StateSetup setup := tm.testDefs, 
       contains(setup@\loc, l);
default Maybe[StateSetup] isStateDefinition(loc l, TestModule tm) = nothing();       


Maybe[Check] isCheckDefinition(loc l, TestModule tm) = just(check)
  when /Check check := tm.testDefs, 
       contains(check@\loc, l);
Maybe[Check] isCheckDefinition(loc l, TestModule tm) = nothing();

ReachabilityResult interpretCheck(Check check, TestLoaderResult tlr, bool requireTrace = false) {
  if ((CheckStatement)`<VarName r> reachable <StepBounds sb>;` := check.stat, {loc setupDef} := tlr.refs.setupRefs[r@\loc]) {
    StateSetup setup = getSetup(setupDef, tlr.testModule);
    
    State state = constructStateSetup(setup, tlr.refs, tlr.importedSpecs);
    StepConfig bounds = constructStepConfig(sb); 
    
    map[loc, Type] allResolvedTypes = tlr.resolvedTypes + (() | it + b.resolvedTypes | Built b <- tlr.importedSpecs);
        
    return checkIfStateIsReachable(state, bounds, tlr.importedSpecs, allResolvedTypes, requireTrace);
  }
}

StateSetup getSetup(loc setupDef, TestModule tm) {
  if ((TestDef)`<StateSetup s>` <- tm.testDefs, s@\loc == setupDef) {
    return s;
  } 
  
  throw "Unable to find StateSetup definition";
}

StepConfig constructStepConfig((StepBounds)`in max <Int stepNr> <Step _>`) = max(toInt("<stepNr>"));
StepConfig constructStepConfig((StepBounds)`in exactly <Int stepNr> <Step _>`) = exact(toInt("<stepNr>"));
StepConfig constructStepConfig((StepBounds)`between <Int lower> and <Int upper> <Step _>`) = between(toInt("<lower>"), toInt("<upper>")); 