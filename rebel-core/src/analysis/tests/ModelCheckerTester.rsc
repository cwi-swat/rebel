module analysis::tests::ModelCheckerTester

import analysis::ModelChecker;
import testlang::TestPreparer;
import analysis::CommonAnalysisFunctions;
import analysis::SimulationHelper;

import testlang::Loader;
import testlang::Syntax;
import testlang::Parser;

import lang::Builder;

import Message;
import IO;
import List;
import util::Maybe;

test bool testIfStateIsReachable() = testIfStateIsReachable(|project://rebel-core/examples/simple_transaction/TransactionTest.tebl|,5);

test bool solveRiverCrossingProblem() = testIfStateIsReachable(|project://rebel-core/examples/rivercrossing/Problem.tebl|, 12);

bool testIfStateIsReachable(loc testFile, int maxSteps) {
  if (<_, TestLoaderResult loaded> := loadTestModule(testFile), /StateSetup setup := loaded.testModule.testDefs) {
    State state = constructStateSetup(setup, loaded.refs, loaded.importedSpecs);

    map[loc, Type] allResolvedTypes = loaded.resolvedTypes + (() | it + b.resolvedTypes | Built b <- loaded.importedSpecs);

    if (reachable(list[State] trace) := checkIfStateIsReachable(state, max(maxSteps), loaded.importedSpecs, allResolvedTypes, true)) {
      printTrace(trace, loaded.importedSpecs);
      
      return true; 
    } else {
      return false; 
    }
  } 
  else {
    return false;
  }
}

void printTrace(list[State] t, set[Built] builds) {
  for (State st <- t) {
    printState(st, builds);
  }
}
