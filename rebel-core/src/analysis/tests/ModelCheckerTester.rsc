module analysis::tests::ModelCheckerTester

import analysis::ModelChecker;
import testlang::TestPreparer;
import analysis::CommonAnalysisFunctions;

import testlang::Loader;
import testlang::Syntax;
import testlang::Parser;

import lang::Builder;

import Message;
import IO;
import List;
import util::Maybe;

test bool testIfStateIsReachable() = testIfStateIsReachable(|project://rebel-core/examples/simple_transaction/TransactionTest.tebl|,7);

test bool solveRiverCrossingProblem() = testIfStateIsReachable(|project://rebel-core/examples/rivercrossing/Problem.tebl|, 12);

bool testIfStateIsReachable(loc testFile, int maxSteps) {
  if (<_, TestLoaderResult loaded> := loadTestModule(testFile), /StateSetup setup := loaded.testModule.testDefs) {
    State state = constructStateSetup(setup, loaded.refs, loaded.importedSpecs);

    map[loc, Type] allResolvedTypes = loaded.resolvedTypes + (() | it + b.resolvedTypes | Built b <- loaded.importedSpecs);

    if (reachable(list[State] trace) := checkIfStateIsReachable(state, max(maxSteps), loaded.importedSpecs, allResolvedTypes, true)) {
      printTrace(trace);
      
      return true; 
    } else {
      return false;
    }
  } 
  else {
    return false;
  }
}

void printTrace(list[State] t) {
  for (State st <- t) {
    println("<st.nr>:
            '  now = <st.now>");

    if (step(str entity, str event, list[Variable] transitionParameters) := st.step) {
      println("  step: <entity>.<event> <for (v <- transitionParameters) {>
              '    var <v.name> (type: <v.tipe>) = <v.val> <}>
              '");
    }
    
    println("<for (i <- st.instances) {>
            '  instance: <i.entityType>, key = <intercalate(",", i.id)> <for (v <- i.vals) {>
            '    var <v.name> (type: <v.tipe>) = <((uninitialized(_,_) !:= v) ? v.val : "uninitialized")> <}>  
            '<}>
            '");
  }
}

void printState(State st) {
  println("<st.nr>:
          'now = <st.now>
          '<for (i <- st.instances) {>
          'instance: <i.entityType>, key = <intercalate(",", i.id)> <for (v <- i.vals) {>
          '  var <v.name> (type: <v.tipe>) = <v.val> <}>  
          '<}>
          '");  
}
