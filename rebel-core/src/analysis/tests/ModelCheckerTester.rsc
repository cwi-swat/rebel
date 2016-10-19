module analysis::tests::ModelCheckerTester

import analysis::ModelChecker;
import analysis::TestPreparer;
import analysis::CommonAnalysisFunctions;

import testlang::Loader;
import testlang::Syntax;
import testlang::Parser;

import lang::Builder;

import Message;
import IO;
import List;
import util::Maybe;

test bool testIfStateIsReachable() {
  if (<_, loaded> := loadTestModule(|project://rebel-core/examples/simple_transaction/TransactionTest.tebl|), /StateSetup setup := loaded<0>.testDefs) {
    State state = constructStateSetup(setup, loaded<1>, loaded<2>);

    if (reachable(list[State] trace) := checkIfStateIsReachable(state, max(7), loaded<2>)) {
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
