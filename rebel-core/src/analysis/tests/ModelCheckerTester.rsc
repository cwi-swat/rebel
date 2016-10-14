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
    checkIfStateIsReachable(state, max(6), loaded<2>);
    
    return true; 
  } 
  else {
    return false;
  }
  
}
