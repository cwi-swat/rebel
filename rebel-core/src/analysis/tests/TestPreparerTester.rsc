module analysis::tests::TestPreparerTester

import analysis::TestPreparer;
import analysis::Simulator;

import testlang::Loader;
import testlang::Syntax;

import lang::Builder;

import Message;
import IO;
import List;

test bool testSimpleSetup() {
  if (<_, loaded> := loadTestModule(|project://rebel-core/examples/simple_transaction/TransactionTest.tebl|)) {
    for (/StateSetup setup := loaded<0>.testDefs) {
      State state = constructStateSetup(setup, loaded<1>, loaded<2>);
      printState(state);
    } 
    
    return true; 
  } else {
    throw "Unable to load specification test file";
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