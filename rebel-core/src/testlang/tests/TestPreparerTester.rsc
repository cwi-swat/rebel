module testlang::tests::TestPreparerTester

import analysis::CommonAnalysisFunctions;

import testlang::Loader;
import testlang::Syntax;
import testlang::TestPreparer;

import lang::Builder;

import Message;
import IO;
import List;

test bool testSimpleSetup() {
  if (<_, TestLoaderResult loaded> := loadTestModule(|project://rebel-core/examples/simple_transaction/TransactionTest.tebl|)) {
    for (/StateSetup setup := loaded.testModule.testDefs) {
      State state = constructStateSetup(setup, loaded.refs, loaded.importedSpecs);
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
          '  <if (var(name,tipe,val) := v) {> var <v.name> (type: <v.tipe>) = <v.val><}>
          '  <if (constraintedVar(const) := v) {> constraint <const> <}><}>  
          '<}>
          '");  
}