module testlang::tests::LoaderTester

import testlang::Loader;

import IO;

test bool testLoadOfTestModule() = testLoadOfTestModule(|project://rebel-core/examples/simple_transaction/TransactionTest.tebl|); 

bool testLoadOfTestModule(loc testModuleLoc) {
  result = loadTestModule(testModuleLoc);
  
  println(result<0>);
  
  return result<0> == {};
}