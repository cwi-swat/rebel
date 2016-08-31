module lang::tests::BuilderTester

import lang::Builder;
import lang::ExtendedSyntax;
import lang::Resolver;

import Message;
import IO;

void testLoad(bool clean = false) = testLoad(|project://rebel-core/examples/simple_transaction/Transaction.ebl|, clean = clean);

void testLoad(loc file, bool clean = false) {
  void log(str msg) = println(msg);

  tuple[set[Message], Built] result = load(file, |project://rebel-core/bin/rebel|, log = log, clean = clean);
  
  for (m <- result<0>) { println(m); }
}