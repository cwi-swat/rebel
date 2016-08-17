module analysis::tests::TimeGeneratorTester

import analysis::TimeGenerator;

import lang::smtlib25::AST;
import lang::smtlib25::Compiler;

import IO;
import List;

void testTimeGenerator() {
  list[Command] smt = generateDateTimeFunctions($2016-08-01$, $2016-08-31$);
  
  writeFile(|project://smtlib2/examples/sim2_date_time_functions.smt2|, intercalate("\n", [compile(s) | s <- smt]));  
}