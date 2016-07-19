module analysis::tests::SimulatorTests

import analysis::Simulator;

import lang::Parser;
import lang::Importer;
import lang::Resolver;
import lang::Flattener;
import lang::Normalizer;
import lang::ExtendedSyntax;

import lang::smtlib25::Compiler;
import lang::smtlib25::AST;

import IO;

void testInitializeEntity() {
  Module spc = parseModule(|project://ing-specs/src/booking/sepa/ct/CreditTransfer.ebl|);
  set[Module] imports = loadImports(spc);
  Refs refs = resolve({spc} + imports);
  Module normalizedSpc = normalize(spc, imports, refs);
  
  list[Command] smt = declareSmtTypes(normalizedSpc + imports);
  for (c <- smt) { 
    println(compile(c));
  }
  
  //initialize("<normalizedSpc.spec.name>", 
  //  "create", [
  //    var("ordering", [Type]"IBAN", [IBAN]"NL34INGB0000000001"),
  //    var("beneficiary", [Type]"IBAN", [IBAN]"NL34INGB0000000002"),
  //    var("executionDate", [Type]"Date", [Date]"13 Jul 2016"),
  //    var("receiveDate", [Type]"Date", [Date]"13 Jul 2016"),
  //    var("amount", [Type]"Money", [Money]"EUR 60.00")
  //  ],
  //  state(0,[]), 
  //  normalizedSpc + imports
  //); 
}