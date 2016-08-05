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
  Module spc = parseModule(|project://rebel-core/examples/simple_transaction/Transaction.ebl|);
  
  set[Module] imports = loadImports(spc);
  
  for (/Specification spc := imports + spc) {
    println(spc.name);
  }
  
  Refs refs = resolve({spc} + imports);
  
  set[Module] normalizedSpecs = normalizeAllSpecs(imports + spc, refs);
  
  list[Command] smt = declareSmtTypes(normalizedSpecs) +
    declareSmtVariables("Transaction", 
      "create", [
        var("ordering", [Type]"IBAN", [IBAN]"NL34INGB0000000001"),
        var("beneficiary", [Type]"IBAN", [IBAN]"NL34INGB0000000002"),
        var("executionDate", [Type]"Date", [Date]"13 Jul 2016"),
        var("receiveDate", [Type]"Date", [Date]"13 Jul 2016"),
        var("amount", [Type]"Money", [Money]"EUR 60.00")
      ],
      imports
    ) +
    declareSmtSpecLookup(normalizedSpecs);
    
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

set[Module] normalizeAllSpecs(set[Module] mods, Refs refs) =
  {normalize(m, mods, refs) | Module m <- mods, /Specification spc := m, canBeNormalized(spc), bprintln("Normalizing <spc.name>")};

bool canBeNormalized(Specification spc) = true 
  when /(SpecModifier)`abstract` !:= spc,
       /(SpecModifier)`external` !:= spc; 

default bool canBeNormalized(Specification _) = false;