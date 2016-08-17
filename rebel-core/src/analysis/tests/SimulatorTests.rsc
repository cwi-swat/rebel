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
import List;

void testInitializeEntity() {
  Module spc = parseModule(|project://rebel-core/examples/simple_transaction/Transaction.ebl|);
  
  set[Module] imports = loadImports(spc);
  Refs refs = resolve({spc} + imports);
  
  set[Module] normalizedSpecs = normalizeAllSpecs(imports + spc, refs);

  for (Module m <- normalizedSpecs, EventDef evnt <- m.spec.events, m.spec.) {
    println(evnt);
  }

  // Build up the current state, all possible entities must be present, even if they are not initialized
  State current = state(
    1, // state nr
    [DateTime]"12 Jul 2016, 12:00:00", // now 
    [instance("Account", [[lang::Syntax::Literal]"NL34ING001"], true, [var("accountNumber", [Type]"IBAN", [IBAN]"NL34ING001"), // all possible instances and their current values
                                                    var("balance", [Type]"Money", [Money]"EUR 10.00")]),
     instance("Account", [[lang::Syntax::Literal]"NL34ING002"], true, [var("accountNumber", [Type]"IBAN", [IBAN]"NL34ING002"),
                                                   var("balance", [Type]"Money", [Money]"EUR 20.00")]),
     instance("Transaction", [[lang::Syntax::Literal]"1"], false, [])   
  ]);
  
  list[Variable] transitionParams = [
        var("id", [Type]"Integer", [Int]"1"),
        var("amount", [Type]"Money", [Money]"EUR 5.00"),
        var("from", [Type]"IBAN", [IBAN]"NL34ING001"),
        var("to", [Type]"IBAN", [IBAN]"NL34ING002"),
        var("bookOn", [Type]"Date", [Date]"13 Jul 2016")
      ];
  
  list[Command] smt = declareSmtTypes(normalizedSpecs) +
                      declareSmtVariables("Transaction", "start", transitionParams, normalizedSpecs) +
                      declareSmtSpecLookup(normalizedSpecs) +
                      translateState(current) +
                      translateTransitionParams("Transaction", "start", transitionParams) +
                      [checkSatisfiable(), getModel()];
    
  writeFile(|project://smtlib2/examples/sim2_gen.smt2|, intercalate("\n", [compile(s) | s <- smt]));   
}

set[Module] normalizeAllSpecs(set[Module] mods, Refs refs) =
  {normalize(m, mods, refs) | Module m <- mods, /Specification spc := m, canBeNormalized(spc), bprintln("Normalizing <spc.name>")};

bool canBeNormalized(Specification spc) = true 
  when /(SpecModifier)`abstract` !:= spc,
       /(SpecModifier)`external` !:= spc; 

default bool canBeNormalized(Specification _) = false;