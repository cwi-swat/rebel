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

  for (Module ns <- normalizedSpecs) {
    println(ns);
  }

  // Build up the current state, all possible entities must be present, even if they are not initialized
  State current = state(
    1, // state nr
    [DateTime]"12 Jul 2016, 12:00:00", // now 
    [instance("Account", [[lang::Syntax::Literal]"NL34ING001"], [var("accountNumber", [Type]"IBAN", [IBAN]"NL34ING001"), // all possible instances and their current values
                                                    var("balance", [Type]"Money", [Money]"EUR 10.00"),
                                                    var("_state", [Type]"Int", [Int]"1")]),
     instance("Account", [[lang::Syntax::Literal]"NL34ING002"], [var("accountNumber", [Type]"IBAN", [IBAN]"NL34ING002"),
                                                   var("balance", [Type]"Money", [Money]"EUR 20.00"),
                                                   var("_state", [Type]"Int", [Int]"1")]),
     instance("Account", [[lang::Syntax::Literal]"NL34ING003"], [var("_state", [Type]"Int", [Int]"3")]),
     instance("Transaction", [[lang::Syntax::Literal]"1"], [var("_state", [Type]"Int", [Int]"4")])   
  ]);
  
  list[Variable] transitionParams = [
        var("_id", [Type]"Integer", [Int]"1"),
        var("_toState", [Type]"Integer", [Int]"1"),
        var("amount", [Type]"Money", [Money]"EUR 5.00"),
        var("from", [Type]"IBAN", [IBAN]"NL34ING001"),
        var("to", [Type]"IBAN", [IBAN]"NL34ING003"),
        var("bookOn", [Type]"Date", [Date]"13 Jul 2016")
      ];
   
  list[Command] smt = declareSmtTypes(normalizedSpecs) +
                      declareSmtVariables("Transaction", "start", transitionParams, normalizedSpecs) +
                      declareSmtSpecLookup(normalizedSpecs) +
                      translateState(current) +
                      translateTransitionParams("Transaction", "start", transitionParams) +
                      translateEventToSingleAsserts("Transaction", find("start", normalizedSpecs)) +
                      [checkSatisfiable(), getModel()];
    
  writeFile(|project://smtlib2/examples/sim2_gen.smt2|, intercalate("\n", [compile(s) | s <- smt]));   
}

EventDef find(str eventName, set[Module] spcs) = evnt when /EventDef evnt := spcs, "<evnt.name>" == eventName;
EventDef find(str eventName, set[Module] spcs) { throw "Event with name \'<eventName>\' not found in spec \'<spc.spec.name>\'"; }

set[Module] normalizeAllSpecs(set[Module] mods, Refs refs) =
  {normalize(m, mods, refs) | Module m <- mods, /Specification spc := m, canBeNormalized(spc), bprintln("Normalizing <spc.name>")};

bool canBeNormalized(Specification spc) = true 
  when /(SpecModifier)`abstract` !:= spc,
       /(SpecModifier)`external` !:= spc; 

default bool canBeNormalized(Specification _) = false;