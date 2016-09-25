module analysis::tests::SimulatorTests

import analysis::Simulator;

import lang::Resolver;
import lang::Builder;
import lang::ExtendedSyntax;

import lang::smtlib25::Compiler;
import lang::smtlib25::AST;
import ParseTree;

import IO;
import List;
import util::Maybe; 

void testInitializeEntity() {
  loc file = |project://rebel-core/examples/simple_transaction/Transaction.ebl|; 
  
  set[Module] normalizedSpecs = {b.normalizedMod | Built b <- loadSpecsTransitive(file, {})};

  // Build up the current state, all possible entities must be present, even if they are not initialized
  State current = state(
    1, // state nr
    [DateTime]"12 Jul 2016, 12:00:00", // now 
    [instance("Account", [[lang::ExtendedSyntax::Literal]"NL34ING001"], [var("accountNumber", [Type]"IBAN", [IBAN]"NL34ING001"), // all possible instances and their current values
                                                    var("balance", [Type]"Money", [Money]"EUR 10.00"),
                                                    var("_state", [Type]"Int", [Int]"1")]),
     instance("Account", [[lang::ExtendedSyntax::Literal]"NL34ING002"], [var("accountNumber", [Type]"IBAN", [IBAN]"NL34ING002"),
                                                   var("balance", [Type]"Money", [Money]"EUR 20.00"),
                                                   var("_state", [Type]"Int", [Int]"1")]),
     instance("Account", [[lang::ExtendedSyntax::Literal]"NL34ING003"], [var("_state", [Type]"Int", [Int]"3")]),
     instance("Transaction", [[lang::ExtendedSyntax::Literal]"1"], [var("_state", [Type]"Int", [Int]"4")])   
  ]);
  
  list[Variable] transitionParams = [
        var("_id", [Type]"Integer", [Int]"1"),
        var("_toState", [Type]"Integer", [Int]"1"),
        var("amount", [Type]"Money", [Money]"EUR 5.00"),
        var("from", [Type]"IBAN", [IBAN]"NL34ING001"),
        var("to", [Type]"IBAN", [IBAN]"NL34ING002"),
        var("bookOn", [Type]"Date", [Date]"13 Jul 2016")
      ];
   
  list[Command] smt = transition("Transaction", "start", transitionParams, current, normalizedSpecs);
    
  writeFile(|project://smtlib2/examples/sim2_gen.smt2|, intercalate("\n", [compile(s) | s <- smt]));   
}

set[Built] loadSpecsTransitive(loc origin, set[Built] alreadyLoaded) {
  bool isAlreadyLoaded(loc b) = b.top in {al.normalizedMod@\loc.top | al <- alreadyLoaded};
  
  set[Built] loaded  = {};
  if (<set[Message] _, just(Built b)> := load(origin)) {
    if (b.normalizedMod has spec) {
      loaded += b;
    }
    
    for (<_, loc def> <- b.refs.imports, !isAlreadyLoaded(def)) {
      loaded += loadSpecsTransitive(def.top, alreadyLoaded + b);
    }
  }
  
  return loaded;
}