module analysis::tests::SimulatorTests

import analysis::Simulator;
import analysis::SimulationLoader;

import lang::Resolver;
import lang::Builder;
import lang::ExtendedSyntax;

import lang::smtlib25::Compiler;
import lang::smtlib25::AST;
import ParseTree;

import IO;
import List;
import util::Maybe; 

test bool testInitialStateSetup() {
  loc file = |project://rebel-core/examples/simple_transaction/Account.ebl|; 
  
  State initial = constructInitialState(getInitialConfiguration(file));
    
  list[Variable] transitionParams = [
        var("_accountNumber", [Type]"IBAN", [IBAN]"NL01INGB0000001"),
        var("_toState", [Type]"Integer", [Int]"2"),
        var("initialDeposit", [Type]"Money", [Money]"EUR 51.00")
      ];
   
  TransitionResult result = transition(file, "simple_transaction.Account", "openAccount", transitionParams, initial);
  
  return successful(_) := result;
}

test bool testStartTransaction() {
  loc file = |project://rebel-core/examples/simple_transaction/Transaction.ebl|; 
  
  set[Module] normalizedSpecs = {b.normalizedMod | Built b <- loadSpecsTransitive(file, {})};

  // Build up the current state, all possible entities must be present, even if they are not initialized
  State current = state(
    1, // state nr
    [DateTime]"12 Jul 2016, 12:00:00", // now 
    [instance("simple_transaction.Account", [[lang::ExtendedSyntax::Literal]"NL01INGB0000001"], [var("accountNumber", [Type]"IBAN", [IBAN]"NL34ING001"), // all possible instances and their current values
                                                    var("balance", [Type]"Money", [Money]"EUR 10.00"),
                                                    var("_state", [Type]"Int", [Int]"1")]),
     instance("simple_transaction.Account", [[lang::ExtendedSyntax::Literal]"NL01INGB0000002"], [var("accountNumber", [Type]"IBAN", [IBAN]"NL34ING002"),
                                                   var("balance", [Type]"Money", [Money]"EUR 20.00"),
                                                   var("_state", [Type]"Int", [Int]"1")]),
     instance("simple_transaction.Account", [[lang::ExtendedSyntax::Literal]"NL01INGB0000003"], [var("_state", [Type]"Int", [Int]"4")]),
     instance("simple_transaction.Transaction", [[lang::ExtendedSyntax::Literal]"1"], [var("_state", [Type]"Int", [Int]"1")])   
  ]);
  
  list[Variable] transitionParams = [
        var("_id", [Type]"Integer", [Int]"1"),
        var("_toState", [Type]"Integer", [Int]"4"),
        var("amount", [Type]"Money", [Money]"EUR 5.00"),
        var("from", [Type]"IBAN", [IBAN]"NL01INGB0000001"),
        var("to", [Type]"IBAN", [IBAN]"NL01INGB0000002"),
        var("bookOn", [Type]"Date", [Date]"12 Jul 2016")
      ];
   
  TransitionResult result = transition(file, "simple_transaction.Transaction", "start", transitionParams, current);
  
  return successful(_) := result;
  
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