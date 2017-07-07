module analysis::tests::SimulatorTests

import analysis::Simulator;
import analysis::SimulationHelper;
import analysis::CommonAnalysisFunctions;

import lang::Resolver; 
import lang::Builder;
import lang::ExtendedSyntax;

import lang::smtlib25::Compiler;
import lang::smtlib25::AST;
import ParseTree; 

import IO;
import String;
import List;
import util::Maybe; 

test bool testInitialStateSetup() {
  loc file = |project://rebel-core/examples/simple_transaction/Account.ebl|; 

  set[Built] allSpecs = loadAllSpecs(file, {});  
  map[loc, Type] resolvedTypes = (() | it + b.resolvedTypes | Built b <- allSpecs);
     
  State initial = constructInitialState(getInitialConfiguration(file));
  list[Variable] transitionParams = buildTransitionParams("simple_transaction.Account", "openAccount", "opened", var("accountNumber", "NL01INGB0000001"), [var("initialDeposit", "EUR 51.00")], allSpecs);
      
  TransitionResult result = step("simple_transaction.Account", "openAccount", transitionParams, initial, allSpecs, resolvedTypes);
  
  if (successful(State new) := result) {
    printState(new, allSpecs);
    return true;
  } 
   
  return false;
}

test bool testStartTransaction() {
  loc file = |project://rebel-core/examples/simple_transaction/Transaction.ebl|; 
  
  set[Built] allSpecs = loadAllSpecs(file, {});  
  map[loc, Type] resolvedTypes = (() | it + b.resolvedTypes | Built b <- allSpecs);

  EntityInstance account1     = buildInstance("simple_transaction.Account", var("accountNumber", "NL01INGB0000001"), "opened", [var("balance", "EUR 10.00")], allSpecs);
  EntityInstance account2     = buildInstance("simple_transaction.Account", var("accountNumber", "NL01INGB0000002"), "opened", [var("balance", "EUR 20.00")], allSpecs);
  EntityInstance account3     = buildInstance("simple_transaction.Account", var("accountNumber", "NL01INGB0000003"), "closed", [var("balance", "EUR 0.00")], allSpecs);
  EntityInstance transaction  = buildInstance("simple_transaction.Transaction", var("id", "1"), "uninit", [], allSpecs);

  State current = buildState("12 Jul 2016, 12:00:00", [account1, account2, account3, transaction]);
  
  list[Variable] transitionParams = buildTransitionParams("simple_transaction.Transaction", "start", "validated", var("id", "1"), 
    [var("amount", "EUR 10.00"), var("from", "NL01INGB0000001"), var("to", "NL01INGB0000002")], allSpecs);
     
  TransitionResult result = step("simple_transaction.Transaction", "start", transitionParams, current, allSpecs, resolvedTypes);
  
  if (successful(State new) := result) {
    printState(new, allSpecs);
    return true;
  } 
  
  return false;
}

test bool testOpenAccountWithAnyAmount() {
  loc file = |project://rebel-core/examples/simple_transaction/Account.ebl|; 
  
  set[Built] allSpecs = loadAllSpecs(file, {});  
  map[loc, Type] resolvedTypes = (() | it + b.resolvedTypes | Built b <- allSpecs);

  EntityInstance account     = buildInstance("simple_transaction.Account", var("accountNumber", "NL01INGB0000001"), "init", [], allSpecs);

  State current = buildState("12 Jul 2016, 12:00:00", [account]);
  
  list[Variable] transitionParams = buildTransitionParams("simple_transaction.Account", "openAccount", "opened", var("accountNumber", "NL01INGB0000001"), 
    [var("initialDeposit", "ANY")], allSpecs);
     
  TransitionResult result = step("simple_transaction.Account", "openAccount", transitionParams, current, allSpecs, resolvedTypes);
  
  if (successful(State new) := result) {
    printState(new, allSpecs);
    return true;
  } 
  
  return false;
}

test bool testStartTransactionAndThenBook() {
  loc file = |project://rebel-core/examples/simple_transaction/Transaction.ebl|; 
  
  set[Built] allSpecs = loadAllSpecs(file, {});  
  map[loc, Type] resolvedTypes = (() | it + b.resolvedTypes | Built b <- allSpecs);

  EntityInstance account1     = buildInstance("simple_transaction.Account", var("accountNumber", "NL01INGB0000001"), "opened", [var("balance", "EUR 10.00")], allSpecs);
  EntityInstance account2     = buildInstance("simple_transaction.Account", var("accountNumber", "NL01INGB0000002"), "opened", [var("balance", "EUR 20.00")], allSpecs);
  EntityInstance transaction  = buildInstance("simple_transaction.Transaction", var("id", "1"), "uninit", [], allSpecs);

  State current = buildState("12 Jul 2016, 12:00:00", [account1, account2, transaction]);
  
  list[Variable] transitionParams1 = buildTransitionParams("simple_transaction.Transaction", "start", "validated", var("id", "1"), 
    [var("amount", "EUR 5.00"), var("from", "NL01INGB0000001"), var("to", "NL01INGB0000002")], allSpecs);
     
  TransitionResult result1 = step("simple_transaction.Transaction", "start", transitionParams1, current, allSpecs, resolvedTypes);
  
  if (successful(State next) := result1) {
    list[Variable] transitionParams2 = buildTransitionParams("simple_transaction.Transaction", "book", "booked", var("id", "1"), [], allSpecs);
    TransitionResult result2 = step("simple_transaction.Transaction", "book", transitionParams2, next, allSpecs, resolvedTypes);
    
    if (successful(State next2) := result2) {
      printState(next, allSpecs);
      printState(next2, allSpecs);
      return true;
    }         
    
    return false;
  } 
  
  return false;
}

test bool testTransactionCannotBeBooked() {
  loc file = |project://rebel-core/examples/simple_transaction/Transaction.ebl|; 
  
  set[Built] allSpecs = loadAllSpecs(file, {});  
  map[loc, Type] resolvedTypes = (() | it + b.resolvedTypes | Built b <- allSpecs);

  EntityInstance account1     = buildInstance("simple_transaction.Account", var("accountNumber", "NL01INGB0000001"), "opened", [var("balance", "EUR 10.00")], allSpecs);
  EntityInstance account2     = buildInstance("simple_transaction.Account", var("accountNumber", "NL01INGB0000002"), "opened", [var("balance", "EUR 10.00")], allSpecs);
  EntityInstance transaction  = buildInstance("simple_transaction.Transaction", var("id", "1"), "validated", [var("from", "NL01INGB0000001"), var("to", "NL01INGB0000002"), var("amount", "EUR 15.00")], allSpecs);

  State current = buildState("12 Jul 2016, 12:00:00", [account1, account2, transaction]);
  
  list[Variable] transitionParams = buildTransitionParams("simple_transaction.Transaction", "book", "booked", var("id", "1"), [], allSpecs);
     
  TransitionResult result = step("simple_transaction.Transaction", "book", transitionParams, current, allSpecs, resolvedTypes);
  
  if (failed(list[str] reasons) := result) {
    println("Transition failed because of reason:");
    for(str r <- reasons) { println(r); }
        
    return true;
  } 
  
  return false;
}

test bool testOpenAccountWhileFramingOtherEntities() {
  loc file = |project://rebel-core/examples/simple_transaction/Account.ebl|; 
  
  set[Built] allSpecs = loadAllSpecs(file, {});  
  map[loc, Type] resolvedTypes = (() | it + b.resolvedTypes | Built b <- allSpecs);

  EntityInstance account1     = buildInstance("simple_transaction.Account", var("accountNumber", "NL01INGB0000001"), "init", [], allSpecs);
  EntityInstance account2     = buildInstance("simple_transaction.Account", var("accountNumber", "NL01INGB0000002"), "opened", [var("balance", "EUR 10.00")], allSpecs);
  EntityInstance account3     = buildInstance("simple_transaction.Account", var("accountNumber", "NL01INGB0000003"), "opened", [var("balance", "EUR 30.00")], allSpecs);

  State current = buildState("12 Jul 2016, 12:00:00", [account1, account2, account3]);
  
  list[Variable] transitionParams = buildTransitionParams("simple_transaction.Account", "openAccount", "opened", var("accountNumber", "NL01INGB0000001"), [var("initialDeposit", "EUR 55.00")], allSpecs);

  TransitionResult result = step("simple_transaction.Account", "openAccount", transitionParams, current, allSpecs, resolvedTypes);

  if (successful(State new) := result) {
    printState(new, allSpecs);
   
    if (EntityInstance ei <- new.instances, /Expr id := ei.id, "<id>" == "NL01INGB0000002", /var("balance",_, Expr val) := ei.vals, "<val>" != "EUR10.00") {
      println("The balance of account NL01INGB0000002 changed");
      return false;
    }
    if (EntityInstance ei <- new.instances, /Expr id := ei.id, "<id>" == "NL01INGB0000003", /var("balance",_, Expr val) := ei.vals, "<val>" != "EUR30.00") {
      println("The balance of account NL01INGB0000003 changed");
      return false;
    }
    
    return true;
  } 
  
  println("Transition should be posible but failed for some reason");
  return false;

}
