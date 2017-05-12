@license{
  Copyright (c) 2009-2015 CWI
  All rights reserved. This program and the accompanying materials
  are made available under the terms of the Eclipse Public License v1.0
  which accompanies this distribution, and is available at
  http://www.eclipse.org/legal/epl-v10.html
}
@doc{
  Synopsis: Translate the SMTLIBv2 AST to string so that it can be interpreted by a SMTLIBv2 compliant solver 
}
@contributor{Jouke Stoel - stoel@cwi.nl (CWI)}

module lang::smtlib25::Compiler

import lang::smtlib25::AST;

import List;

list[str] compile(Script script) = compile(script.commands);
list[str] compile(list[Command] commands, bool skipComments=true) {
  list[str] smt = [];
  
  for (Command c <- commands) { 
    if ((comment(str _) := c && !skipComments) || comment(str _) !:= c) {
      smt += compile(c);
    }
  }
  
  return smt;
}
 
// Commands
str compile(setLogic(logic)) = "(not yet implemented)";
str compile(setOption(option)) = "(set-option <compile(option)>)";
str compile(setInfo(info)) = "(not yet implemented)";
str compile(declareSort(name)) = "(declare-sort <name>)";
str compile(declareSort(name, arity)) = "(declare-sort <name> <arity>)";
str compile(defineSort(str name, list[str] sorts, Sort sort)) = "(define-sort <name> (<("" | "<it> <s>" | s <- sorts)>) <compile(sort)>)";
str compile(declareConst(name, tipe)) = "(declare-const <name> <compile(tipe)>)";
str compile(declareFunction(name, params, returnType)) = "(declare-fun <name> (<compile(params)>) <compile(returnType)>)";
str compile(defineFunction(name, params, returnType, body)) = "(define-fun <name> (<compile(params)>) <compile(returnType)> <compile(body)>)";
str compile(\assert(expr)) = "(assert <compile(expr)>)";
str compile(checkSatisfiable()) = "(check-sat)";
str compile(getValue(exprs)) = "(get-value (<(""| "<it> <compile(expr)>" | expr <- exprs )>))";
str compile(getModel()) = "(get-model)";
str compile(comment(str c)) = ";<c>";
str compile(getUnsatCore()) = "(get-unsat-core)";
str compile(push(nr)) = "(push <nr>)";
str compile(pop(nr)) = "(pop <nr>)";
str compile(exit()) = "(exit)";
str compile(declareDataTypes(list[str] typeNames, list[DataTypeDefinition] definitions)) 
  = "(declare-datatypes (<intercalate(" ", [n | n <- typeNames])>) ( <("" | "<it> ( <compile(dtd)> )" | dtd <- definitions)> ))";
str compile(comment(str com)) = "; <com>";
default str compile(Command command) = "(unknown command \'<command>\')";

str compile(dataTypeDef(str typeName, list[Constructor] cons)) = "<typeName> <intercalate(" ", ["(<compile(c)>)" | c <- cons])>";

str compile(combinedCons(str name, list[SortedVar] sortedVars)) = "<name> <compile(sortedVars)>"; 
str compile(cons(str name)) = "<name>";

str compile(exists(list[SortedVar] sortedVar, Formula expr)) = "(exists (<compile(sortedVar)>) <compile(expr)>)";
str compile(forall(list[SortedVar] sortedVar, Formula expr)) = "(forall (<compile(sortedVar)>) <compile(expr)>)"; 

// Options
//str compile(interactiveMode(val)) = ":interactive-mode <val>";
//str compile(printSuccess(bool val)) = ":print-success <val>";
//str compile(regularOutputChannel(channel)) = ":regular-output-channel <channel>";
//str compile(diagnosticOutputChannel(str channel)) = ":diagnostic-output-channel <channel>";
//str compile(expandDefinitions(bool val)) = ":expand-definitions <val>";
//str compile(produceProofs(bool val)) = ":produce-proofs <val>";
//str compile(produceUnsatCores(bool val)) = ":produce-unsat-cores <val>";
//str compile(produceModels(bool val)) = ":produce-models <val>";
//str compile(produceAssignments(bool val)) = ":produce-assignments <val>";
//str compile(randomSeed(int seed)) = ":random-seed <seed>";
//str compile(verbosity(int level)) = ":verbosity <level>";
str compile(custom(str name, str val)) = ":<name> <val>";

// Sorts
str compile(list[SortedVar] params) = ("" | "<it> (<param.name> <compile(param.sort)>)" | param <- params); 
str compile(list[Sort] sorts) = ("" | "<it> <compile(sort)>" | Sort sort <- sorts); 
str compile(\integer()) = "Int";
str compile(\boolean())= "Bool";
str compile(string()) = "String";
str compile(array(Sort idx, Sort elems))= "(Array <compile(idx)> <compile(elems)>)";
str compile(custom(str name)) = name;
str compile(combined(list[Sort] sorts)) = "(<compile(sorts)>)";

// Literals
str compile(boolVal(b)) = b ? "true" : "false";
str compile(intVal(i)) = "<i>";  
str compile(strVal(s)) = "\"<s>\"";
str compile(adt(str consName, list[Formula] vals)) = "(<consName> <intercalate(" ", [compile(f) | Formula f <- vals])>)";

// Formula
str compile(list[Formula] exprs) = ("" | "<it> <compile(exp)>" | exp <- exprs);
str compile(var(name)) = "<compile(name)>";
str compile(lit(Literal lit)) = compile(lit);
str compile(functionCall(functionName, params)) = "(<compile(functionName)> <("" | "<it> <compile(param)>" | param <- params)>)";
str compile(forall(vars, term)) = "(forall (<compile(vars)>) <compile(term)>)";
str compile(exists(vars, term)) = "(exists (<compile(vars)>) <compile(term)>)";
str compile(attributed(term, attributes)) = "(! <compile(term)> <compile(attributes)>)";

str compile(cons(str name)) = "(<name>)";
 
// QualifiedId
str compile(as(str name, Sort sort)) = "(as <name> <compile(sort)>)";
str compile(simple(str name)) = name;
 
// From core
str compile(\not(val)) = "(not <compile(val)>)";
str compile(implies(lhs, rhs)) = "(=\> <compile(lhs)> <compile(rhs)>)";
str compile(and(list[Formula] clauses)) = "(and <intercalate(" ", [compile(c) | c <- clauses])>)";
str compile(or(list[Formula] clauses)) = "(or <intercalate(" ", [compile(c) | c <- clauses])>)";
str compile(xor(list[Formula] clauses)) = "(xor <intercalate(" ", [compile(c) | c <- clauses])>)";
str compile(equal(lhs, rhs)) = "(= <compile(lhs)> <compile(rhs)>)";
str compile(distinct(list[Formula] clauses)) = "(distinct <intercalate(" ", [compile(c) | c <- clauses])>)";
str compile(ite(condition, whenTrue, whenFalse)) = "(ite <compile(condition)> <compile(whenTrue)> <compile(whenFalse)>)";   

// From ints
str compile(neg(val)) = "(- <compile(val)>)";
str compile(sub(lhs, rhs)) = "(- <compile(lhs)> <compile(rhs)>)";
str compile(add(lhs, rhs)) = "(+ <compile(lhs)> <compile(rhs)>)";
str compile(mul(lhs, rhs)) = "(* <compile(lhs)> <compile(rhs)>)";
str compile(div(lhs, rhs)) = "(div <compile(lhs)> <compile(rhs)>)";
str compile(\mod(lhs, rhs)) = "(mod <compile(lhs)> <compile(rhs)>)";
str compile(abs(val)) = "(abs <compile(val)>)";
str compile(lte(lhs, rhs)) = "(\<= <compile(lhs)> <compile(rhs)>)";
str compile(lt (lhs, rhs)) = "(\< <compile(lhs)> <compile(rhs)>)";
str compile(gte(lhs, rhs)) = "(\>= <compile(lhs)> <compile(rhs)>)";
str compile(gt (lhs, rhs)) = "(\> <compile(lhs)> <compile(rhs)>)";

// From array
str compile(select(arr, idx)) = "(select <compile(arr)> <compile(idx)>)";
str compile(store(arr, idx, val)) = "(store <compile(arr)> <compile(idx)> <compile(val)>)";

// Attributes
str compile(list[Attribute] attributes) = ("" | "<it> <compile(att)>" | att <- attributes);
str compile(named(name)) = ":named <name>";
str compile(pattern(exprs)) = "<("" | "<it> :pattern <compile(e)>" | e <- exprs)>";
