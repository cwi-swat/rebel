module testlang::Resolver

extend lang::Resolver;

import lang::Builder;

import testlang::Syntax;
import lang::ExtendedSyntax;

import ParseTree;

alias TestRefs = tuple[Reff imports, Reff specs, Reff states, Reff fields, Reff setupRefs];

TestRefs resolveTestRefs(TestModule m, set[Built] imports) =
  <resolveImports(m, imports), resolveSpecs(m, imports), resolveStates(m, imports), resolveFields(m, imports), resolveSetupRefs(m, imports)>;
  
Reff resolveImports(TestModule m, set[Built] imports) {
  map[str,loc] defs = ("<b.normalizedMod.modDef.fqn>" : b.normalizedMod@\loc | Built b <- imports);
  return {<i.fqn@\loc,defs["<i.fqn>"]> | Import i <- m.imports, "<i.fqn>" in defs}; 
}

Reff resolveSpecs(TestModule m, set[Built] imports) {
  map[str,loc] defs = ("<b.normalizedMod.spec.name>" : b.normalizedMod.spec@\loc | Built b <- imports, b.normalizedMod has spec);
  return {<spec@\loc, defs["<spec>"]> | (TestDef)`<StateSetup setup>` <- m.testDefs, /(SetupStatement)`<Int? _> <StateRef? _> <TypeName spec> <FieldValueDeclarations? _>;` := setup, "<spec>" in defs};
}

Reff resolveStates(TestModule m, set[Built] imports) {
  map[str, map[str,loc]] defs = ("<b.normalizedMod.spec.name>" : ("<sf.from>":sf.from@\loc | StateFrom sf <-  b.normalizedMod.spec.lifeCycle.from) | Built b <- imports, b.normalizedMod has spec);
  return {<state@\loc, defs["<spec>"]["<state>"]> | (TestDef)`<StateSetup setup>` <- m.testDefs, /(SetupStatement)`<Int? _> <VarName state> <TypeName spec> <FieldValueDeclarations? _>;` := setup, "<spec>" in defs, "<state>" in defs["<spec>"]};
}

Reff resolveFields(TestModule m, set[Built] imports) {
  map[str, map[str,loc]] defs = ("<b.normalizedMod.spec.name>" : ("<f.name>":f@\loc | FieldDecl f <-  b.normalizedMod.spec.fields.fields) | Built b <- imports, b.normalizedMod has spec);
  return {<field@\loc, defs["<spec>"]["<field>"]> | 
    (TestDef)`<StateSetup setup>` <- m.testDefs, /(SetupStatement)`<Int? _> <VarName _> <TypeName spec> <FieldValueDeclarations? fvd>;` := setup, "<spec>" in defs, 
    /(FieldValueDeclaration)`<VarName field> <Expr _>` := fvd, "<field>" in defs["<spec>"]};
}

Reff resolveSetupRefs(TestModule m, set[Built] imports) {
  map[str,loc] defs = ("<s.name>" : s@\loc | (TestDef)`<StateSetup s>` <- m.testDefs);
  return {<r@\loc, defs["<r>"]> | /(CheckStatement)`<VarName r> reachable <StepBounds _>;` := m.testDefs, "<r>" in defs};
}