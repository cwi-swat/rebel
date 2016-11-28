module testlang::Checker

import testlang::Resolver;
import testlang::Syntax;

import Message;
import ParseTree;

set[Message] checkReferences(TestModule m, TestRefs refs) =
  checkImports(m, refs.imports) +
  checkSpecs(m, refs.specs) +
  checkStates(m, refs.states) +
  checkFields(m, refs.fields);
  
set[Message] checkImports(TestModule m, Reff importRefs) =
  {error("Unable to locate imported module", i.fqn@\loc) | Import i <- m.imports, importRefs[i.fqn@\loc] == {}}; 

set[Message] checkSpecs(TestModule m, Reff specRefs) =
  {error("Unable to locate referenced specification", spec@\loc) | (TestDef)`<StateSetup setup>` <- m.testDefs, /(SetupStatement)`<Int? _> <StateRef? _> <TypeName spec> <FieldValueDeclarations? _>;` := setup, specRefs[spec@\loc] == {}}; 

set[Message] checkStates(TestModule m, Reff stateRefs) =
  {error("Unable to locate referenced state in specification", state@\loc) | (TestDef)`<StateSetup setup>` <- m.testDefs, /(SetupStatement)`<Int? _> <VarName state> <TypeName _> <FieldValueDeclarations? _>;` := setup, stateRefs[state@\loc] == {}};

set[Message] checkFields(TestModule m, Reff fieldRefs) =
  {error("Unable to locate referenced field in specification", field@\loc) | (TestDef)`<StateSetup setup>` <- m.testDefs, /(FieldValueDeclaration)`<VarName field> = <Expr _>` := setup, fieldRefs[field@\loc] == {}};