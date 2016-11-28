module testlang::TypeChecker

import lang::TypeInferrer;
import testlang::Syntax;
import lang::ExtendedSyntax;
import lang::Builder;

import Message;
import ParseTree;

alias TypeCheckerResult = tuple[set[Message] messages, map[loc, Type] resolvedTypes]; 

data Scope = testScope(map[str, Type] vars); 

TypeCheckerResult checkTypes(TestModule modul, set[Built] importedSpecs) {
  set[Message] msgs = {};
  map[loc, Type] types = ();

  map[str, Type] findFieldsOfSpec(str spc) {
    for (Built b <- importedSpecs, b.normalizedMod has spec, "<b.normalizedMod.spec.name>" == spc) {
      return ("<f.name>": f.tipe | FieldDecl f <- b.normalizedMod.spec.fields.fields); 
    } 
  }

  for (TestDef td <- modul.testDefs, /StateSetup setup := td, (SetupStatement)`<Int? _> <StateRef? _> <TypeName entity> <FieldValueConstraints? constraints>;` <- setup.body) {
    Context ctx = context(testScope(findFieldsOfSpec("<entity>")));
    
    bottom-up visit(constraints) {
      case Expr expr: {
          Type inferredTipe = resolveTypeCached(expr, ctx);
          
          if ((Type)`$$INVALID_TYPE$$` := inferredTipe) {
            msgs += error("Type error", expr@\loc);
          } else {
            types += (expr@\loc : inferredTipe);
          }  
      }
    }
  }
  
  return <msgs, types>;
 
}