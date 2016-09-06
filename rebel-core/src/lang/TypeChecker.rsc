module lang::TypeChecker

import IO;
import Node;
import ParseTree;
import Set;

import lang::TypeInferrer;
import lang::ExtendedSyntax;

alias TypeCheckerResult = tuple[set[Message], map[loc, Type]]; 

TypeCheckerResult checkTypes(Module inlinedModul, set[Module] imports) {
  set[Message] msgs = {};
  map[loc, Type] types = ();

  void checkStatements(Statement* stats, Context ctx, str eventName) {
    set[Message] internalMsg = {};
    map[loc, Type] internalTypes = ();
    
    bottom-up visit(stats) {
      case Expr expr: {
        Type inferredTipe = resolveTypeCached(expr, ctx);
        if ((Type)`$$INVALID_TYPE$$` := inferredTipe) {
          internalMsg += error("Type error", expr@\loc);
        } else {
          internalTypes += (expr@\loc : inferredTipe);
        }  
      }
    }
    
    msgs += internalMsg;
    types += internalTypes;
    
    if (internalMsg != {}) {
      msgs += error("Event definition contains type errors", findEventRef(eventName));
    }
  }
  
  loc findEventRef(str eventName) = er@\loc
    when EventRef er <- inlinedModul.spec.eventRefs.events,
         "<er.eventRef>" == eventName;
     
  if (inlinedModul has spec) {
    map[str, Type] fields = ("this.<f.name>" : f.tipe | FieldDecl f <- inlinedModul.spec.fields.fields);
    map[str, Type] functions = ("<f.name>" : f.returnType | FunctionDef f <- inlinedModul.spec.functions.defs);
    map[str, Type] otherSpecs = ("<m.modDef.fqn.modName>" : [Type]"<m.modDef.fqn.modName>" | Module m <- imports + inlinedModul, m has spec); 
    
    Scope rootScope = root("<inlinedModul.spec.name>", fields, functions, otherSpecs);
    
    for (EventDef ev <- inlinedModul.spec.events.events) {
      paramsInEvent = ("<p.name>" : p.tipe | Parameter p <- ev.transitionParams);
      Context ctx = context(nested("<ev.name>", paramsInEvent, rootScope));
      
      if (/Statement* stats := ev.pre) checkStatements(stats, ctx, "<ev.name>");
      if (/Statement* stats := ev.post) checkStatements(stats, ctx, "<ev.name>");
    }
  }
    
  return <msgs, types>;  
}