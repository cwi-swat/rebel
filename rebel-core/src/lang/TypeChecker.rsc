module lang::TypeChecker

import IO;
import Node;
import ParseTree;
import Set;

import lang::TypeInferrer;
import lang::ExtendedSyntax;

alias TypeCheckerResult = tuple[set[Message], map[loc, Type]]; 

TypeCheckerResult checkTypes(Module modul, set[Module] imports) {
  set[Message] msgs = {};
  map[loc, Type] types = ();

  void checkStatement(Statement stat, Context ctx) {
    set[Message] internalMsg = {};
    map[loc, Type] internalTypes = ();
    
    bottom-up visit(stat) {
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
  }

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
  
    void checkSyncStatements(SyncStatement* stats, Context ctx, str eventName) {
      set[Message] internalMsg = {};
      map[loc, Type] internalTypes = ();
    
      bottom-up visit(stats) {
        case SyncExpr expr: {
          Type inferredTipe = resolveTypeCached(expr, ctx);
          if ((Type)`$$INVALID_TYPE$$` := inferredTipe) {
            internalMsg += error("Type error", expr@\loc);
          } else {
            internalTypes += (expr@\loc : inferredTipe);
          }  
        }
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
    when EventRef er <- modul.spec.eventRefs.events,
         "<er.eventRef>" == eventName;
     
  if (modul has spec) {
    map[str, Type] fields = ("this.<f.name>" : f.tipe | FieldDecl f <- modul.spec.fields.fields);
    map[str, Type] functions = ("<f.name>" : f.returnType | FunctionDef f <- modul.spec.functions.defs);
    map[str, Type] otherSpecs = ("<m.modDef.fqn.modName>" : [Type]"<m.modDef.fqn.modName>" | Module m <- imports + modul, m has spec); 
    
    Scope rootScope = root("<modul.spec.name>", fields, functions, otherSpecs);
    
    for (EventDef ev <- modul.spec.events.events) {
      paramsInEvent = ("<p.name>" : p.tipe | Parameter p <- ev.transitionParams);
      Context ctx = context(nested("<ev.name>", paramsInEvent, rootScope));
      
      if (ev has pre, /Statement* stats := ev.pre) checkStatements(stats, ctx, "<ev.name>");
      if (ev has post, /Statement* stats := ev.post) checkStatements(stats, ctx, "<ev.name>");
      if (ev has sync, /SyncStatement* stats := ev.sync) checkSyncStatements(stats, ctx, "<ev.name>");
    }
    
    for (FunctionDef fd <- modul.spec.functions.defs) {
      paramsInFunction = ("<p.name>" : p.tipe | Parameter p <- fd.params);
      Context ctx = context(nested("<fd.name>", paramsInFunction, rootScope));
      
      checkStatement(fd.statement, ctx);
    }
  }
    
  return <msgs, types>;  
}

@memo
Type resolveTypeCached(SyncExpr exp, Context ctx) = resolveType(exp, ctx);

Type resolveType((SyncExpr)`not <SyncExpr expr>`, Context ctx) = (Type)`Boolean`;
Type resolveType((SyncExpr)`<TypeName specName>[<Expr _>].<VarName _>(<{Expr ","}* _>)`, Context ctx) = getTypeOfSpec("<specName>", ctx.scp);
