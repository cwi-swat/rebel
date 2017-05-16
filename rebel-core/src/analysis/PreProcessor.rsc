module analysis::PreProcessor

import lang::Builder;
import lang::ExtendedSyntax;
import lang::Finder;
import lang::Resolver;

import List;
import util::Maybe;
import ParseTree;
import String;
import IO;
import Set;

import analysis::graphs::Graph;


alias PreProcessorResult = tuple[lrel[Built, EventDef] events, list[FunctionDef] functions];

PreProcessorResult preprocess(set[Built] allBuilts) {
  map[loc, Type] types = (() | it + b.resolvedTypes | b <- allBuilts);
  
  list[FunctionDef] functions = getAllFunctionsOrderedByCallOrder(allBuilts);
  lrel[Built, EventDef] events = getAllEventsOrderedByCallOrder(allBuilts);
  
  events = rewriteInStateExpression(events, types, allBuilts);
  events = addToStateAndIdToSyncedEventCalls(events, allBuilts);
  events = addSyncedInstances(events, allBuilts);
  
  return <events, functions>;    
}

list[FunctionDef] getAllFunctionsOrderedByCallOrder(set[Built] specs) {
  Graph[FunctionDef] getFunctionCallOrder(FunctionDef currentFunc, Built currentBuild) {
    rel[FunctionDef, FunctionDef] calledFunctions = {}; //<currentFunc, currentFunc>};
    
    for (<loc ref, loc def> <- currentBuild.refs.functionRefs,
         contains(currentFunc@\loc, ref),
         just(FunctionDef calledFunc) := findFunctionDef(def, specs)) {
      
      calledFunctions += <currentFunc, calledFunc>;
    }
    
    return calledFunctions;
  }
  
  Graph[FunctionDef] callOrder = {};
  list[FunctionDef] ordered = []; 
  
  for (Built b <- specs, b.normalizedMod has spec, FunctionDef f <- b.normalizedMod.spec.functions.defs) {
    Graph[FunctionDef] partial = getFunctionCallOrder(f, b);
    if (partial == {}) {
      ordered += f;
    } else {
      callOrder += partial;
    }
  }
    
  return dup(ordered + reverse(order(callOrder)));
}

lrel[Built, EventDef] getAllEventsOrderedByCallOrder(set[Built] specs) {
  Graph[EventDef] getSyncedEvents(EventDef currentEvent, Built currentBuilt, set[Built] allBuilts) {
    Graph[EventDef] syncedEvents = {};
  
    for (<loc ref, loc def> <- currentBuilt.refs.syncedEventRefs, 
         contains(currentEvent@\loc, ref),
         just(Built b) := findBuilt(def, allBuilts), 
         {loc eventDef} := b.refs.eventRefs[def], 
         just(EventDef syncedEvnt) := findNormalizedEventDef(eventDef, allBuilts)) {
      
      syncedEvents += <currentEvent, syncedEvnt>;
    }
    
    return syncedEvents;
  }

  void printGraph(Graph[EventDef] syncGraph) {
    void pr(EventDef cur, str indent) {
      for (EventDef to <- syncGraph[cur]) {
        pr(to, "<indent>  ");
      }
    }
    
    str indent = "";
    for (EventDef evnt <- top(syncGraph)) {
      pr(evnt, "");
    }
  }

  Graph[EventDef] callOrder = {};
  list[EventDef] ordered = [];
  
  for (Built b <- specs, b.normalizedMod has spec, EventDef e <- b.normalizedMod.spec.events.events) {
      // the event has synced events, the call order should be decided
    Graph[EventDef] partial = getSyncedEvents(e,b,specs);
    if (partial == {}) {
      ordered += e;
    } else {
      callOrder += partial;
   }
  }
  
  //println("Printing event sync order graph. Size of graph = <size(callOrder)>, size of top of graph = <size(top(callOrder))>");
  //printGraph(callOrder);
  
  ordered = dup(ordered + reverse(order(callOrder)));
 
  return [<b, e> | EventDef e <- ordered, just(Built b) := findBuiltBeloningToEvent(e@\loc, specs)];
}

lrel[Built, EventDef] rewriteInStateExpression(lrel[Built, EventDef] events, map[loc, Type] types, set[Built] allBuilts) {
  Maybe[str] construct(str spc, str id, VarName state, Built b) {
      if (b.refs.stateRefs[state@\loc] == {}) {
        return nothing();      
      }
            
      if ({r} := b.refs.stateRefs[state@\loc], just(StateFrom sf) := findNormalizedStateFrom(r, allBuilts)) {
        return just("<spc>[<id>]._state == <sf.nr>");
      }
  } 

  Maybe[Expr] rewrite(Built b, (Expr)`<Expr spc>[<Expr id>] instate <StateRef sr>`) {
    if((StateRef)`<VarName state>` := sr, just(str expr) := construct("<spc>", "<id>", state, b)) {
      return just([Expr]"<expr>");
    }
    else if ((StateRef)`<VarName+ states>` := sr) {
      list[str] exprs = [expr | VarName state <- states, just(str expr) := construct("<spc>", "<id>", state, b)];
      return just([Expr]"<intercalate(" || ", exprs)>");
    }    
  }

  Maybe[Expr] rewrite(Built b, e:(Expr)`new <Expr spc>[<Expr id>] instate <StateRef sr>`) {
    if((StateRef)`<VarName state>` := sr, just(str expr) := construct("<spc>", "<id>", state, b)) {
      return just([Expr]"new <expr>");
    }
  }
      
  EventDef rewrite(Built b, EventDef orig) = bottom-up visit(orig) {
    case e:(Expr)`<Expr spc>[<Expr _>] instate <StateRef state>` => newExpr[@\loc = e@\loc] when just(Expr newExpr) := rewrite(b, e)
    case e:(Expr)`new <Expr spc>[<Expr _>] instate <StateRef state>` => newExpr[@\loc = e@\loc] when just(Expr newExpr) := rewrite(b, e)
  };
  
  return [<b, rewrite(b, evnt)> | <Built b, EventDef evnt> <- events];
}

lrel[Built, EventDef] addSyncedInstances(lrel[Built, EventDef] events, set[Built] allBuilts) {
  SyncInstances merge((SyncInstances)`syncInstances { <Statement* stats> }`, Statement newStat) = 
    (SyncInstances)`syncInstances {
                   '  <Statement* stats>
                   '  <Statement newStat>
                   '}`; 
  
  EventDef add(EventDef evnt, Built b) {
    if ([Expr key] := [[Expr]"_<field>" | (FieldDecl)`<VarName field>: <Type tipe> @key` <- b.normalizedMod.spec.fields.fields]) {
      set[Statement] result = findSyncedInstances(key, evnt, b, allBuilts);
    
      return visit(evnt) {
        case orig:(EventDef)`<Annotations annos> event <FullyQualifiedVarName name><EventConfigBlock? configParams>(<{Parameter ","}* transitionParams>){<Preconditions? pre> <Postconditions? post> <MaybeSyncBlock sync>}` =>
          (EventDef)`<Annotations annos> event <FullyQualifiedVarName name><EventConfigBlock? configParams>(<{Parameter ","}* transitionParams>){
            ' <Preconditions? pre>
            ' <Postconditions? post>
            ' <MaybeSyncBlock sync>
            ' <SyncInstances si>
            '}`[@\loc=orig@\loc]
          when SyncInstances si := ((SyncInstances)`syncInstances {}` | merge(it, stat) | Statement stat <- result)
      }
    } else {
      throw "Currently no Specification with more (or less) than 1 key are supported";
    }
  }
  
  return [<b, add(evnt, b)> | <Built b, EventDef evnt> <- events];
}

lrel[Built, EventDef] addToStateAndIdToSyncedEventCalls(lrel[Built, EventDef] events, set[Built] allBuilts) {
  SyncExpr merge(orig:(SyncExpr)`<TypeName specName>[<Expr id>].<VarName event>(<{Expr ","}* params>)`, Expr newParam) =
    (SyncExpr)`<TypeName specName>[<Expr id>].<VarName event>(<{Expr ","}* params>, <Expr newParam>)`[@\loc=orig@\loc];
  
  Expr consToStateArg(str evnt, Module spc) {
    list[int] possibleStates = [];
    for (/LifeCycle lc := spc.spec.lifeCycle, StateFrom sf <- lc.from, (StateTo)`-\> <VarName to>: <StateVia via>` <- sf.destinations, VarName e <- via.refs, "<e>" == evnt, StateFrom targetState <- lc.from, "<targetState.from>" == "<to>") {
      possibleStates += toInt("<targetState.nr>");      
    }
    
    return [Expr]"<intercalate(" || ",  dup(possibleStates))>";
  }
  
  Maybe[Module] findMod(loc eventRefLoc) {
    for (Built b <- allBuilts, contains(b.normalizedMod@\loc, eventRefLoc)) {
      return just(b.normalizedMod);
    }
    
    return nothing();
  } 
  
  SyncExpr addParams(orig:(SyncExpr)`<TypeName specName>[<Expr id>].<VarName event>(<{Expr ","}* params>)`, Built b) {
    SyncExpr result = orig;
    
    if ({loc eventRef} := b.refs.syncedEventRefs[event@\loc], just(Module m) := findMod(eventRef)) {
      result = merge(orig, consToStateArg("<event>", m));
      result = merge(result, id);
    } 
    
    return result;
  }  
  
  default SyncExpr addParams(SyncExpr exp, Built b) { throw "Adding parameters to \'<exp>\' not yet implemented"; }
  
  EventDef addParamNames(EventDef orig, Built b) {
    if (/SyncBlock _ !:= orig.sync) {
      return orig;
    }
    
    return visit(orig) {
      case se:(SyncExpr)`<TypeName specName>[<Expr id>].<VarName event>(<{Expr ","}* params>)` => addParams(se, b)
    }
  }
  
  return [<b, addParamNames(evnt, b)> | <Built b, EventDef evnt> <- events];
}

set[Statement] findSyncedInstances(Expr newId, EventDef evnt, Built origin, set[Built] allSpecs) {
  Expr findEnclosingSyncExprId(loc ref) = id
    when evnt has sync,
         /e:(SyncExpr)`<TypeName _>[<Expr id>].<VarName _>(<{Expr ","}* _>)` := evnt.sync,
         contains(e@\loc, ref);
           
  set[Statement] instances = {}; 
  
  if ([str key] := ["_<field>" | (FieldDecl)`<VarName field>: <Type tipe> @key` <- origin.normalizedMod.spec.fields.fields]) {

    evnt = visit(evnt) {
      case (Expr)`<Expr spc>[<Expr id>]` => (Expr)`<Expr spc>[<Expr newId>]` 
        when "<spc>" == "<origin.normalizedMod.spec.name>",
             "<id>" == "<key>"
    } 
    
    top-down visit(evnt) {
      case e:(Expr)`<Expr spc>[<Expr _>]`: {
        if ("<spc>" == "<origin.normalizedMod.spec.name>") {
          instances += [Statement]"<e>;";
        }
      }
    } 

    for (<loc ref, loc def> <- origin.refs.syncedEventRefs, contains(evnt@\loc, ref), Expr syncedId := findEnclosingSyncExprId(ref)) {
      if (just(Built b) := findBuilt(def, allSpecs), {loc eventDef} := b.refs.eventRefs[def], just(EventDef syncedEvnt) := findNormalizedEventDef(eventDef, allSpecs)) {
        instances += findSyncedInstances(syncedId, syncedEvnt, b, allSpecs);
      }  
    }
  }
  
  return instances;
}
