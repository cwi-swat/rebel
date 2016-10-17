module analysis::CommonAnalysisFunctions

import lang::ExtendedSyntax;
import lang::Builder;
import lang::Resolver;
import lang::Finder;

import lang::smtlib25::AST;
import lang::smtlib25::Compiler;
import solver::SolverRunner;

import analysis::SmtResponseTranslator;
import analysis::LocTranslator;

import IO;
import Set;
import String;
import List;
import Map;
import util::Maybe;
import util::Math;
import ParseTree;
import Boolean;
import analysis::graphs::Graph;

alias RebelLit = lang::ExtendedSyntax::Literal;

data StringConstantPool = scp(str (int) toStr, int (str) toInt);

data Context(map[str,str] specLookup = (), map[loc, Type] types = ())
  = context(str spec, str event)
  | flattenedEvent(str spec, str event)
  | eventAsFunction()
  | function()
  ;

data Step 
  = step(str entity, str event, list[Variable] transitionParameters)
  | noStep()
  ; 

data Variable 
  = var(str name, Type tipe, RebelLit val)
  | uninitialized(str name, Type tipe)
  ;
   
data EntityInstance = instance(str entityType, list[RebelLit] id, list[Variable] vals);  
data State 
  = state(int nr, DateTime now, list[EntityInstance] instances, Step step)
  ;

list[Command] replaceStringsWithInts(list[Command] commands, StringConstantPool scp) = [replaceStringsWithInts(c, scp) | Command c <- commands];

Command replaceStringsWithInts(Command command, StringConstantPool scp) {
  return visit(command) {
    case \string() => integer()
    case strVal(str s) => intVal(scp.toInt(s))
  }
}

tuple[int, map[str,int]] fromStrToInt(str astr, map[str,int] constantPool) = <constantPool[astr], constantPool> when astr in constantPool;
default tuple[int, map[str, int]] fromStrToInt(str astr, map[str, int] constantPool) {
  int getNewInt(map[str, int] cp) = 0 when size(cp) == 0;
  default int getNewInt(map[str, int] cp) = (getOneFrom(onlyInts) | max(it, e) | int e <- onlyInts) + 1 when set[int] onlyInts := cp<1>;

  constantPool[astr] = getNewInt(constantPool);
  return <constantPool[astr], constantPool>;  
}

tuple[str, map[str,int]] fromIntToStr(int anint, map[str,int] constantPool) = <inverted[anint], constantPool> when map[int,str] inverted := invertUnique(constantPool), anint in inverted;
default tuple[str, map[str, int]] fromIntToStr(int anint, map[str, int] constantPool) {
  int strLength = 10;
  
  str randomStrGen(int lengthLimit) {
    list[str] abc = ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z"];
    return ("" | it + abc[arbInt(25) + 1] | int i <- [0..lengthLimit], str l := (i % 2 == 0 ? toUpperCase(abc[arbInt(25) + 1]) : abc[arbInt(25) + 1]));
  }
  
  str getNewStr(map[str, int] cp) =  randomStrGen(strLength) when size(cp) == 0;
  default str getNewStr(map[str, int] constantPool) {
    bool inserted = false;
    str newStr = "";
    
    while (!inserted) {
      newStr = randomStrGen(strLength);
    
      if (newStr notin constantPool) {
        constantPool[newStr] = anint;
        inserted = true;
      }
    }
    
    return newStr;
  }
  
  str newStr = getNewStr(constantPool);
  
  constantPool[newStr] = anint;
  return <newStr, constantPool>;
}

Graph[EventDef] getSyncedEvents(EventDef currentEvent, Built currentBuilt, set[Built] allBuilts) {
  Graph[EventDef] syncedEvents = {<currentEvent, currentEvent>};

  for (<loc ref, loc def> <- currentBuilt.refs.syncedEventRefs, 
       contains(currentEvent@\loc, ref),
       just(Built b) := findBuilt(def, allBuilts), 
       {loc eventDef} := b.refs.eventRefs[def], 
       just(EventDef syncedEvnt) := findNormalizedEventDef(eventDef, allBuilts)) {
    
    syncedEvents += <currentEvent, syncedEvnt>;
  }
  
  return syncedEvents;
}

Graph[FunctionDef] getFunctionCallOrder(FunctionDef currentFunc, Built currentBuild, set[Built] allBuilts) {
  rel[FunctionDef, FunctionDef] calledFunctions = {<currentFunc, currentFunc>};
  
  for (<loc ref, loc def> <- currentBuild.refs.functionRefs,
       contains(currentFunc@\loc, ref),
       just(FunctionDef calledFunc) := findFunctionDef(def, allBuilts)) {
    
    calledFunctions += <currentFunc, calledFunc>;
  }
  
  return calledFunctions;
}

EventDef addSyncedInstances(EventDef evnt, Built current, set[Built] otherSpecs) {
  SyncInstances merge((SyncInstances)`syncInstances { <Statement* stats> }`, Statement newStat) = 
    (SyncInstances)`syncInstances {
                   '  <Statement* stats>
                   '  <Statement newStat>
                   '}`; 
  
  if ([Expr key] := [[Expr]"_<field>" | (FieldDecl)`<VarName field>: <Type tipe> @key` <- current.normalizedMod.spec.fields.fields]) {
    set[Statement] result = findSyncedInstances(key, evnt, current, otherSpecs);
  
    return visit(evnt) {
      case orig:(EventDef)`<Annotations annos> event <FullyQualifiedVarName name><EventConfigBlock? configParams>(<{Parameter ","}* transitionParams>){<Preconditions? pre> <Postconditions? post> <SyncBlock? sync>}` =>
        (EventDef)`<Annotations annos> event <FullyQualifiedVarName name><EventConfigBlock? configParams>(<{Parameter ","}* transitionParams>){
          ' <Preconditions? pre>
          ' <Postconditions? post>
          ' <SyncBlock? sync>
          ' <SyncInstances si>
          '}`[@\loc=orig@\loc]
        when SyncInstances si := ((SyncInstances)`syncInstances {}` | merge(it, stat) | Statement stat <- result)
    }
  } else {
    throw "Currently no Specification with more (or less) than 1 key are supported";
  }
    
  
}

EventDef addToStateAndIdToSyncedEventCalls(EventDef evnt, Built parent, set[Built] allBuilds) {
  SyncExpr merge(orig:(SyncExpr)`<TypeName specName>[<Expr id>].<VarName event>(<{Expr ","}* params>)`, Expr newParam) =
    (SyncExpr)`<TypeName specName>[<Expr id>].<VarName event>(<{Expr ","}* params>, <Expr newParam>)`[@\loc=orig@\loc];
  
  Expr consToStateArg(str evnt, Module spc) {
    list[int] possibleStates = [];
    for (/LifeCycle lc := spc.spec.lifeCycle, StateFrom sf <- lc.from, (StateTo)`-\> <VarName to>: <StateVia via>` <- sf.destinations) {
      if (VarName e <- via.refs, "<e>" == evnt) {
        possibleStates += toInt("<sf.nr>");      
      }
    }
    
    return [Expr]"<intercalate(" || ",  dup(possibleStates))>";
  }
  
  Maybe[Module] findMod(loc eventRefLoc) {
    for (Built b <- allBuilds, contains(b.normalizedMod@\loc, eventRefLoc)) {
      return just(b.normalizedMod);
    }
    
    return nothing();
  } 
  
  SyncExpr addParams(orig:(SyncExpr)`<TypeName specName>[<Expr id>].<VarName event>(<{Expr ","}* params>)`) {
    SyncExpr result = orig;
    
    if ({loc eventRef} := parent.refs.syncedEventRefs[event@\loc], just(Module m) := findMod(eventRef)) {
      result = merge(orig, consToStateArg("<event>", m));
      result = merge(result, id);
    } 
    
    return result;
  }  
  
  default SyncExpr addParams(SyncExpr exp) { throw "Adding parameters to \'<exp>\' not yet implemented"; }
  
  EventDef addParamNames(EventDef orig) {
    if (/SyncBlock _ !:= orig.sync) {
      return orig;
    }
    
    return visit(orig) {
      case se:(SyncExpr)`<TypeName specName>[<Expr id>].<VarName event>(<{Expr ","}* params>)` => addParams(se)
    }
  }
  
  return addParamNames(evnt);
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

lrel[Built,EventDef] filterSynchronizedEventsOnly(Built origin, str eventName, set[Built] allSpecs, set[str] alreadyVisited) {
  if (eventName in alreadyVisited) {
    return [];
  }
  
  EventDef evnt = findEventDef(eventName, origin);
  evnt = addToStateAndIdToSyncedEventCalls(evnt, origin, allSpecs);
  
  lrel[Built, EventDef] result = [];
  
  for (<loc ref, loc def> <- origin.refs.syncedEventRefs, contains(evnt@\loc, ref)) {
    if (just(Built b) := findBuilt(def, allSpecs), {loc eventDef} := b.refs.eventRefs[def], just(EventDef syncedEvnt) := findNormalizedEventDef(eventDef, allSpecs)) {
      result += filterSynchronizedEventsOnly(b, "<syncedEvnt.name>", allSpecs, alreadyVisited + eventName);      
    }  
  }
  
  return result + <origin, evnt>;
}

list[str] getUnsatCoreStatements(SolverPID pid, EventDef raisedEvent) {
  str smtResponse = runSolver(pid, compile(getUnsatCore()), wait = 20);
  list[loc] unsatCoreLocs = [strToLoc(l) | str l <- parseSmtUnsatCore(smtResponse)];
  
  list[str] unsatCoreStats = ["<s>" | /Statement s := raisedEvent, s@\loc in unsatCoreLocs] +
                             ["<s>" | /SyncStatement s := raisedEvent, s@\loc in unsatCoreLocs];

  return unsatCoreStats;
} 

State getNextStateModel(SolverPID pid, State current, str nextStateLabel, map[str,str] specLookup, StringConstantPool scp, set[Built] allBuilts) {
  // TODO: filter out all unchanged, uninitialized fields
  
  EntityInstance getNextInstance(EntityInstance ei) {
    if (isInitializedEntity(pid, ei.entityType, ei.id, nextStateLabel, scp)) {
      return instance(ei.entityType, ei.id, 
        [getNewVarValue(pid, ei.entityType, ei.id, v, nextStateLabel, scp) | Variable v <- ei.vals]);
    } else {
      return ei; 
    }  
  }
  
  Step step = getStep(pid, nextStateLabel, scp, allBuilts);
  
  return state(current.nr + 1, current.now, [getNextInstance(ei) | EntityInstance ei <- current.instances],
               step);
}

str emptyLookup(int label) { throw "No string lookup function defined. Given label: <label>"; } 

Step getStep(SolverPID pid, str smtStateLabel, StringConstantPool scp, set[Built] allBuilts) {
  Command stepEntityCmd = getValue([functionCall(simple("step_entity"), [var(simple(smtStateLabel))])]);
  str entity = scp.toStr(toInt(parseSmtResponse(runSolver(pid, compile(stepEntityCmd), wait = 2), scp.toStr)));
  println(entity);
  
  Command stepEventCmd = getValue([functionCall(simple("step_transition"), [var(simple(smtStateLabel))])]);
  str event = scp.toStr(toInt(parseSmtResponse(runSolver(pid, compile(stepEventCmd), wait = 2), scp.toStr)));
  println(event);
  
  list[Variable] transitionValues = [];

  if (Built b <- allBuilts, "<b.normalizedMod.modDef.fqn>" == entity, EventDef evnt <- b.normalizedMod.spec.events.events, "<evnt.name>" == event) {
    for (Parameter p <- evnt.transitionParams) {
      Command transitionVal = getValue([functionCall(simple("eventParam_<entity>_<event>_<p.name>"), [var(simple(smtStateLabel))])]);
      str formattedRebelLit = parseSmtResponse(runSolver(pid, compile(transitionVal), wait = 5), scp.toStr);
      if (isStringType(p.tipe)) {
        formattedRebelLit = scp.toStr(toInt(formattedRebelLit));
      }
      
      RebelLit val = [lang::ExtendedSyntax::Literal]"<formattedRebelLit>";
      transitionValues += var("<p.name>", p.tipe, val);
    }
  }
  
  return step(entity, event, transitionValues);
}

bool isInitializedEntity(SolverPID pid, str entityType, list[RebelLit] id, str smtStateLabel, StringConstantPool scp) {
  Command isInitializedCmd = getValue([functionCall(simple("spec_<entityType>_initialized"), 
    [functionCall(simple("spec_<entityType>"), [var(simple(smtStateLabel))] + [translateLit(i) | lang::ExtendedSyntax::Literal i <- id])] +
    [translateLit(i) | lang::ExtendedSyntax::Literal i <- id])]);
  
  str smtOutput = runSolver(pid, compile(replaceStringsWithInts(isInitializedCmd, scp)), wait = 2);
  return fromString(parseSmtResponse(smtOutput, emptyLookup));
}

Variable getNewVarValue(SolverPID pid, str entityType, list[RebelLit] id, Variable current, str smtStateLabel, StringConstantPool scp) {
  Command newValCmd = getValue([functionCall(simple("field_<entityType>_<current.name>"), 
                        [functionCall(simple("spec_<entityType>"), [var(simple(smtStateLabel))] + [translateLit(i) | lang::ExtendedSyntax::Literal i <- id])])
                      ]);
           
  str smtOutput = runSolver(pid, compile(replaceStringsWithInts(newValCmd, scp)), wait = 10);

  str formattedRebelLit = parseSmtResponse(smtOutput, scp.toStr);
  if (isStringType(current.tipe)) {
    formattedRebelLit = scp.toStr(toInt(formattedRebelLit));
  }
  println(formattedRebelLit);
  RebelLit newVal = [lang::ExtendedSyntax::Literal]"<formattedRebelLit>";
  
  return var(current.name, current.tipe, newVal);
}

bool isStringType((Type)`String`) = true;
bool isStringType((Type)`Currency`) = true;
default bool isStringType(Type _) = false;

set[Built] loadAllSpecs(loc file, set[loc] visited) {
  set[Built] result = {};
  
  Built b = loadSpec(file);
  if (b.normalizedMod has spec) {
    result += b;    
  }
    
  for (<_, loc imported> <- b.refs.imports, imported.top notin visited) {
    set[Built] loaded = loadAllSpecs(imported.top, visited + file);
    visited += {l.normalizedMod@\loc.top | Built l <- loaded};
    result += loaded;
  } 
  
  return result;
}

Built loadSpec(loc file) {
  if (<_,just(Built b)> := load(file)) {
    return b;
  } else throw "Unable to load built file of <file>";
}

EventDef findEventDef(str eventName, Built b) = evnt when b.normalizedMod has spec, EventDef evnt <- b.normalizedMod.spec.events.events, "<evnt.name>" == eventName;
EventDef findEventDef(str eventName, Built b) { throw "Event with name \'<eventName>\' not found in specs"; }

list[Command] declareSmtSpecLookup(set[Module] mods, State st) {
  list[EntityInstance] getInstances(str entityType) = [ei | ei <- st.instances, ei.entityType == entityType];
   
  list[Command] smt = [];

  for (Module m <- mods, /normalized(_, _, TypeName name, _, Fields fields, _, _, _, _, _, LifeCycle lc) := m) {
    // lookup @key fields
    list[FieldDecl] keys = [f | /FieldDecl f := fields, /(Annotation)`@key` := f.meta];

    smt += declareFunction("spec_<m.modDef.fqn>", [custom("State")] + [translateSort(k.tipe) | k <- keys], custom("<m.modDef.fqn>"));  

    // declare an exist function to check whether keys are part of the predefined model universe
    smt += defineFunction("spec_<m.modDef.fqn>_exists", [sortedVar("<k.name>", translateSort(k.tipe)) | k <- keys], \boolean(),
      or([and([equal(var(simple("<keys[i].name>")), translateLit(ei.id[i])) | int i <- [0..size(keys)]]) | ei <- getInstances("<m.modDef.fqn>")])
    );

    // define the initialized function
    // 1. get all the states nr's which represent initialized states
    set[int] initializedStateNrs = {toInt("<sf.nr>") | /StateFrom sf := lc, /(LifeCycleModifier)`initial` !:= sf};
    smt += defineFunction("spec_<m.modDef.fqn>_initialized", 
      [sortedVar("entity", custom("<m.modDef.fqn>"))] + [sortedVar("<k.name>", translateSort(k.tipe)) | k <- keys], 
      \boolean(), 
      and([
        functionCall(simple("spec_<m.modDef.fqn>_exists"),[var(simple("<k.name>")) | k <- keys]),
        or([equal(functionCall(simple("field_<m.modDef.fqn>__state"), [var(simple("entity"))]), lit(intVal(nr))) | int nr <- initializedStateNrs])
      ]));
  }
  
  return smt;
}

list[Command] declareNow() = [declareFunction("now", [custom("State")], custom("DateTime"))];

list[Command] declareSmtTypes(set[Module] specs) {
  // first declare the build in Rebel types
  list[Command] smt = declareRebelTypes();
  
  // Add the state sort as undefined sort
  smt += declareSort("State");
  
  // Add 'specification' types as undefined sorts
  smt += toList({declareSort("<m.modDef.fqn>") | /Module m := specs, m has spec});
  
  return smt; 
}

list[Command] translateInvariants(set[Built] specs, Context ctx) =
  [defineFunction("invariant_<b.normalizedMod.modDef.fqn>.<inv.name>", 
    [sortedVar("state", custom("State"))] + [sortedVar("param__<f.name>", translateSort(f.tipe)) | FieldDecl f <- b.normalizedMod.spec.fields.fields, /(Annotation)`@key` := f.meta],
    boolean(),
    \and([translateStat(st, ctx) | Statement st <- inv.stats])) | Built b <- specs, InvariantDef inv <- b.normalizedMod.spec.invariants.defs];  

list[Command] translateFields(set[Module] specs) =
  [declareFunction("field_<m.modDef.fqn>_<f.name>", [custom("<m.modDef.fqn>")], translateSort(f.tipe)) | Module m <- specs, m has spec, FieldDecl f <- m.spec.fields.fields];

list[Command] translateAllTransitionParameters(set[Module] specs) =
  ([] | it + translateTransitionParameters("<m.modDef.fqn>", "<evnt.name>", {p | Parameter p <- evnt.transitionParams}) | Module m <- specs, m has spec, EventDef evnt <- m.spec.events.events);

list[Command] translateTransitionParameters(str fqnSpecName, str eventName, set[Parameter] transitionParams) =
  [declareFunction("eventParam_<fqnSpecName>_<eventName>_<p.name>", [custom("State")], translateSort(p.tipe)) | Parameter p <- transitionParams];  

list[Command] translateState(State state) {
  // Declare the current and next state variables
  list[Command] smt = [declareConst("current", custom("State")), declareConst("next", custom("State"))];
  
  // Assert the current value for 'now'
  smt += [\assert(equal(functionCall(simple("now"), [var(simple("next"))]), translateLit(state.now)))];
    
  // Assert all the current values of the entities
  smt += [\assert(equal(functionCall(simple("field_<ei.entityType>_<name>"), [functionCall(simple("spec_<ei.entityType>"), [var(simple("current")), *[translateLit(i) | lang::ExtendedSyntax::Literal i <- ei.id]])]), translateLit(val))) | EntityInstance ei <- state.instances, var(str name, Type tipe, RebelLit val) <- ei.vals];
  
  return smt; 
}

list[Command] translateEntityFrameFunctions(set[Built] allSpecs) {
  Formula frameField(Module m, FieldDecl field, list[FieldDecl] keyFields) 
    = equal(functionCall(simple("field_<m.modDef.fqn>_<field.name>"), [functionCall(simple("spec_<m.modDef.fqn>"), [var(simple("next"))] + [var(simple("_<f.name>")) | FieldDecl f <- keyFields])]),
            functionCall(simple("field_<m.modDef.fqn>_<field.name>"), [functionCall(simple("spec_<m.modDef.fqn>"), [var(simple("current"))] + [var(simple("_<f.name>")) | FieldDecl f <- keyFields])]));
  
  list[Command] result = [];
  
  for (Built b <- allSpecs, b.normalizedMod has spec, Module m := b.normalizedMod) {
    list[FieldDecl] keyFields = [f | f:(FieldDecl)`<VarName _> :<Type _> @key` <- m.spec.fields.fields];
    result += defineFunction("spec_<m.modDef.fqn>_frame", [sortedVar("current", custom("State")), sortedVar("next", custom("State"))] +
      [sortedVar("_<f.name>", translateSort(f.tipe)) | f <- keyFields], boolean(), 
      \and([frameField(m, f, keyFields) | FieldDecl f <- m.spec.fields.fields])); 
  }
  
  return result;
}

list[Command] translateTransitionParams(str entity, str transitionToFire, list[Variable] params) =
  [\assert(equal(functionCall(simple("eventParam_<entity>_<transitionToFire>_<p.name>"), [var(simple("next"))]), translateLit(p.val))) | Variable p <- params]; 

list[Command] translateFunctions(list[FunctionDef] functions, Context ctx) =
  [defineFunction("func_<f.name>", [sortedVar("param_<p.name>", translateSort(p.tipe)) | p <- f.params], translateSort(f.returnType), translateStat(f.statement, ctx)) | f <- functions];

list[Command] translateEventsToFunctions(lrel[Built, EventDef] evnts, Context ctx) {
  Command translate(Module m, EventDef evnt) =
    defineFunction("event_<m.modDef.fqn>_<evnt.name>", [sortedVar("current", custom("State")), sortedVar("next", custom("State"))] + 
      [sortedVar("param_<p.name>", translateSort(p.tipe)) | p <- evnt.transitionParams], \boolean(),
      \and([translateStat(s, ctx) | /Statement s := evnt] + 
           [translateSyncStat(s, ctx) | /SyncStatement s := evnt]));
  
  return [translate(b.normalizedMod, evnt) | Built b <- dup(evnts<0>), b.normalizedMod has spec, EventDef evnt <- evnts[b]];
}

list[Formula] translateFrameConditionsForUnchangedInstances(EventDef evnt, State current, Context ctx) {
  set[Expr] getKeysThatTakePartInTransition(str fqn) = {id | /(Statement)`<TypeName spc>[<Expr id>];` := evnt.syncInstances, ctx.specLookup["<spc>"] == fqn};

  set[EntityInstance] getInstancesOfType(str entityType) = {ei | EntityInstance ei <- current.instances, ei.entityType == entityType};

  RebelLit getId(EntityInstance ei) = id when [id] := ei.id;
  default RebelLit getId(EntityInstance ei) { throw "More then 1 field as id is not supported at this moment"; }
  
  list[Formula] result = [];
  set[str] uniqueEntities = {ei.entityType | EntityInstance ei <- current.instances};
  
  for (str fqn <- uniqueEntities) {
    set[Expr] keys = getKeysThatTakePartInTransition(fqn);
    set[EntityInstance] instances = getInstancesOfType(fqn);
    
    if (keys == {}) {
      // Entity type does not take part in transitions, all instances should be framed
      result += [functionCall(simple("spec_<fqn>_frame"), [var(simple("current")), var(simple("next")), translateLit(getId(i))]) | EntityInstance i <- instances];
    } else {
      // Check if the key is equal to one of the used keys and otherwise frame
      for (EntityInstance ei <- instances) {
        result += or([equal(translateLit(getId(ei)), translateExpr(key, ctx)) | Expr key <- keys] +
                      [functionCall(simple("spec_<fqn>_frame"), [var(simple("current")), var(simple("next")), translateLit(getId(ei))])]);
      }
    }
  }
  
  return result; 
}

list[Command] declareStepFunction() = [declareFunction("step_entity", [custom("State")], \string()), declareFunction("step_transition", [custom("State")], \string())]; 


Formula translateSyncStat(SyncStatement s, Context ctx) = translateSyncExpr(s.expr, ctx);

Formula translateSyncExpr((SyncExpr)`not <SyncExpr expr>`, Context ctx) = \not(translateSyncExpr(expr, ctx));
Formula translateSyncExpr((SyncExpr)`<TypeName spc>[<Expr id>].<VarName event>(<{Expr ","}* params>)`, Context ctx) 
  = functionCall(simple("event_<ctx.specLookup["<spc>"]>_<event>"), [var(simple("current")), var(simple("next"))] + [translateExpr(p, ctx) | p <- params]);

Formula translateStat((Statement)`(<Statement s>)`, Context ctx) = translateStat(s, ctx);
Formula translateStat((Statement)`<Annotations _> <Expr e>;`, Context ctx) = translateExpr(e, ctx);

Formula translateExpr((Expr)`new <Expr spc>[<Expr id>]`, Context ctx) = functionCall(simple("spec_<ctx.specLookup["<spc>"]>"), [var(simple("next")), translateExpr(id, ctx)]);
Formula translateExpr((Expr)`new <Expr spc>[<Expr id>].<VarName field>`, Context ctx) = functionCall(simple("field_<ctx.specLookup["<spc>"]>_<field>"), [functionCall(simple("spec_<ctx.specLookup["<spc>"]>"), [var(simple("next")), translateExpr(id, ctx)])]);

Formula translateExpr((Expr)`<Expr spc>[<Expr id>]`, Context ctx)  = functionCall(simple("spec_<ctx.specLookup["<spc>"]>"), [var(simple("current")), translateExpr(id, ctx)]);
Formula translateExpr((Expr)`<Expr spc>[<Expr id>].<VarName field>`, Context ctx) = functionCall(simple("field_<ctx.specLookup["<spc>"]>_<field>"), [functionCall(simple("spec_<ctx.specLookup["<spc>"]>"), [var(simple("current")), translateExpr(id, ctx)])]);

Formula translateExpr((Expr)`initialized <Expr spc>[<Expr id>]`, Context ctx) = functionCall(simple("spec_<ctx.specLookup["<spc>"]>_initialized"), [translateExpr((Expr)`<Expr spc>[<Expr id>]`, ctx), translateExpr((Expr)`<Expr id>`, ctx)]); 

Formula translateExpr((Expr)`<Expr lhs>.<VarName field>`, Context ctx) = functionCall(simple("<field>"), [translateExpr(lhs, ctx)]); 

Formula translateExpr((Expr)`(<Expr e>)`, Context ctx) = translateExpr(e, ctx);

Formula translateExpr((Expr)`<Literal l>`, Context ctx) = translateLit(l);

Formula translateExpr((Expr)`<Ref r>`, Context ctx) 
  = functionCall(simple("eventParam_<spec>_<event>_<r>"), [var(simple("next"))])
  when flattenedEvent(str spec, str event) := ctx;

Formula translateExpr((Expr)`<Ref r>`, Context ctx) 
  = var(simple("param_<r>"))
  when function() := ctx || eventAsFunction() := ctx;

Formula translateExpr((Expr)`<VarName function>(<{Expr ","}* params>)`, Context ctx) = functionCall(simple("func_<function>"), [translateExpr(p, ctx) | Expr p <- params]);

Formula translateFormula(Expr lhs, Expr rhs, (Type)`Money`, (Type)`Money`, Context ctx, Formula (Formula, Formula) createComp) 
  = createComp(functionCall(simple("amount"), [translateExpr(lhs, ctx)]), functionCall(simple("amount"), [translateExpr(rhs, ctx)])); 

default Formula translateFormula(Expr lhs, Expr rhs, Type _, Type _, Context ctx, Formula (Formula, Formula) createComp) 
  = createComp(translateExpr(lhs, ctx), translateExpr(rhs, ctx)); 

Formula translateExpr(Expr lhs, Expr rhs, (Type)`Money`, (Type)`Money`, Context ctx, Formula (Formula, Formula) createComp) 
  = functionCall(simple("consMoney"), [functionCall(simple("currency"), [translateExpr(lhs,ctx)]), 
      createComp(functionCall(simple("amount"), [translateExpr(lhs, ctx)]), functionCall(simple("amount"), [translateExpr(rhs, ctx)]))]); 

Formula translateExpr(Expr lhs, Expr rhs, (Type)`Money`, (Type)`Integer`, Context ctx, Formula (Formula, Formula) createComp) 
  = functionCall(simple("consMoney"), [functionCall(simple("currency"), [translateExpr(lhs,ctx)]), 
      createComp(functionCall(simple("amount"), [translateExpr(lhs, ctx)]), translateExpr(rhs, ctx))]); 

Formula translateExpr(Expr lhs, Expr rhs, (Type)`Money`, (Type)`Percentage`, Context ctx, Formula (Formula, Formula) createComp) 
  = functionCall(simple("consMoney"), [functionCall(simple("currency"), [translateExpr(lhs,ctx)]), 
      createComp(functionCall(simple("amount"), [translateExpr(lhs, ctx)]), translateExpr(rhs, ctx))]); 

default Formula translateExpr(Expr lhs, Expr rhs, Type _, Type _, Context ctx, Formula (Formula, Formula) createComp) 
  = createComp(translateExpr(lhs, ctx), translateExpr(rhs, ctx)); 

Formula translateExpr((Expr)`<Expr lhs> + <Expr rhs>`, Context ctx) 
  = translateExpr(lhs, rhs, ctx.types[lhs@\loc], ctx.types[rhs@\loc], ctx, Formula (Formula l, Formula r) { return add(l, [r]); });

Formula translateExpr((Expr)`<Expr lhs> - <Expr rhs>`, Context ctx)
  = translateExpr(lhs, rhs, ctx.types[lhs@\loc], ctx.types[rhs@\loc], ctx, Formula (Formula l, Formula r) { return sub(l, [r]); });

Formula translateExpr((Expr)`<Expr lhs> * <Expr rhs>`, Context ctx)
  = translateExpr(lhs, rhs, ctx.types[lhs@\loc], ctx.types[rhs@\loc], ctx, Formula (Formula l, Formula r) { return mul(l, [r]); });

Formula translateExpr((Expr)`<Expr lhs> / <Expr rhs>`, Context ctx)
  = translateExpr(lhs, rhs, ctx.types[lhs@\loc], ctx.types[rhs@\loc], ctx, Formula (Formula l, Formula r) { return div(l, [r]); });

Formula translateExpr((Expr)`<Expr lhs> % <Expr rhs>`, Context ctx)
  = translateExpr(lhs, rhs, ctx.types[lhs@\loc], ctx.types[rhs@\loc], ctx, Formula (Formula l, Formula r) { return \mod(l, r); });

Formula translateExpr((Expr)`-<Expr expr>`, Context ctx) = neg(translateExpr(expr, ctx));

Formula translateExpr((Expr)`not <Expr expr>`, Context ctx) = not(translateExpr(expr, ctx));

Formula translateExpr((Expr)`<Expr lhs> \< <Expr rhs>`, Context ctx) 
  = translateFormula(lhs, rhs, ctx.types[lhs@\loc], ctx.types[rhs@\loc], ctx, Formula (Formula l, Formula r) { return lt(l, r); });

Formula translateExpr((Expr)`<Expr lhs> \<= <Expr rhs>`, Context ctx) 
  = translateFormula(lhs, rhs, ctx.types[lhs@\loc], ctx.types[rhs@\loc], ctx, Formula (Formula l, Formula r) { return lte(l, r); });

Formula translateExpr((Expr)`<Expr lhs> \> <Expr rhs>`, Context ctx) 
  = translateFormula(lhs, rhs, ctx.types[lhs@\loc], ctx.types[rhs@\loc], ctx, Formula (Formula l, Formula r) { return gt(l, r); });

Formula translateExpr((Expr)`<Expr lhs> \>= <Expr rhs>`, Context ctx)
  = translateFormula(lhs, rhs, ctx.types[lhs@\loc], ctx.types[rhs@\loc], ctx, Formula (Formula l, Formula r) { return gte(l, r); });

Formula translateExpr((Expr)`<Expr lhs> == <Expr rhs>`, Context ctx) = equal(translateExpr(lhs, ctx), translateExpr(rhs, ctx));
Formula translateExpr((Expr)`<Expr lhs> != <Expr rhs>`, Context ctx) = \not(equal(translateExpr(lhs, ctx), translateExpr(rhs, ctx)));
Formula translateExpr((Expr)`<Expr lhs> && <Expr rhs>`, Context ctx) = and([translateExpr(lhs, ctx), translateExpr(rhs, ctx)]);
Formula translateExpr((Expr)`<Expr lhs> || <Expr rhs>`, Context ctx) = or([translateExpr(lhs, ctx), translateExpr(rhs, ctx)]);

Formula translateExpr((Expr)`inUni (<TypeName spc>[<Expr id>])`, Context ctx) = functionCall(simple("spec_<ctx.specLookup["<spc>"]>_exists"), [translateExpr(id,ctx)]);

  //| "{" Expr lower ".." Expr upper"}"   
  //| "(" {MapElement ","}* mapElems ")"
  //| staticSet: "{" {Expr ","}* setElems "}"
  //| "{" Expr elem "|" Expr loopVar "\<-" Expr set "}"
  //| "{" Expr init "|" Statement reducer "|" Expr loopVar "\<-" Expr set "}" 
  //| isMember: Expr lhs "in" Expr rhs
  //> right ( Expr cond "?" Expr whenTrue ":" Expr whenFalse
  //  | Expr cond "-\>" Expr implication
  //| "finalized" Expr
  //| Expr lhs "instate" Expr rhs
  
default Formula translateExpr(Expr exp, Context ctx) { throw "Translation for expr \'<exp>\' not yet implemented"; }
  
Sort translateSort((Type)`Currency`) = custom("Currency");
Sort translateSort((Type)`Date`) = custom("Date");
Sort translateSort((Type)`Time`) = custom("Time");
Sort translateSort((Type)`DateTime`) = custom("DateTime");
Sort translateSort((Type)`IBAN`) = custom("IBAN");
Sort translateSort((Type)`Money`) = custom("Money");
Sort translateSort((Type)`Integer`) = \integer();
Sort translateSort((Type)`Frequency`) = custom("Frequency");
Sort translateSort((Type)`Percentage`) = custom("Percentage");
Sort translateSort((Type)`String`) = \string();


default Sort translateSort(Type t) { throw "Sort conversion for <t> not yet implemented"; }

//Formula translateLit(value v) = translateLit(l) when RebelLit l := v;

Formula translateLit((Literal)`<Int i>`) = translateLit(i);
Formula translateLit((Literal)`<Percentage p>`) = translateLit(p);

Formula translateLit((Literal)`<IBAN i>`) = translateLit(i);

Formula translateLit((Literal)`<Money m>`) = translateLit(m);//functionCall(simple("amount"), [translateLit(m)]);

Formula translateLit((Literal)`<DateTime tm>`) = translateLit(tm);
Formula translateLit((Literal)`<Date d>`) = translateLit(d);
Formula translateLit((Literal)`<Time t>`) = translateLit(t);
Formula translateLit((Literal)`<Currency c>`) = translateLit(c);

Formula translateLit(Money m) = lit(adt("consMoney", [lit(strVal("<m.cur>")), translateLit(m.amount)]));
Formula translateLit(MoneyAmount ma) = lit(intVal(toInt("<ma.whole>") * 100 + toInt("<ma.decimals>")));

Formula translateLit((DateTime)`now`) = functionCall(simple("now"), [var(simple("next"))]);
Formula translateLit(DateTime dt) = lit(adt("consDateTime", [translateLit(dt.date), translateLit(dt.time)]));

Formula translateLit(Date d) = lit(adt("consDate", [translateLit(d.day), translateLit(d.month),translateLit(year)])) when d has year, /Int year := d.year;
Formula translateLit(Date d) = lit(adt("consDate", [translateLit(d.day), translateLit(d.month), translateLit(0)])) when !(d has year); 
Formula translateLit(Time t) = lit(adt("consTime", [translateLit(toInt("<t.hour>")), translateLit(toInt("<t.minutes>")), translateLit(toInt("<sec>"))])) when t has seconds, /Int sec := t.seconds; 
Formula translateLit(Time t) = lit(adt("consTime", [translateLit(toInt("<t.hour>")), translateLit(toInt("<t.minutes>")), translateLit(0)])) when !t has seconds; 
Formula translateLit(IBAN i) = lit(adt("consIBAN", [translateLit("<i.countryCode>"), translateLit(toInt("<i.checksum>")), translateLit("<i.accountNumber>")])); 

Formula translateLit(Currency c) = lit(strVal("<c>"));

Formula translateLit((Month)`Jan`) = lit(intVal(1)); 
Formula translateLit((Month)`Feb`) = lit(intVal(2));
Formula translateLit((Month)`Mar`) = lit(intVal(3));
Formula translateLit((Month)`Apr`) = lit(intVal(4));
Formula translateLit((Month)`May`) = lit(intVal(5));
Formula translateLit((Month)`Jun`) = lit(intVal(6)); 
Formula translateLit((Month)`Jul`) = lit(intVal(7));
Formula translateLit((Month)`Aug`) = lit(intVal(8));
Formula translateLit((Month)`Sep`) = lit(intVal(9));
Formula translateLit((Month)`Oct`) = lit(intVal(10));
Formula translateLit((Month)`Nov`) = lit(intVal(11));
Formula translateLit((Month)`Dec`) = lit(intVal(12));

Formula translateLit(Int i) = lit(intVal(toInt("<i>")));
Formula translateLit(int i) = lit(intVal(i));

Formula translateLit(Percentage p) = lit(intVal(toInt("<p.per>")));

Formula translateLit(String s) = lit(strVal("<s>"));
Formula translateLit(str s) = lit(strVal(s));

default Literal translateLit(value l) { throw "translateLit(..) not implemented for <l>"; }

list[Command] declareRebelTypes() {   
  set[tuple[str,Sort]] rebelTypes = {<"Currency", \string()>,
                                     <"Frequency", \integer()>,
                                     <"Percentage", \integer()>,
                                     <"Period", \integer()>,
                                     <"Term", \integer()>};
                             
  return [defineSort(name, [], sort) | <str name, Sort sort> <- rebelTypes] +
         [declareDataTypes([], [dataTypeDef("IBAN", [combinedCons("consIBAN", [sortedVar("countryCode", string()), sortedVar("checksum",\integer()), sortedVar("accountNumber", string())])])]),
          declareDataTypes([], [dataTypeDef("Money", [combinedCons("consMoney", [sortedVar("currency", custom("Currency")), sortedVar("amount", \integer())])])]),
          declareDataTypes([], [dataTypeDef("Date", [
            combinedCons("consDate", [sortedVar("date", \integer()), sortedVar("month", \integer()), sortedVar("year", \integer())]), 
            cons("undefDate")])]),
          declareDataTypes([], [dataTypeDef("Time", [

            combinedCons("consTime", [sortedVar("hour", \integer()), sortedVar("minutes", \integer()), sortedVar("seconds", \integer())]), 
            cons("undefTime")])]),
          declareDataTypes([], [dataTypeDef("DateTime", [combinedCons("consDateTime", [sortedVar("date", custom("Date")), sortedVar("time", custom("Time"))]), cons("undefDateTime")])])                                   
          ];                                  
}
