module analysis::SimulationHelper

import lang::Builder;
import lang::ExtendedSyntax;
import lang::Resolver;

import analysis::Simulator;
import analysis::CommonAnalysisFunctions;

import util::Maybe;
import ParseTree;
import Set; 
import String;
import DateTime;
import IO;

alias SimConfig = set[tuple[loc spec, str fqnOfSpec, int nrOfInstances]]; 

SimConfig getInitialConfiguration(loc spec) {
  set[Built] allSpecs = loadAllSpecs(spec, {});
  int nrOfInstances = size(allSpecs) == 1 ? 1 : 2;
  
  return {<s.normalizedMod@\loc.top, "<s.normalizedMod.modDef.fqn>", nrOfInstances> | Built s <- allSpecs};
} 

State constructInitialState(SimConfig cfg) {
  int accountIter = 0;
  int intIter = 0;

  Expr getIdProposal((Type)`IBAN`) { accountIter += 1; return [Expr]"NL01INGB000000<accountIter>"; }
  Expr getIdProposal((Type)`Integer`) {intIter += 1; return [Expr]"<intIter>"; }
  default Literal getIdProposal(Type t) { throw "Id proposal for type \'<t>\' not yet implemented"; }
  
  set[Variable] getIdFields(Module spc) = {var("<field>",tipe, getIdProposal(tipe)) | (FieldDecl)`<VarName field> : <Type tipe> @key` <- spc.spec.fields.fields};
  set[Variable] getNonIdFields(Module spc) = {uninitialized("<field>",tipe) | (FieldDecl)`<VarName field> : <Type tipe>` <- spc.spec.fields.fields, !startsWith("<field>", "_")};
  
  int findInitialStateNr(Module spc) {
    if (StateFrom sf <- spc.spec.lifeCycle.from, sf has \mod, /(LifeCycleModifier)`initial` := sf.\mod) {
      return toInt("<sf.nr>");
    }
   
    throw "Unable to locate initial state of spec \'<spc.modDef.fqn>\'"; 
  }
  
  list[EntityInstance] instances = [];
  for (<loc specLoc, _, int nrOfInstances> <- cfg, <_, just(Built b)> := load(specLoc), Module spc := b.normalizedMod, int i <- [0 .. nrOfInstances]) {
    idFields = getIdFields(spc);
    instances += instance("<spc.modDef.fqn>", 
                   [v.val | v <- idFields], // id
                   [var("_state", [Type]"Int", [Expr]"<findInitialStateNr(spc)>")] + // current initial state 
                   [uninitialized("_step", [Type]"Int")] +
                   [v | v <- idFields] + // identity fields with value
                   [v | v <- getNonIdFields(spc)]); // other uninitialized fields
  } 
  
  return state(0, 
              [DateTime]"26 Sep 2016, 14:32", // TODO: Construct now base on actual time 
              instances,
              noStep()
         );    
}

set[Built] loadAllSpecs(loc file, set[loc] visited) {
  set[Built] result = {};
  
  if (<_,just(Built b)> := load(file)) {
    if (b.normalizedMod has spec) {
      result += b;    
    }
    
    for (<_, loc imported> <- b.refs.imports, imported.top notin visited) {
      set[Built] loaded = loadAllSpecs(imported.top, visited + file);
      visited += {l.normalizedMod@\loc.top | Built l <- loaded};
      result += loaded;
    } 
  }
  
  return result;
} 

data Var = var(str fieldName, str val);

State buildState(str now, list[EntityInstance] instances) =
  state(1, [DateTime]"<now>", instances, noStep());

list[Variable] buildTransitionParams(str entity, str transitionToFire, str toState, Var id, list[Var] params, set[Built] allSpecs) {
  loc findSpec() = b.normalizedMod.modDef@\loc.top
    when Built b <- allSpecs,
         b has normalizedMod,
         "<b.normalizedMod.modDef.fqn>" == entity;

  default loc findSpec() { throw "Unable to locate the specification \'<entity>\'. Is it correctly spelled?"; }

  list[Param] paramsInTransition = getTransitionParams(findSpec(), transitionToFire);
 
  list[Variable] result = [];

  if (/param("_<id.fieldName>", _) !:= paramsInTransition, /param(str name, _) := paramsInTransition, startsWith(name, "_"), name != "_toState") {
    throw "The provided id field \'<id.fieldName>\' does not match the id field of the entity. The id field should be \'<substring(name,1)>\'";
  } 

  for (param(str name, Type tipe) <- paramsInTransition) {
    if (v:var(name, str val) <- params) {
      result += buildTransitionParam(v, "<tipe>");
    } else if (name == "_<id.fieldName>") {
      result += buildTransitionParam(var("<name>", id.val), "<tipe>");
    }
    else if (name != "_toState") {
      throw "Used parameter \'<name>\' of type \'<tipe>\' not in provided transition parameter list";
    }
  }
  
  result += [var("_toState", [Type]"Int", findStateLabel(allSpecs, entity, toState))];  
  
  return result;
}

Variable buildTransitionParam(Var param, str tipe) = var(param.fieldName, [Type]"<tipe>", [Expr]"<param.val>"); 

Expr findStateLabel(set[Built] allSpecs, str entity, str state) = [Expr]"<from.nr>"
  when  Built b <- allSpecs, 
        b has normalizedMod, 
        entity == "<b.normalizedMod.modDef.fqn>",
        StateFrom from <- b.normalizedMod.spec.lifeCycle.from,
        "<from.from>" == state;
default Expr findStateLabel(set[Built] allSpecs, str entity, str state) { throw "Unable to find state \'<state>\' in entity \'<entity>\'"; }

EntityInstance buildInstance(str entity, Var id, str state, list[Var] fieldsAndVals, set[Built] allSpecs) {  
  set[str] fieldsWithValues = {v.fieldName | Var v <- fieldsAndVals};
  
  Variable keyField() = var(id.fieldName, [Type]"<f.tipe>", [Expr]"<id.val>")
    when Built b <- allSpecs, b has normalizedMod, entity == "<b.normalizedMod.modDef.fqn>", FieldDecl f <- b.normalizedMod.spec.fields.fields, "<f.name>" == id.fieldName; 

  default Variable keyField() { throw "Used id field name \'<id.fieldName>\' does not correspond with the annotated key field for the \'<entity>\' specification"; }

  
  list[Variable] uninitializedFields = [uninitialized("<f.name>", [Type]"<f.tipe>") | 
    Built b <- allSpecs, b has normalizedMod, entity == "<b.normalizedMod.modDef.fqn>", FieldDecl f <- b.normalizedMod.spec.fields.fields, "<f.name>" notin fieldsWithValues, "<f.name>" != id.fieldName, "<f.name>" != "_state"];

  list[Variable] initializedFields = [var("<f.name>", [Type]"<f.tipe>", [Expr]"<val>") |
    Built b <- allSpecs, b has normalizedMod, entity == "<b.normalizedMod.modDef.fqn>", FieldDecl f <- b.normalizedMod.spec.fields.fields, "<f.name>" in fieldsWithValues, var("<f.name>", str val) <- fieldsAndVals];
  
  if (var(str name, _) <- fieldsAndVals, /var(name, _, _) !:= uninitializedFields + initializedFields) {
    throw "Provided field \'<name>\' is not a known field of the entity \'<entity>\'. Could it be a typo?";
  }
  
  return instance(entity, [[lang::ExtendedSyntax::Expr]"<id.val>"], 
    [keyField()] + [var("_state", [Type]"Int", findStateLabel(allSpecs, entity, state))] + initializedFields + uninitializedFields);
}

str findState(set[Built] allSpecs, str entity, str stateLabel) = "<from.from>"
  when  Built b <- allSpecs, 
        b has normalizedMod, 
        entity == "<b.normalizedMod.modDef.fqn>",
        StateFrom from <- b.normalizedMod.spec.lifeCycle.from,
        "<from.nr>" == stateLabel;
default str findState(set[Built] allSpecs, str entity, str stateLabel) = "?";

str findStep(set[Built] allSpecs, str entity, str stepLabel) = "<evnt.name>"
  when  Built b <- allSpecs, 
        b has normalizedMod, 
        entity == "<b.normalizedMod.modDef.fqn>",
        EventDef evnt <- b.normalizedMod.spec.events.events,
        /(Statement)`new <Expr spc>[<Expr id>]._step == <Int i>;` := evnt.post,
        stepLabel == "<i>";
default str findStep(set[Built] allSpecs, str entity, str stepLabel) = "?";


void printState(State st, set[Built] allSpecs) {
  str printStateLabel(EntityInstance ei) = printStateVar(v, ei.entityType)
    when v:var("_state", Type _, Expr _) <- ei.vals;
  default str printStateLabel(EntityInstance ei) = "?";
    
  str printStepLabel(EntityInstance ei) = printStateVar(v, ei.entityType)
    when v:var("_step", Type _, Expr _) <- ei.vals;
  default str printStepLabel(EntityInstance ei) = "?";
     
  str printStateVar(var("_state", Type t, Expr val), str entity) = "State = <findState(allSpecs, entity, "<val>")>";  
  str printStateVar(var("_step", Type t, Expr val), str entity) = "Last event triggered = <findStep(allSpecs, entity, "<val>")>";
  default str printStateVar(var(str name, Type t, Expr val), str entity) = "var <name> (type: <t>) = <val>"; 
  str printStateVar(uninitialized(str name, Type t), str entity) = "var <name> (type: <t>) (uninitialized)";
  
  str printStepVar(var("_toState", Type t, Expr val), str entity) = "Transition to state = <findState(allSpecs, entity, "<val>")>"; 
  default str printStepVar(var(str idField, Type t, Expr val), str entity) = "Identified by <fieldName> = <val>" when startsWith(idField, "_"), str fieldName := substring(idField, 1); 
  default str printStepVar(var(str name, Type t, Expr val), str entity) = "var <name> (type: <t>) = <val>" when !startsWith(name, "_");
  
  println("<st.nr>:
          '  now = <st.now>");

  if (step(str entity, str event, list[Variable] transitionParameters) := st.step) {
    println("  step: <entity>.<event> <for (v <- transitionParameters) {>
            '    <printStepVar(v, entity)> <}>
            '");
  }
  
  println("<for (i <- st.instances) {>
          '  instance: <i.entityType>, key = <intercalate(",", i.id)> 
          '    <printStateLabel(i)>
          '    <printStepLabel(i)><for (v <- i.vals, v.name != "_state" && v.name != "_step") {>
          '    <printStateVar(v, i.entityType)> <}>  
          '<}>
          '");
}


