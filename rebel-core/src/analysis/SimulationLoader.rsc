module analysis::SimulationLoader

import lang::Builder;
import lang::ExtendedSyntax;
import lang::Resolver;

import analysis::Simulator;

import util::Maybe;
import ParseTree;
import Set;
import String;
import DateTime;

alias SimConfig = set[tuple[loc spec, str fqnOfSpec, int nrOfInstances]]; 

SimConfig getInitialConfiguration(loc spec) {
  set[Built] allSpecs = loadAllSpecs(spec, {});
  int nrOfInstances = size(allSpecs) == 1 ? 1 : 2;
  
  return {<s.normalizedMod@\loc.top, "<s.normalizedMod.modDef.fqn>", nrOfInstances> | Built s <- allSpecs};
} 

State constructInitialState(SimConfig cfg) {
  int accountIter = 0;
  int intIter = 0;

  Literal getIdProposal((Type)`IBAN`) { accountIter += 1; return [Literal]"NL01INGB000000<accountIter>"; }
  Literal getIdProposal((Type)`Integer`) {intIter += 1; return [Literal]"<intIter>"; }
  default Literal getIdProposal(Type t) { throw "Id proposal for type \'<t>\' not yet implemented"; }
  
  map[str, Type] getIdFields(Module spc) = ("<field>":tipe | (FieldDecl)`<VarName field> : <Type tipe> @key` <- spc.spec.fields.fields);
  
  int findInitialStateNr(Module spc) {
    if (StateFrom sf <- spc.spec.lifeCycle.from, sf has \mod, /(LifeCycleModifier)`initial` := sf.\mod) {
      return toInt("<sf.nr>");
    }
   
    throw "Unable to locate initial state of spec \'<spc.modDef.fqn>\'"; 
  }
  
  return state(0, 
              [DateTime]"26 Sep 2016, 14:32:00", // TODO: Construct now base on actual time 
              [instance("<spc.modDef.fqn>", 
                        [getIdProposal(idFields[id]) | map[str,Type] idFields := getIdFields(spc), str id <- idFields],
                        [var("_state", [Type]"Int", [Int]"<findInitialStateNr(spc)>")])
              | <loc specLoc, _, int nrOfInstances> <- cfg, <_, just(Built b)> := load(specLoc), Module spc := b.normalizedMod] 
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


