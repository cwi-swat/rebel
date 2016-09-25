module analysis::SimulationLoader

import lang::Builder;
import lang::ExtendedSyntax;
import lang::Resolver;

import analysis::Simulator;

import util::Maybe;
import ParseTree;

alias SimConfig = map[str fqnOfSpec, int nrOfInstances]; 

SimConfig getInitialConfiguration(loc spec) =
  ("<s.normalizedMod.modDef.fqn>": 2 | Built s <- loadAllSpecs(spec, {})); 

State constructInitialState(SimConfig cfg) {
  int accountIter = 0;
  int intIter = 0;

  Literal getIdProposal((Type)`IBAN`) { accountIter += 1; return [Literal]"NL01INGB000000<accountIter>"; }
  Literal getIdProposal((Type)`Integer`) {intIter += 1; return [Literal]"<intIter>"; }
  
  int findInitialStateNr(Module spc) {}
    
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


