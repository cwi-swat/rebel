module lang::Builder

import Message;
import util::Maybe;
import util::FileSystem;

import lang::Importer;
import lang::Flattener;
import lang::Resolver;
import lang::Checker;
import lang::Normalizer;
import lang::Parser;
import lang::ExtendedSyntax;

import IO;
import ValueIO;
import List;
import String;
import ParseTree;
import Set;

alias Log = void(str);

void noLog(str x) {}

alias Phase1Result = tuple[set[Message] msgs, Module phase1Module, set[Module] imports, Refs refs];

//data Built 
//  = buildSpec(Module inlinedMod, Module normalizedMod, Refs refs)
//  | buildLib(Module normalizedMod, Refs refs)
//  ;

alias Built = tuple[Module inlinedMod, Module normalizedMod, Refs refs];

tuple[set[Message], Built] load(loc modLoc, 
  loc outputDir, 
  Maybe[Module] modulPt = nothing(), 
  bool clean = false, 
  Log log = noLog) {
  
  Module orig = (just(Module m) := modulPt) ? m : parseModule(modLoc);
  
  <msgs, allNormalizedBuilds> = loadAll(modLoc, outputDir, modulPt = modulPt, clean = clean, log = log);
  if (Built m <- allNormalizedBuilds, m.normalizedMod.modDef.fqn == orig.modDef.fqn) {
    return <msgs, m>;
  } else {
    throw "Unable to locate normalized module in result";
  }   
}

tuple[set[Message], set[Built]] loadAll(loc modLoc, 
  loc outputDir, 
  Maybe[Module] modulPt = nothing(), 
  bool clean = false, 
  Log log = noLog) {
  
  int indent = 0;
  void ilog(str x) {
    msg = ( "" | it + "  " | _ <- [0..indent] ) + x;
    log(msg);
  }
  
  map[FullyQualifiedName, tuple[bool, Built]] done = ();
  
  tuple[set[Message], Built, set[Module]] build(Module modul) {
    ImporterResult importResult = loadImports(modul); //, {"<i.modDef.fqn>" | i <- imported});
    //imported += importResult<1>;    
    Refs refs = resolve({modul} + importResult<1>);
    
    if (modul has spec) {
      FlattenerResult flattenResult = flatten(modul, importResult<1>);
      NormalizeResult inliningResult =  inline(flattenResult.flattenedModule, importResult<1>, refs);
      NormalizeResult desugaringResult =  desugar(inliningResult<1>, importResult<1>, refs);
      
      return <importResult<0> + flattenResult<0> + inliningResult<0> + desugaringResult<0>, <inliningResult<1>, desugaringResult<1>, refs>, importResult<1>>;
    } else {
      return <importResult<0>, <modul, modul, refs>, importResult<1>>;
    }
  } 
    
  //void saveToOutput(b:buildSpec(Module inlinedMod, Module normalizedMod, Refs refs)) {
  //  writeBinaryValueFile(builtFile(inlinedMod), b);
  //  writeFile(normalizedFile(normalizedMod), normalizedMod);
  //}  
  //  
  //void saveToOutput(b:buildLib(Module normalizedMod, Refs refs)) {
  //  writeBinaryValueFile(builtFile(normalizedMod), b);
  //}

  void saveToOutput(Built b) {
    writeBinaryValueFile(builtFile(b.normalizedMod), b);
    writeFile(normalizedFile(b.normalizedMod), b.normalizedMod);
  }
  
  Built loadFromOutput(Module orig) = readBinaryValueFile(#Built, builtFile(orig));
  
  @memo
  loc normalizedFile(Module src) = toOutputPath(outputDir, src)[extension = "nebl"];
  @memo
  loc builtFile(Module src) = toOutputPath(outputDir, src)[extension = "bebl"];
      
  loc toOutputPath(loc base, Module m) = (base + "<("" | "<it><p>/" | /VarName p := m.modDef.fqn)><m.modDef.fqn.modName>")[extension="ebl"];  
  
  @memo
  Module cachedParse(loc src) = parseModule(src);
  
  bool changedOnDisk(Module m) = m != cachedParse(modLoc);
  
  bool needsBuild(Module origMod) {
    bool buildNecessary() = 
      !exists(builtFile(origMod)) 
      || (lastModified(builtFile(origMod)) <= lastModified(origMod@\loc.top))
      || clean
      || (just(origMod) := modulPt && changedOnDisk(origMod))
      ;
 
    if (origMod.modDef.fqn in done) {
      return false;
    } else if (!buildNecessary()) {
      Built buildModule = loadFromOutput(origMod);
      done += (origMod.modDef.fqn : <false, buildModule>); 

      return false;
    } else {
      return true;
    }
  }
  
  set[Message] msgs = {};
  
  void buildRecursive(Module orig) {
    ilog("Preparing <orig.modDef.fqn> for build");
    indent += 1;
    
    if (needsBuild(orig) && orig.modDef.fqn notin done) {
      ilog("<orig.modDef.fqn.modName> needs fresh build");
      
      tuple[set[Message], Built, set[Module]] result = build(orig); 
      
      done += (result<1>.normalizedMod.modDef.fqn : <true, result<1>>);
      msgs += result<0>;

      for (Module imp <- result<2>) {
        buildRecursive(imp);
      }
    } else {
      ilog("<orig.modDef.fqn.modName> already build");
    }
    
    indent -= 1;
  }
  
  Module orig = (just(Module m) := modulPt) ? m : cachedParse(modLoc);
  buildRecursive(orig);
  
  for (<bool needsSave, Built built> <- done<1>) {
    if (needsSave) {
      saveToOutput(built);
    }
  }
  
  return <msgs, {b | Built b <- done<1><1>}>;
}