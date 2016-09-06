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
import lang::TypeChecker;

import IO;
import ValueIO;
import List;
import String;
import ParseTree;
import Set;

alias Log = void(str);

void noLog(str x) {}

//data Built 
//  = buildSpec(Module inlinedMod, Module normalizedMod, Refs refs)
//  | buildLib(Module normalizedMod, Refs refs)
//  ;

alias Built = tuple[Module inlinedMod, Module normalizedMod, Refs refs, map[loc, Type] resolvedTypes];
alias UsedBy = set[loc];

private str buildDir = "bin";

loc getOutputLoc(loc srcFile)  = |<srcFile.scheme>://<srcFile.authority>/<buildDir>/rebel|;

tuple[set[Message], Built] load(loc modLoc, 
  loc outputDir = getOutputLoc(modLoc), 
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
  map[loc, Module] parsed = ();
  
  tuple[set[Message], Built, set[Module]] build(Module modul) {
    ImporterResult importResult = loadImports(modul, cachedParse);
    Refs refs = resolve({modul} + importResult<1>);
    
    if (modul has spec) {
      FlattenerResult flattenResult = flatten(modul, importResult<1>);
      NormalizeResult inliningResult =  inline(flattenResult.flattenedModule, importResult<1>, refs);
      NormalizeResult desugaringResult =  desugar(inliningResult<1>, importResult<1>, refs);
      
      // Check types
      TypeCheckerResult inlineTypeCheckerResult = checkTypes(inliningResult<1>, importResult<1>);
      TypeCheckerResult desugaredTypeCheckerResult = checkTypes(inliningResult<1>, importResult<1>);
      
      return <importResult<0> + flattenResult<0> + inliningResult<0> + desugaringResult<0> + inlineTypeCheckerResult<0> + desugaredTypeCheckerResult<0>, <inliningResult<1>, desugaringResult<1>, refs, inlineTypeCheckerResult<1> + desugaredTypeCheckerResult<1>>, importResult<1>>;
    } else {
      return <importResult<0>, <modul, modul, refs, ()>, importResult<1>>;
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
  @memo
  loc usedByFile(Module src) = toOutputPath(outputDir, src)[extension = "ub"];
      
  @memo      
  loc toOutputPath(loc base, Module m) = (base + "<("" | "<it><p>/" | /VarName p := m.modDef.fqn)><m.modDef.fqn.modName>")[extension="ebl"];  
  
  set[loc] loadUsedBy(Module src) = (exists(usedByFile(src))) ? readTextValueFile(#UsedBy, usedByFile(src)) : {};
      
  set[Module] loadUsedByModules(Module src) { 
    set[loc] usedBy = loadUsedBy(src);
      
    return {cachedParse(u.top) | u <- usedBy};      
  }
  
  void addToUsedBy(Module src, loc dep) {
    set[loc] usedBy = loadUsedBy(src);
    usedBy += dep;
    writeTextValueFile(usedByFile(src), usedBy);
  }
  
  void removeFromUsedBy(Module src, loc dep) {
    set[loc] usedBy = loadUsedBy(src);
    usedBy -= dep;
    writeTextValueFile(usedByFile(src), usedBy);
  }
  
  Module cachedParse(loc src) { 
    if (src in parsed) {
      return parsed[src];
    } else {
      Module m = parseModule(src);
      parsed += (src : m);
      return m;
    }
  }
  
  bool changedOnDisk(Module m) = <m> != <parseModule(modLoc)>;
  
  bool needsBuild(Module origMod) {
    bool buildNecessary() = 
      !exists(builtFile(origMod)) 
      || (lastModified(builtFile(origMod)) <= lastModified(origMod@\loc.top))
      || clean
      || (just(origMod) := modulPt && changedOnDisk(origMod))
      ;
 
    if (origMod.modDef.fqn in done) {
      return false;
    } 
    else if (!buildNecessary()) {
      Built buildModule = loadFromOutput(origMod);
      done += (origMod.modDef.fqn : <false, buildModule>); 

      return false;
    } else {
      return true;
    }
  }
  
  set[Message] msgs = {};
  
  void buildRecursive(Module orig) {
    indent += 1;
    ilog("Preparing <orig.modDef.fqn> for build");
    
    if (needsBuild(orig) && orig.modDef.fqn notin done) {
      ilog("<orig.modDef.fqn.modName> needs fresh build");
      
      tuple[set[Message], Built, set[Module]] result = build(orig); 
      
      done += (result<1>.normalizedMod.modDef.fqn : <true, result<1>>);
      msgs += result<0>;
      
      for (Module imp <- result<2>, imp != orig) {
        buildRecursive(imp);
      }
      
      // Check used by dependencies as well
      for (Module dependency <- loadUsedByModules(orig)) {
        if ("<orig.modDef.fqn>" notin {"<imp.fqn>" | Import imp <- dependency.imports}) {
          ilog("Dependend module <dependency.modDef.fqn.modName> is not depending on this module any more");
          removeFromUsedBy(orig, dependency@\loc.top);
        }
      } 
      
      // Check the imports and add this module as dependency if needed
      for (Module imp <- result<2>, imp != orig) {
        addToUsedBy(imp, orig@\loc.top);
      }      

      ilog("Done building <orig.modDef.fqn.modName>");
    } else {
      ilog("<orig.modDef.fqn.modName> already build");
    }
    
    indent -= 1;
  }
  
  Module orig = (just(Module m) := modulPt) ? m : cachedParse(modLoc);
  parsed += (orig@\loc.top : orig);

  buildRecursive(orig);
  
  for (<bool needsSave, Built built> <- done<1>) {
    if (needsSave) {
      saveToOutput(built);
    }
  }
  
  ilog("Building done!");
  
  return <msgs, {b | Built b <- done<1><1>}>;
}

