module testlang::Loader

import testlang::Syntax;
import testlang::Parser;
import testlang::Resolver;
import testlang::Checker;
import testlang::TypeChecker;

import lang::Builder;

import ParseTree;
import util::Maybe;
import IO;
import String;
import Message;

alias TestLoaderResult = tuple[TestModule testModule, TestRefs refs, map[loc, Type] resolvedTypes, set[Built] importedSpecs];

Log stdOutLog(str message) = println(message);

tuple[set[Message], TestLoaderResult] loadTestModule(loc modLoc, 
  Maybe[TestModule] modulePt = nothing(),
  Log log = stdOutLog) {

  TestModule subject = (just(TestModule tm) := modulePt) ? tm : parseTestModule(modLoc);
  
  set[Built] imports = loadImports(subject);
  
  TestRefs refs = resolveTestRefs(subject, imports);
  set[Message] msgs = checkReferences(subject, refs);
  TypeCheckerResult tcr = checkTypes(subject, imports); 
  
  return <msgs + tcr.messages, <subject, refs, tcr.resolvedTypes, imports>>; 
} 

private set[Built] loadImports(TestModule testModule) {
  loc base = fromModuleDefToLoc(testModule.modDef.fqn);
  
  return {b | Import i <- testModule.imports, <_, just(Built b)> := load(findFile(i.fqn, base))};
}

private loc fromModuleDefToLoc(FullyQualifiedName fqn) {
  loc base = fqn@\loc.top.parent;
  
  for (package <- reverse(["<p>" | /VarName p := fqn]), endsWith(base.path, "<package>")) {
    base = base.parent;
  }
  
  if (!exists(base)) {
    throw "Base directory \'<base>\' does not exist";
  }
  
  return base;
} 

private str toPath(FullyQualifiedName n) = "<("" | "<it><p>/" | /VarName p := n)><n.modName>";  
  
private loc findFile(FullyQualifiedName n, loc baseDir) = baseDir + "/<toPath(n)>.ebl";
