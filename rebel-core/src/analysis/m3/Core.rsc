module analysis::m3::Core

import lang::Syntax;
import lang::Parser;
import lang::Resolver;
import lang::Importer;
import IO;
import Traversal;
import Node;
import ParseTree;

// M3 @decl
anno loc Tree@decl;

// Scope handles scoping for @decl
alias Scope = str;
anno Scope Module@scope;
anno Scope Specification@scope;

// decl scheme roots
loc specScheme = |rebel+specification:///|;
loc libScheme = |rebel+lib:///|;
loc modScheme = |rebel+module:///|;
loc importScheme = |rebel+import:///|;
loc eventScheme = |rebel+event:///|;
loc functionScheme = |rebel+function:///|;
loc invariantScheme = |rebel+invariant:///|;
loc fieldScheme = |rebel+field:///|;
loc eventRefScheme = |rebel+eventRef:///|;
loc invariantRefScheme = |rebel+invariantRef:///|;
loc stateScheme = |rebel+state:///|;

  
Scope unsafeGetScopeFromParent() {
  list[node] parents = getTraversalContextNodes();
  
  //println([ getAnnotations(p)["scope"]? ? <"<p>"[..10], "<getAnnotations(p)["scope"]>"> : "false"  | p <- getTraversalContextNodes() ]);
   
   // get the closest @scope in the parent hierarchy
  result = ("@scope not found on parent of `<parents[0]>`"
           | getAnnotations(parent)["scope"]?
             ? "<getAnnotations(parent)["scope"]>" : it 
           | parent <- reverse(parents)); // Reverse here to simulate fold right instead of fold left (improve for performance)
  //println("@scope for `<parents[0]>` = `<result>`");
  return result;
}

//bool dirtyDebug(a) {       
//  println("DEBUGP: <a>");      
//  return true;     
//}
  
 //visit
Module annotate(Module orig) {
  initModule = orig[@scope = ""]; 
  
  // first we visit the scope/context changing nodes
  contextVisit = top-down visit(initModule) {
    case Module m        => m[@scope = "<m.modDef.fqn>"]
  };
  
  contextVisit2 = top-down visit(contextVisit) {
    case Specification s => s[@scope = unsafeGetScopeFromParent() + "/<s.name>"]
  };
  
  return top-down visit(contextVisit2) {
    // Generic
    case Import i        => i[@decl = importScheme + "<i.fqn>"]
    //Libs
    case m:(Module)`<ModuleDef modDef> <Import* imports> <LibraryModules decls>` => 
      m[@decl = modScheme + "<m.modDef.fqn>"][decls = decls[@decl = libScheme + "<modDef.fqn>"]]
    case EventDef ed     => ed[@decl = eventScheme + unsafeGetScopeFromParent() + "<ed.name>"]
    case FunctionDef fd  => fd[@decl = functionScheme + unsafeGetScopeFromParent() + "<fd.name>"]
    case InvariantDef id => id[@decl = invariantScheme + unsafeGetScopeFromParent() + "<id.name>"]
    // Specs
    case m:(Module)`<ModuleDef modDef> <Import* imports> <Specification spec>` => 
      m[@decl = modScheme + "<m.modDef.fqn>"][spec = spec[@decl = specScheme + unsafeGetScopeFromParent() + "<spec.name>"]]
    case FieldDecl fd    => fd[@decl = fieldScheme + unsafeGetScopeFromParent() + "<fd.name>"]
    case EventRef er     => er[@decl = eventRefScheme + unsafeGetScopeFromParent() + "<er.eventRef>"]
    case InvariantRef id => id[@decl = invariantRefScheme + unsafeGetScopeFromParent() + "<id.invariantRef>"]
    case StateFrom sf    => sf[@decl = stateScheme + unsafeGetScopeFromParent() + "<sf.from>"]
  };
}