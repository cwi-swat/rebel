module lang::TypeChecker

import IO;
import lang::ExtendedSyntax;
extend lang::Syntax;
syntax Type = "$$INVALID$$";
import Node;
import ParseTree;
import Set;
import lang::Parser;
import lang::Importer;
import lang::Resolver;
import lang::Normalizer;
import lang::TypeResolver;

// TODO: move stuff to Checker.rsc and use errors and success there
data TypeError = error(loc location, str error) | success();

list[TypeError] typeCheck(loc location) {
    Module modul = parseModule(location);   
    set[Module] imports = loadImports(modul);
    Refs refs = resolve(modul + imports);
    
    modul = inline(modul, imports, refs);
    return typeCheck(modul.spec);
}

// TODO: introduce type mapper?
// Second pass after type resolver
// visit nodes bottom-up (breadth-first traversal) and append map with types
list[TypeError] typeCheck(Specification spec) {
//  = nested(str name, map[str, Type] vars, map[str, Type] functions, Scope parent)

    // TODO: is the this keyword a good idea actually?
    map[str, ScopeValue] getFieldMap() = ("this.<f.name>" : f.tipe | FieldDecl f <- spec.fields.fields) when spec.fields has fields;
    map[str, ScopeValue] getFunctionMap() = ("<f.name>" : f.returnType | FunctionDef f <- spec.functions.defs) when spec.functions has defs;
    default map[str, ScopeValue] getFieldMap() = ();
    default map[str, ScopeValue] getFunctionMap() = ();
    
    Scope rootScope = root(spec@\loc, getFieldMap() + getFunctionMap());
    return typeCheck(spec, globalContext("<spec.name>", globalScope));
}

list[TypeError] typeCheck(Specification s, Context ctx) = [ x | x <- ([] | it + typeCheck(ev, ctx) | EventDef ev <- s.events.events), x is error ] when s has events;
list[TypeError] typeCheck(Specification s, Context ctx) = [];

list[TypeError] typeCheck(EventDef ev, Context ctx) {
    // We now have to add a local scope (a larger context)
    localScopeMap = ("<p.name>" : ScopeValue(p@\loc, p.tipe) | Parameter p <- ev.transitionParams);
    localCtx = localContext(ctx.specificationName, ctx.globalScope, scope(ev@\loc, localScopeMap));

    // TODO: add types to map for declarations in local/global scope?
    errors = typeCheck(ev.pre, ctx) + typeCheck(ev.post, ctx);
    // TODO: syncblock

    return errors;
}

list[TypeError] typeCheck(Preconditions? pre, Context ctx) = typeCheck(p.stats, ctx) when (/Preconditions p := pre);
default list[TypeError] typeCheck(Preconditions? _, Context ctx) = [];

list[TypeError] typeCheck(Postconditions? post, Context ctx) = typeCheck(removePostConditionPrefix(p.stats), ctx) when (/Postconditions p := post);
default list[TypeError] typeCheck(Postconditions? _, Context ctx) = [];
Statement* removePostConditionPrefix(Statement* stats) = visit (stats) { case (Expr)`new this.<VarName v>` => (Expr)`this.<VarName v>` };

// This context is necessary
TypeError typeCheck((Statement)`<Annotations _><Expr e>;`, Context ctx) {
    Type resolvedType = resolveTypeCached(e, ctx);
    if (resolvedType == (Type)`$$TYPE_ERROR$$`) {
        return error(e@\loc, "Could not resolve expression <e>");
    }
    return success();
}
default list[TypeError] typeCheck(Statement s, Context ctx) = error(s@\loc, "Unsupported type of statement: <s>");

list[TypeError] typeCheck(Statement* stats, Context ctx) {
    return for (Statement stat <- stats) append typeCheck(stat, ctx);
}