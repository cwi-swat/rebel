@license{
Copyright (c) 2016, CWI
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
@contributor{Jouke Stoel - jouke.stoel@cwi.nl - CWI}
module lang::TypeResolver

import IO;
import lang::ExtendedSyntax;
extend lang::Syntax;
syntax Type = "$$INVALID$$";
import Node;
import ParseTree;
import Set;

// Invalid type should have originator location
data ScopeKey = scopeKey(loc declareLocation, Type variableType); 
data Scope = scope(loc scopeRange, map[str, ScopeKey] variables);
data Context = globalContext(str specificationName, Scope globalScope) | localContext(str specificationName, Scope globalScope, Scope localScope);

bool isCurrentScope(TypeName name, Context ctx) = "<name>" == ctx.specificationName;
bool inScope(str var, Scope scope) = var in scope.variables;
Type getTypeInScope(str var, Context ctx) {
    if (ctx is localContext) {
        if (inScope(var, ctx.localContext.variables)) return ctx.localScope.variables[var].variableType;
    }
    return ctx.globalScope.variables[var].variableType;
}

// Subtraction
Type resolveType((Expr)`<Expr lhs> - <Expr rhs>`, Context ctx) = (Type)`Integer` when resolveType(lhs, ctx) == (Type)`Integer` && resolveType(rhs, ctx) == (Type)`Integer`;
Type resolveType((Expr)`<Expr lhs> - <Expr rhs>`, Context ctx) = (Type)`Date` when resolveType(lhs, ctx) == (Type)`Date` && resolveType(rhs, ctx) == (Type)`Term`;
Type resolveType((Expr)`<Expr lhs> - <Expr rhs>`, Context ctx) = (Type)`Integer` when resolveType(lhs, ctx) == (Type)`Integer` && resolveType(rhs, ctx) == (Type)`Integer`;
Type resolveType((Expr)`<Expr lhs> - <Expr rhs>`, Context ctx) = (Type)`Money` when resolveType(lhs, ctx) == (Type)`Money` && resolveType(rhs, ctx) == (Type)`Money`;
Type resolveType((Expr)`<Expr lhs> - <Expr rhs>`, Context ctx) = (Type)`Term` when resolveType(lhs, ctx) == (Type)`Date` && resolveType(rhs, ctx) == (Type)`Time`; // temp for "now" keyword

// Plus
Type resolveType((Expr)`<Expr lhs> + <Expr rhs>`, Context ctx) = (Type)`Integer` when resolveType(lhs, ctx) == (Type)`Integer` && resolveType(rhs, ctx) == (Type)`Integer`;
Type resolveType((Expr)`<Expr lhs> + <Expr rhs>`, Context ctx) = (Type)`Date` when resolveType(lhs, ctx) == (Type)`Date` && resolveType(rhs, ctx) == (Type)`Term`;
Type resolveType((Expr)`<Expr lhs> + <Expr rhs>`, Context ctx) = (Type)`Date` when resolveType(lhs, ctx) == (Type)`Term` && resolveType(rhs, ctx) == (Type)`Date`;
Type resolveType((Expr)`<Expr lhs> + <Expr rhs>`, Context ctx) = (Type)`Money` when resolveType(lhs, ctx) == (Type)`Integer` && resolveType(rhs, ctx) == (Type)`Money`;

// Multiply
Type resolveType((Expr)`<Expr lhs> * <Expr rhs>`, Context ctx) = (Type)`Money` when resolveType(lhs, ctx) == (Type)`Integer` && resolveType(rhs, ctx) == (Type)`Money`;
Type resolveType((Expr)`<Expr lhs> * <Expr rhs>`, Context ctx) = (Type)`Money` when resolveType(lhs, ctx) == (Type)`Money` && resolveType(rhs, ctx) == (Type)`Integer`;
Type resolveType((Expr)`<Expr lhs> * <Expr rhs>`, Context ctx) = (Type)`Term` when resolveType(lhs, ctx) == (Type)`Integer` && resolveType(rhs, ctx) == (Type)`Period`;
Type resolveType((Expr)`<Expr lhs> * <Expr rhs>`, Context ctx) = (Type)`Term` when resolveType(lhs, ctx) == (Type)`Period` && resolveType(rhs, ctx) == (Type)`Integer`;
Type resolveType((Expr)`<Expr lhs> * <Expr rhs>`, Context ctx) = (Type)`Percentage` when resolveType(lhs, ctx) == (Type)`Integer` && resolveType(rhs, ctx) == (Type)`Percentage`;
Type resolveType((Expr)`<Expr lhs> * <Expr rhs>`, Context ctx) = (Type)`Percentage` when resolveType(lhs, ctx) == (Type)`Percentage` && resolveType(rhs, ctx) == (Type)`Integer`;
Type resolveType((Expr)`<Expr lhs> * <Expr rhs>`, Context ctx) = (Type)`Money` when resolveType(lhs, ctx) == (Type)`Percentage` && resolveType(rhs, ctx) == (Type)`Money`;
Type resolveType((Expr)`<Expr lhs> * <Expr rhs>`, Context ctx) = (Type)`Money` when resolveType(lhs, ctx) == (Type)`Money` && resolveType(rhs, ctx) == (Type)`Percentage`;

// Comparisons and boolean logic
Type resolveType((Expr)`<Expr lhs> == <Expr rhs>`, Context ctx) = (Type)`Boolean` when resolveType(lhs, ctx) == resolveType(rhs, ctx);
Type resolveType((Expr)`<Expr lhs> \>= <Expr rhs>`, Context ctx) = (Type)`Boolean` when resolveType(lhs, ctx) == resolveType(rhs, ctx);
Type resolveType((Expr)`<Expr lhs> \<= <Expr rhs>`, Context ctx) = (Type)`Boolean` when resolveType(lhs, ctx) == resolveType(rhs, ctx);
Type resolveType((Expr)`<Expr lhs> != <Expr rhs>`, Context ctx) = (Type)`Boolean` when resolveType(lhs, ctx) == resolveType(rhs, ctx);
Type resolveType((Expr)`<Expr lhs> \> <Expr rhs>`, Context ctx) = (Type)`Boolean` when resolveType(lhs, ctx) == resolveType(rhs, ctx);
Type resolveType((Expr)`<Expr lhs> \< <Expr rhs>`, Context ctx) = (Type)`Boolean` when resolveType(lhs, ctx) == resolveType(rhs, ctx);
Type resolveType((Expr)`<Expr lhs> && <Expr rhs>`, Context ctx) = (Type)`Boolean` when resolveType(lhs, ctx) == (Type)`Boolean` && resolveType(rhs, ctx) == (Type)`Boolean`;
Type resolveType((Expr)`<Expr lhs> || <Expr rhs>`, Context ctx) = (Type)`Boolean` when resolveType(lhs, ctx) == (Type)`Boolean` && resolveType(rhs, ctx) == (Type)`Boolean`;

// In for structured expressions
Type resolveType((Expr)`<Expr lhs> in <Expr rhs>`, Context ctx) = (Type)`Boolean` when resolveType(lhs, ctx) == (Type)`set [<Type _>]` && resolveType(rhs, ctx) == (Type)`Set`;

// Field access
Type resolveType((Expr)`<Expr lhs>.<Expr rhs>`, Context ctx) = (Type)`Integer` when resolveType(lhs, ctx) == (Type)`Date` && "<rhs>" in { "day", "month", "year" };
Type resolveType((Expr)`<Expr lhs>.<Expr rhs>`, Context ctx) = (Type)`Integer` when resolveType(lhs, ctx) == (Type)`Time` && "<rhs>" in { "hour", "minutes", "seconds", "timestamp" };
Type resolveType((Expr)`<Expr lhs>.<Expr rhs>`, Context ctx) = (Type)`Currency` when resolveType(lhs, ctx) == (Type)`Money` && "<rhs>" == "currency";
Type resolveType((Expr)`<Expr lhs>.<Expr rhs>`, Context ctx) = (Type)`Integer` when resolveType(lhs, ctx) == (Type)`Money` && "<rhs>" == "amount";
Type resolveType((Expr)`<Expr lhs>.<Expr rhs>`, Context ctx) = (Type)`String` when resolveType(lhs, ctx) == (Type)`IBAN` && "<rhs>" == "countryCode";
Type resolveType((Expr)`<Expr lhs>.<Expr rhs>`, Context ctx) = rhsType when (Type)`<TypeName custom>` := resolveType(lhs, ctx) && isCurrentScope(custom, ctx) && rhsType := resolveType(rhs, ctx); // spec is referring to itself
Type resolveType((Expr)`<Expr lhs>.<Expr rhs>`, Context ctx) = rhsType when (Type)`<TypeName custom>` := resolveType(lhs, ctx) && rhsType := resolveType(rhs, ctx); // TODO perhaps append context to find rhs

// Literals
Type resolveType((Expr)`{<{Expr ","}* elements>}`, Context _) = (Type)`set [<Type subType>]` when /Expr e := elements && subType := resolveType(e[0], ctx); // sets are homogenous so we take the type of the first element
Type resolveType((Expr)`(<{MapElement ","}* elements>)`, Context _) =  (Type)`map [<Type keyType> : <Type valueType>]` when /MapElement e := elements && keyType := resolveType(e[0].key, ctx) && valueType := resolveType(e[0].val, ctx); // maps are homogenous so we take the type of the first element 

// Literals
Type resolveType((Expr)`<Int _>`, Context _) = (Type)`Integer`;
Type resolveType((Expr)`<Bool _>`, Context _) = (Type)`Boolean`;
Type resolveType((Expr)`<String _>`, Context _) = (Type)`String`;
Type resolveType((Expr)`<Percentage _>`, Context _) = (Type)`Percentage`;
Type resolveType((Expr)`<Date _>`, Context _) = (Type)`Date`;
Type resolveType((Expr)`<Time _>`, Context _) = (Type)`Time`;
Type resolveType((Expr)`<Period _>`, Context _) = (Type)`Period`;
Type resolveType((Expr)`<Frequency _>`, Context _) = (Type)`Frequency`;
Type resolveType((Expr)`<Money _>`, Context _) = (Type)`Money`;
Type resolveType((Expr)`<Currency _>`, Context _) = (Type)`Currency`;
Type resolveType((Expr)`<Term _>`, Context _) = (Type)`Term`;
Type resolveType((Expr)`<IBAN _>`, Context _) = (Type)`IBAN`;
Type resolveType((Expr)`<Ref r>`, Context ctx) = getTypeInScope("<r>", ctx);
Type resolveType((Expr)`this`, Context ctx) = (Type)`<TypeName name>` when name := ctx.specificationName; // allows us to refer to own instance
// TODO build propagation for parentheses etc


default Type resolveType((Expr)`<Expr e>`, Context _) {
    throw "Could not resolve expression <e>";
}

// visit nodes bottom-up (breadth-first traversal) and append map with types
map[loc, Type] getTypeMapping(Specification spec) {
    // TODO: is the this keyword a good idea actually?
    Scope getGlobalScope(Specification spec) = scope(spec@\loc, ("<f.name>" : scopeKey(f@\loc, f.tipe) | FieldDecl f <- spec.fields.fields)) when spec.fields has fields;
    default Scope getGlobalScope(Specification spec) = scope(spec@\loc, ());
    return visitNode(spec, globalContext("<spec.name>", getGlobalScope(spec)), ());
}

map[loc, Type] visitNode(Specification s, Context ctx, map[loc, Type] typeMap) {
    if (s has events) {
        for (EventDef ev <- s.events.events) {
            typeMap = visitNode(ev, ctx, typeMap);
        }
    }
    return typeMap;
}

map[loc, Type] visitNode(EventDef ev, Context ctx, map[loc, Type] typeMap) {
    // We now have to add a local scope (a larger context)
    localScopeMap = ( "<p.name>" : scopeKey(p@\loc, p.tipe) | Parameter p <- ev.transitionParams);
    localCtx = localContext(ctx.specificationName, ctx.globalScope, scope(ev@\loc, localScopeMap));

    // TODO: add types to map for declarations in local/global scope?
    typeMap = visitNode(ev.pre, ctx, typeMap);
    typeMap = visitNode(ev.post, ctx, typeMap);
    // TODO: syncblock

    return typeMap;
}

map[loc, Type] visitNode(Preconditions? pre, Context ctx, map[loc, Type] typeMap) = visitNode(p.stats, ctx, typeMap) when (/Preconditions p := pre);
default map[loc, Type] visitNode(Preconditions? _, Context ctx, map[loc, Type] typeMap) = typeMap;

map[loc, Type] visitNode(Postconditions? post, Context ctx, map[loc, Type] typeMap) = visitNode(removePostConditionPrefix(p.stats), ctx, typeMap) when (/Postconditions p := post);
default map[loc, Type] visitNode(Postconditions? _, Context ctx, map[loc, Type] typeMap) = typeMap;
Statement* removePostConditionPrefix(Statement* stats, map[loc, Type] typeMap) = visit (stats) { case (Expr)`new this.<VarName v>` => (Expr)`this.<VarName v>` };

map[loc, Type] visitNode((Statement)`<Annotations _><Expr e>;`, Context ctx, map[loc, Type] typeMap) {
    Type resolvedType = resolveType(e, ctx);
    println("Resolved: <e> to <resolvedType>");
    typeMap[e@\loc] = resolvedType;
    return typeMap;    
}
default map[loc, Type] visitNode(Statement s, Context ctx, map[loc, Type] typeMap) {
    println("Unsupported statement type");
    return typeMap;
}

map[loc, Type] visitNode(Statement* stats, Context ctx, map[loc, Type] typeMap) {
    for (Statement stat <- stats) typeMap = visitNode(stat, ctx, typeMap);
    return typeMap;
}