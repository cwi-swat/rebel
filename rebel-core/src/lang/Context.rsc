module lang::Context

import lang::ExtendedSyntax;
extend lang::Syntax;
syntax Type = "$$INVALID$$";

data ScopeValue = ScopeValue(loc declareLocation, Type variableType); 
data Scope = scope(loc scopeRange, map[str, ScopeValue] variables);
data Context = globalContext(str specificationName, Scope globalScope) | localContext(str specificationName, Scope globalScope, Scope localScope);

bool isCurrentScope(TypeName name, Context ctx) = "<name>" == ctx.specificationName;
bool inScope(str var, Scope scope) = var in scope.variables;
bool inGlobalScope(str var, Context ctx) = var in ctx.globalScope.variables;
Type getTypeInScope(str var, Context ctx) {
    if (ctx is localContext) {
        if (inScope(var, ctx.localContext.variables)) return ctx.localScope.variables[var].variableType;
    }
    return getTypeInGlobalScope(var, ctx);
}
Type getTypeInGlobalScope(str var, Context ctx) = ctx.globalScope.variables[var].variableType;