@license{
Copyright (c) 2016, CWI
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
@contributor{Jouke Stoel - jouke.stoel@cwi.nl - CWI}
module lang::TypeInferrer

import IO;
import Node;
import ParseTree;
import Set;

extend lang::ExtendedSyntax;

syntax Type 
  = "$$INVALID_TYPE$$"
  | "$$SPEC_TYPE$$"
  ;

data Context = context(Scope scp); 

data Scope
  = nested(str name, map[str, Type] vars, Scope parent)
  | root(str name, map[str, Type] vars, map[str, Type] functions, map[str, Type] referrencedSpecs)
  ;

Type getTypeOfVar(str name, Scope scope) = scope.vars[name]
  when name in scope.vars;

Type getTypeOfVar(str name, Scope scope) = getTypeOfVar(name, scope.parent)
  when name notin scope.vars,
    scope is nested;
    
default Type getTypeOfVar(str name, Scope scope) = (Type)`$$INVALID_TYPE$$`;

Type getTypeOfFunction(str name, Scope scope) = scope.parent.functions[name]
  when scope is nested,
       name in scope.parent.functions;

default Type getTypeOfFunction(str name, Scope scope) = (Type)`$$INVALID_TYPE$$`;

Type getTypeOfSpec(str name, Scope scope) = scope.parent.referrencedSpecs[name]
  when scope is nested,
       name in scope.parent.referrencedSpecs;
default Type getTypeOfSpec(str name, Scope scope) = (Type)`$$INVALID_TYPE$$`;

bool inScope(str name, Scope scope) = inCurrentScope(name, scope) || inScope(name, scope.parent) when (scope is nested);
bool inScope(str name, Scope scope) = inCurrentScope(name, scope) || name in scope.referrencedSpecs;
private bool inCurrentScope(str name, Scope scope) = name == scope.name || name in scope.vars;

@memo
Type resolveTypeCached(Expr exp, Context ctx) = resolveType(exp, ctx);

// Negative
Type resolveNegative((Type)`Integer`) = (Type)`Integer`;
Type resolveNegative((Type)`Money`) = (Type)`Money`;

// Subtraction
Type resolveSubtraction((Type)`Integer`, (Type)`Integer`) = (Type)`Integer`;
Type resolveSubtraction((Type)`Date`,    (Type)`Term`)    = (Type)`Date`;
Type resolveSubtraction((Type)`Date`,    (Type)`Date`)    = (Type)`Term`;
Type resolveSubtraction((Type)`Money`,   (Type)`Money`)   = (Type)`Money`;
default Type resolveSubtraction(Type _, Type _)           = (Type)`$$INVALID_TYPE$$`;

// Plus
Type resolveAddition((Type)`Integer`,   (Type)`Integer`) = (Type)`Integer`;
Type resolveAddition((Type)`Date`,      (Type)`Date`)    = (Type)`Term`;
Type resolveAddition((Type)`Date`,      (Type)`Term`)    = (Type)`Date`;
Type resolveAddition((Type)`Money`,     (Type)`Money`)   = (Type)`Money`;
default Type resolveAddition(Type _, Type _)             = (Type)`$$INVALID_TYPE$$`;

// Multiply
Type resolveMultiplication((Type)`Money`,       (Type)`Integer`)    = (Type)`Money`;
Type resolveMultiplication((Type)`Integer`,     (Type)`Money`)      = (Type)`Money`;
Type resolveMultiplication((Type)`Period`,      (Type)`Integer`)    = (Type)`Term`;
Type resolveMultiplication((Type)`Integer`,     (Type)`Period`)     = (Type)`Term`;
Type resolveMultiplication((Type)`Integer`,     (Type)`Percentage`) = (Type)`Percentage`;
Type resolveMultiplication((Type)`Percentage`,  (Type)`Integer`)    = (Type)`Percentage`;
Type resolveMultiplication((Type)`Percentage`,  (Type)`Money`)      = (Type)`Money`;
Type resolveMultiplication((Type)`Money`,       (Type)`Percentage`) = (Type)`Money`;

Type resolveType((Expr)`-<Expr exp>`, Context ctx) = resolveNegative(resolveTypeCached(exp, ctx));

Type resolveType((Expr)`<Expr lhs> - <Expr rhs>`, Context ctx) = resolveSubtraction(resolveTypeCached(lhs, ctx), resolveTypeCached(rhs, ctx));
Type resolveType((Expr)`<Expr lhs> + <Expr rhs>`, Context ctx) = resolveAddition(resolveTypeCached(lhs, ctx), resolveTypeCached(rhs, ctx));
Type resolveType((Expr)`<Expr lhs> * <Expr rhs>`, Context ctx) = resolveMultiplication(resolveTypeCached(lhs, ctx), resolveTypeCached(rhs, ctx));

// Comparisons and boolean logic
Type resolveType((Expr)`<Expr lhs> == <Expr rhs>`, Context ctx) = (Type)`Boolean` when resolveTypeCached(lhs, ctx) == resolveTypeCached(rhs, ctx);
Type resolveType((Expr)`<Expr lhs> \>= <Expr rhs>`, Context ctx) = (Type)`Boolean` when resolveTypeCached(lhs, ctx) == resolveTypeCached(rhs, ctx);
Type resolveType((Expr)`<Expr lhs> \<= <Expr rhs>`, Context ctx) = (Type)`Boolean` when resolveTypeCached(lhs, ctx) == resolveTypeCached(rhs, ctx);
Type resolveType((Expr)`<Expr lhs> != <Expr rhs>`, Context ctx) = (Type)`Boolean` when resolveTypeCached(lhs, ctx) == resolveTypeCached(rhs, ctx);
Type resolveType((Expr)`<Expr lhs> \> <Expr rhs>`, Context ctx) = (Type)`Boolean` when resolveTypeCached(lhs, ctx) == resolveTypeCached(rhs, ctx);
Type resolveType((Expr)`<Expr lhs> \< <Expr rhs>`, Context ctx) = (Type)`Boolean` when resolveTypeCached(lhs, ctx) == resolveTypeCached(rhs, ctx);
Type resolveType((Expr)`<Expr lhs> && <Expr rhs>`, Context ctx) = (Type)`Boolean` when resolveTypeCached(lhs, ctx) == (Type)`Boolean` && resolveTypeCached(rhs, ctx) == (Type)`Boolean`;
Type resolveType((Expr)`<Expr lhs> || <Expr rhs>`, Context ctx) = (Type)`Boolean` when resolveTypeCached(lhs, ctx) == (Type)`Boolean` && resolveTypeCached(rhs, ctx) == (Type)`Boolean`;
Type resolveType((Expr)`<Expr lhs> -\> <Expr rhs>`, Context ctx) = (Type)`Boolean` when resolveTypeCached(lhs, ctx) == (Type)`Boolean` && resolveTypeCached(rhs, ctx) == (Type)`Boolean`;

// In for structured expressions
Type resolveType((Expr)`<Expr lhs> in <Expr rhs>`, Context ctx) = (Type)`Boolean` when (Type)`set [<Type rhsType>]` := resolveTypeCached(rhs, ctx) && rhsType == resolveTypeCached(lhs, ctx); 

Type resolveType((Expr)`this`, Context ctx) = (Type)`$$SPEC_TYPE$$`;

// Field access
Type resolveType((Expr)`this.<VarName rhs>`, Context ctx) = tipe when Type tipe := getTypeOfVar("this.<rhs>", ctx.scp);
Type resolveType((Expr)`<Expr lhs>.currency`, Context ctx) = (Type)`Currency` when resolveTypeCached(lhs, ctx) == (Type)`Money`;
Type resolveType((Expr)`<Expr lhs>.amount`, Context ctx) = (Type)`Integer` when resolveTypeCached(lhs, ctx) == (Type)`Money`;
Type resolveType((Expr)`<Expr lhs>.countryCode`, Context ctx) = (Type)`String` when resolveTypeCached(lhs, ctx) == (Type)`IBAN`;
Type resolveType((Expr)`<Expr lhs>.time`, Context ctx) = (Type)`Time` when resolveTypeCached(lhs, ctx) == (Type)`DateTime`;
Type resolveType((Expr)`<Expr lhs>.date`, Context ctx) = (Type)`Date` when resolveTypeCached(lhs, ctx) == (Type)`DateTime`;
Type resolveType((Expr)`<Expr lhs>.<VarName rhs>`, Context ctx) = (Type)`Integer` when resolveTypeCached(lhs, ctx) == (Type)`Date` && "<rhs>" in { "day", "month", "year" };
Type resolveType((Expr)`<Expr lhs>.<VarName rhs>`, Context ctx) = (Type)`Integer` when resolveTypeCached(lhs, ctx) == (Type)`Time` && "<rhs>" in { "hour", "minutes", "seconds" };
//Type resolveType((Expr)`<Expr lhs>.<VarName rhs>`, Context ctx) = rhsType when rhsType := resolveTypeCached(rhs, ctx); // TODO perhaps append context to find rhs

Type resolveType((Expr)`new <Expr exp>`, Context ctx) = resolveTypeCached(exp, ctx); 

Type resolveType((Expr)`not <Expr _>`, Context ctx) = (Type)`Boolean`;
Type resolveType((Expr)`initialized <Expr exp>`, Context ctx) = (Type)`Boolean`;
Type resolveType((Expr)`finalized <Expr exp>`, Context ctx) = (Type)`Boolean`;

Type resolveType((Expr)`<TypeName otherSpec>[<Expr _>]`, Context ctx) = resolveType((Expr)`<TypeName otherSpec>`, ctx);
Type resolveType((Expr)`<TypeName otherSpec>`, Context ctx) = getTypeOfSpec("<otherSpec>", ctx.scp);

Type resolveType((Expr)`<Expr _> instate <Expr _>`) = (Type)`Boolean`;
 
// Function calls
Type resolveType((Expr)`<VarName function>(<{Expr ","}* exprs>)`, Context ctx) = getTypeOfFunction("<function>", ctx.scp);

// Literals
Type resolveType((Expr)`{<{Expr ","}* elements>}`, Context ctx) = (Type)`set [<Type subType>]` when /Expr e := elements && subType := resolveTypeCached(e, ctx); // sets are homogenous so we take the type of the first element
Type resolveType((Expr)`(<{MapElement ","}* elements>)`, Context ctx) =  (Type)`map [<Type keyType> : <Type valueType>]` when /MapElement e := elements && keyType := resolveTypeCached(e.key, ctx) && valueType := resolveTypeCached(e.val, ctx); // maps are homogenous so we take the type of the first element 
Type resolveType((Expr)`<Int _>`, Context _)        = (Type)`Integer`;
Type resolveType((Expr)`<Bool _>`, Context _)       = (Type)`Boolean`;
Type resolveType((Expr)`<String _>`, Context _)     = (Type)`String`;
Type resolveType((Expr)`<Percentage _>`, Context _) = (Type)`Percentage`;
Type resolveType((Expr)`<Date _>`, Context _)       = (Type)`Date`;
Type resolveType((Expr)`<Time _>`, Context _)       = (Type)`Time`;
Type resolveType((Expr)`<DateTime _>`, Context _)   = (Type)`DateTime`;
Type resolveType((Expr)`<Period _>`, Context _)     = (Type)`Period`;
Type resolveType((Expr)`<Term _>`, Context _)       = (Type)`Term`;
Type resolveType((Expr)`<Frequency _>`, Context _)  = (Type)`Frequency`;
Type resolveType((Expr)`<Money _>`, Context _)      = (Type)`Money`;
Type resolveType((Expr)`<Currency _>`, Context _)   = (Type)`Currency`;
Type resolveType((Expr)`<Term _>`, Context _)       = (Type)`Term`;
Type resolveType((Expr)`<IBAN _>`, Context _)       = (Type)`IBAN`;
Type resolveType((Expr)`now`, Context _)            = (Type)`DateTime`;
Type resolveType((Expr)`<Ref r>`, Context ctx)      = getTypeOfVar("<r>", ctx.scp);

Type resolveType((Expr)`(<Expr expr>)`, Context ctx) = resolveTypeCached(expr, ctx);

default Type resolveType((Expr)`<Expr e>`, Context _) = (Type)`$$INVALID_TYPE$$`;