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
extend lang::ExtendedSyntax;
import Node;
import ParseTree;
import Set;
//import lang::Context;

syntax Type = "$$TYPE_ERROR$$";

data Context = context(Scope scp); 

data Scope
  = nested(str name, map[str, Type] vars, map[str, Type] functions, Scope parent)
  | root(str name, map[str, Type] vars)
  ;

Type getTypeOfVar(str name, Scope scope) = scope.vars[name]
  when name in scope.vars;

Type getTypeOfVar(str name, Scope scope) = getTypeOfVar(name, scope.parent)
  when name notin scope.vars,
    scope is nested;
    
default Type getTypeOfVar(str name, Scope scope) { throw "Variable \'<name>\' not found in scopes"; }

Type getTypeOfFunction(str name, Scope scope) = scope.functions[name]
  when scope is nested,
       name in scope.functions;

default Type getTypeOfFunction(str name, Scope scope) { throw "Function \'<name>\' not found in scopes"; }

@memo
Type resolveTypeCached(Expr exp, Context ctx) = resolveType(exp, ctx);

// Subtraction
Type resolveType((Expr)`<Expr lhs> - <Expr rhs>`, Context ctx) = (Type)`Integer` when resolveTypeCached(lhs, ctx) == (Type)`Integer` && resolveTypeCached(rhs, ctx) == (Type)`Integer`;
Type resolveType((Expr)`<Expr lhs> - <Expr rhs>`, Context ctx) = (Type)`Date` when resolveTypeCached(lhs, ctx) == (Type)`Date` && resolveTypeCached(rhs, ctx) == (Type)`Term`;
Type resolveType((Expr)`<Expr lhs> - <Expr rhs>`, Context ctx) = (Type)`Term` when resolveTypeCached(lhs, ctx) == (Type)`Date` && resolveTypeCached(rhs, ctx) == (Type)`Date`;
Type resolveType((Expr)`<Expr lhs> - <Expr rhs>`, Context ctx) = (Type)`Integer` when resolveTypeCached(lhs, ctx) == (Type)`Integer` && resolveTypeCached(rhs, ctx) == (Type)`Integer`;
Type resolveType((Expr)`<Expr lhs> - <Expr rhs>`, Context ctx) = (Type)`Money` when resolveTypeCached(lhs, ctx) == (Type)`Money` && resolveTypeCached(rhs, ctx) == (Type)`Money`;

// Plus
Type resolveType((Expr)`<Expr lhs> + <Expr rhs>`, Context ctx) = (Type)`Integer` when resolveTypeCached(lhs, ctx) == (Type)`Integer` && resolveTypeCached(rhs, ctx) == (Type)`Integer`;
Type resolveType((Expr)`<Expr lhs> + <Expr rhs>`, Context ctx) = (Type)`Date` when resolveTypeCached(lhs, ctx) == (Type)`Date` && resolveTypeCached(rhs, ctx) == (Type)`Term`;
Type resolveType((Expr)`<Expr lhs> + <Expr rhs>`, Context ctx) = (Type)`Date` when resolveTypeCached(lhs, ctx) == (Type)`Term` && resolveTypeCached(rhs, ctx) == (Type)`Date`;
Type resolveType((Expr)`<Expr lhs> + <Expr rhs>`, Context ctx) = (Type)`Money` when resolveTypeCached(lhs, ctx) == (Type)`Integer` && resolveTypeCached(rhs, ctx) == (Type)`Money`;

// Multiply
Type resolveType((Expr)`<Expr lhs> * <Expr rhs>`, Context ctx) = (Type)`Money` when resolveTypeCached(lhs, ctx) == (Type)`Integer` && resolveTypeCached(rhs, ctx) == (Type)`Money`;
Type resolveType((Expr)`<Expr lhs> * <Expr rhs>`, Context ctx) = (Type)`Money` when resolveTypeCached(lhs, ctx) == (Type)`Money` && resolveTypeCached(rhs, ctx) == (Type)`Integer`;
Type resolveType((Expr)`<Expr lhs> * <Expr rhs>`, Context ctx) = (Type)`Term` when resolveTypeCached(lhs, ctx) == (Type)`Integer` && resolveTypeCached(rhs, ctx) == (Type)`Period`;
Type resolveType((Expr)`<Expr lhs> * <Expr rhs>`, Context ctx) = (Type)`Term` when resolveTypeCached(lhs, ctx) == (Type)`Period` && resolveTypeCached(rhs, ctx) == (Type)`Integer`;
Type resolveType((Expr)`<Expr lhs> * <Expr rhs>`, Context ctx) = (Type)`Percentage` when resolveTypeCached(lhs, ctx) == (Type)`Integer` && resolveTypeCached(rhs, ctx) == (Type)`Percentage`;
Type resolveType((Expr)`<Expr lhs> * <Expr rhs>`, Context ctx) = (Type)`Percentage` when resolveTypeCached(lhs, ctx) == (Type)`Percentage` && resolveTypeCached(rhs, ctx) == (Type)`Integer`;
Type resolveType((Expr)`<Expr lhs> * <Expr rhs>`, Context ctx) = (Type)`Money` when resolveTypeCached(lhs, ctx) == (Type)`Percentage` && resolveTypeCached(rhs, ctx) == (Type)`Money`;
Type resolveType((Expr)`<Expr lhs> * <Expr rhs>`, Context ctx) = (Type)`Money` when resolveTypeCached(lhs, ctx) == (Type)`Money` && resolveTypeCached(rhs, ctx) == (Type)`Percentage`;

// Comparisons and boolean logic
Type resolveType((Expr)`<Expr lhs> == <Expr rhs>`, Context ctx) = (Type)`Boolean` when resolveTypeCached(lhs, ctx) == resolveTypeCached(rhs, ctx);
Type resolveType((Expr)`<Expr lhs> \>= <Expr rhs>`, Context ctx) = (Type)`Boolean` when resolveTypeCached(lhs, ctx) == resolveTypeCached(rhs, ctx);
Type resolveType((Expr)`<Expr lhs> \<= <Expr rhs>`, Context ctx) = (Type)`Boolean` when resolveTypeCached(lhs, ctx) == resolveTypeCached(rhs, ctx);
Type resolveType((Expr)`<Expr lhs> != <Expr rhs>`, Context ctx) = (Type)`Boolean` when resolveTypeCached(lhs, ctx) == resolveTypeCached(rhs, ctx);
Type resolveType((Expr)`<Expr lhs> \> <Expr rhs>`, Context ctx) = (Type)`Boolean` when resolveTypeCached(lhs, ctx) == resolveTypeCached(rhs, ctx);
Type resolveType((Expr)`<Expr lhs> \< <Expr rhs>`, Context ctx) = (Type)`Boolean` when resolveTypeCached(lhs, ctx) == resolveTypeCached(rhs, ctx);
Type resolveType((Expr)`<Expr lhs> && <Expr rhs>`, Context ctx) = (Type)`Boolean` when resolveTypeCached(lhs, ctx) == (Type)`Boolean` && resolveTypeCached(rhs, ctx) == (Type)`Boolean`;
Type resolveType((Expr)`<Expr lhs> || <Expr rhs>`, Context ctx) = (Type)`Boolean` when resolveTypeCached(lhs, ctx) == (Type)`Boolean` && resolveTypeCached(rhs, ctx) == (Type)`Boolean`;

// In for structured expressions
Type resolveType((Expr)`<Expr lhs> in <Expr rhs>`, Context ctx) = (Type)`Boolean` when (Type)`set [<Type rhsType>]` := resolveTypeCached(rhs, ctx) && rhsType == resolveTypeCached(lhs, ctx); 

// Field access
Type resolveType((Expr)`this.<VarName rhs>`, Context ctx) = tipe when Type tipe := getTypeOfVar("this.<rhs>", ctx.scp);
Type resolveType((Expr)`<Expr lhs>.currency`, Context ctx) = (Type)`Currency` when resolveTypeCached(lhs, ctx) == (Type)`Money`;
Type resolveType((Expr)`<Expr lhs>.amount`, Context ctx) = (Type)`Integer` when resolveTypeCached(lhs, ctx) == (Type)`Money`;
Type resolveType((Expr)`<Expr lhs>.countryCode`, Context ctx) = (Type)`String` when resolveTypeCached(lhs, ctx) == (Type)`IBAN`;
Type resolveType((Expr)`<Expr lhs>.time`, Context ctx) = (Type)`Time` when resolveTypeCached(lhs, ctx) == (Type)`DateTime`;
Type resolveType((Expr)`<Expr lhs>.date`, Context ctx) = (Type)`Date` when bprintln(lhs), resolveTypeCached(lhs, ctx) == (Type)`DateTime`;
Type resolveType((Expr)`<Expr lhs>.<VarName rhs>`, Context ctx) = (Type)`Integer` when resolveTypeCached(lhs, ctx) == (Type)`Date` && "<rhs>" in { "day", "month", "year" };
Type resolveType((Expr)`<Expr lhs>.<VarName rhs>`, Context ctx) = (Type)`Integer` when resolveTypeCached(lhs, ctx) == (Type)`Time` && "<rhs>" in { "hour", "minutes", "seconds" };
Type resolveType((Expr)`<Expr lhs>.<VarName rhs>`, Context ctx) = rhsType when (Type)`<TypeName custom>` := resolveTypeCached(lhs, ctx) && isCurrentScope(custom, ctx) && rhsType := resolveTypeCached(rhs, ctx); // spec is referring to itself
Type resolveType((Expr)`<Expr lhs>.<VarName rhs>`, Context ctx) = rhsType when (Type)`<TypeName custom>` := resolveTypeCached(lhs, ctx) && rhsType := resolveTypeCached(rhs, ctx); // TODO perhaps append context to find rhs

Type resolveType((Expr)`new <Expr exp>`, Context ctx) = resolveTypeCached(exp, ctx); 

// Field access on specific types
// TODO

// Function calls
Type resolveType((Expr)`<VarName function>(<{Expr ","}* exprs>)`, Context ctx) = getTypeOfFunction("<function>", ctx.scp);

// Literals
Type resolveType((Expr)`{<{Expr ","}* elements>}`, Context ctx) = (Type)`set [<Type subType>]` when /Expr e := elements && subType := resolveTypeCached(e, ctx); // sets are homogenous so we take the type of the first element
Type resolveType((Expr)`(<{MapElement ","}* elements>)`, Context ctx) =  (Type)`map [<Type keyType> : <Type valueType>]` when /MapElement e := elements && keyType := resolveTypeCached(e.key, ctx) && valueType := resolveTypeCached(e.val, ctx); // maps are homogenous so we take the type of the first element 

// Literals
Type resolveType((Expr)`<DateTime _>`, Context _) = (Type)`DateTime`;
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
Type resolveType((Expr)`now`, Context _) = (Type)`DateTime`;
Type resolveType((Expr)`<Ref r>`, Context ctx) = getTypeOfVar("<r>", ctx.scp);

// TODO build propagation for parentheses etc

default Type resolveType((Expr)`<Expr e>`, Context _) = (Type)`$$TYPE_ERROR$$`;
