@license{
Copyright (c) 2016, CWI
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
@contributor{Jouke Stoel - jouke.stoel@cwi.nl - CWI}
module lang::tests::TypeResolverTester

import lang::TypeResolver;
import lang::ExtendedSyntax;

import lang::Parser;
import lang::Importer;
import lang::Resolver;
import lang::Normalizer;

import ParseTree;
import Map;
import IO;

test bool testResolveType() =
	resolveType([Literal]"100") == (Type)`Integer` 
	&& resolveType([Literal]"True") == (Type)`Boolean` 
	&& resolveType([Literal]"\"some String\"") == (Type)`String` 
	&& resolveType([Literal]"50%") == (Type)`Percentage` 
	&& resolveType([Literal]"1 Apr 2016") == (Type)`Date` 
	&& resolveType([Literal]"now") == (Type)`Time` 
	&& resolveType([Literal]"Quarter") == (Type)`Period` 
	&& resolveType([Literal]"Quarterly") == (Type)`Frequency` 
	&& resolveType([Literal]"EUR 100.00") == (Type)`Money` 
	&& resolveType([Literal]"EUR") == (Type)`Currency` 
	&& resolveType([Literal]"2 Month") == (Type)`Term` 
	&& resolveType([Literal]"NL12INGB0001234567") == (Type)`IBAN`
	;

test bool testResolveSpec(loc file) {
  Module orig = parseModule(file);
  set[Module] imports = loadImports(orig);
  Refs refs = resolve({orig} + imports);  
  Module inlinedSpec = inline(orig, imports, refs);

  Scope specScope = root("<inlinedSpec.spec.name>", ("this.<f.name>":f.tipe | /FieldDecl f := inlinedSpec.spec.fields) + ("this":[Type]"<inlinedSpec.spec.name>"));

  map[loc, Type] resolvedTypes = (); 

  for (EventDef evnt <- inlinedSpec.spec.events.events) {
    Context ctx = context(buildEventScope(evnt, inlinedSpec.spec.functions, specScope));
    
    visit(evnt) {
      case Expr expr: {
        Type resolvedType = resolveTypeCached(expr, ctx);
        
        if ((Type)`$$TYPE_ERROR$$` := resolvedType) {
          println("Error resolving type for <expr>");
        }
        
        resolvedTypes += (expr@\loc:resolvedType);
      }
    }
  }
 
  return /(Type)`$$TYPE_ERROR$$` !:= range(resolvedTypes);
}

Scope buildEventScope(EventDef evnt, FunctionDefs functions, Scope parent) =
  nested("<evnt.name>",
          ("<p.name>":p.tipe | Parameter p <- evnt.transitionParams),
          ("<f.name>":f.returnType | /(Expr)`<VarName ref>(<{Expr ","}* _>)` := evnt, FunctionDef f <- functions.defs, "<f.name>" == "<ref>"),
          parent);