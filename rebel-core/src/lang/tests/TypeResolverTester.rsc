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

import lang::TypeChecker;
import lang::ExtendedSyntax;

import lang::Parser;
import lang::Importer;
import lang::Resolver;
import lang::Normalizer;
 
import ParseTree;
import Map;
import IO;

test bool testResolveType() =
	resolveType([Expr]"100", context(root("",(),()))) == (Type)`Integer` && 
  resolveType([Expr]"True", context(root("",(),()))) == (Type)`Boolean` &&
	resolveType([Expr]"\"some String\"", context(root("",(),()))) == (Type)`String` && 
	resolveType([Expr]"50%", context(root("",(),()))) == (Type)`Percentage` &&
	resolveType([Expr]"1 Apr 2016", context(root("",(),()))) == (Type)`Date` &&
	resolveType([Expr]"now", context(root("",(),()))) == (Type)`DateTime` &&
	resolveType([Expr]"Quarter", context(root("",(),()))) == (Type)`Period` && 
	resolveType([Expr]"Quarterly", context(root("",(),()))) == (Type)`Frequency` && 
	resolveType([Expr]"EUR 100.00", context(root("",(),()))) == (Type)`Money` &&
	resolveType([Expr]"EUR", context(root("",(),()))) == (Type)`Currency` &&
	resolveType([Expr]"2 Month", context(root("",(),()))) == (Type)`Term` &&
	resolveType([Expr]"NL12INGB0001234567", context(root("",(),()))) == (Type)`IBAN` 
	;

bool testResolveSpec(loc file) {
  Module orig = parseModule(file);
  set[Module] imports = loadImports(orig); 
  Refs refs = resolve({orig} + imports);  
  Module inlinedSpec = inline(orig, imports, refs);

  map[loc, Type] resolvedTypes = ();
  map[str, Type] functions = ("<f.name>" : f.returnType | /FunctionDef f := inlinedSpec.spec.functions);
  Scope specScope = root("<inlinedSpec.spec.name>", 
    ("this.<f.name>":f.tipe | /FieldDecl f := inlinedSpec.spec.fields) + 
    ("<spec.name>":[Type]"<spec.name>" | /(Module)`<ModuleDef _> <Import* _> <Specification spec>` := imports) +
    ("this":[Type]"<inlinedSpec.spec.name>") , functions); 


  for (EventDef evnt <- inlinedSpec.spec.events.events) {
    Context ctx = context(buildEventScope(evnt, inlinedSpec.spec.functions, specScope));
    
    visit(evnt) {
      case Expr expr: {
        Type resolvedType = resolveTypeCached(expr, ctx);
        
        if ((Type)`$$INVALID_TYPE$$` := resolvedType) {
          println("Error resolving type for <expr> in <expr@\loc>");
        }
        
        resolvedTypes += (expr@\loc:resolvedType);
      }
    }
  }
 
  return /(Type)`$$INVALID_TYPE$$` !:= range(resolvedTypes);
}

Scope buildEventScope(EventDef evnt, FunctionDefs functions, Scope parent) =
  nested("<evnt.name>",
          ("<p.name>":p.tipe | Parameter p <- evnt.transitionParams),
          parent);