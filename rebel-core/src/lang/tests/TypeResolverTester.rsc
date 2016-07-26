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
import lang::Syntax;
import ParseTree;

test bool testResolveType() {
	return resolveType([Literal]"100") == (Type)`Integer` 
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
	
	
}