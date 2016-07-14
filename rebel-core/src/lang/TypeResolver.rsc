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
extend lang::Syntax;
syntax Type = "$$INVALID$$";

map[loc, Type] getTypeMapping() {
    map[loc, Type] typeMapping = ();
    // visit nodes bottom-up (breadth-first traversal) and append map with types
    // todo: interesting for IDE typechecking specifications, SMT proof and code generation
    return typeMapping;
}

Type typeOf((Literal)`<Int x>`) = (Type)`Integer`;
Type typeOf((Literal)`<Bool _>`) 		= (Type)`Boolean`;
Type typeOf((Literal)`<String _>`) 		= (Type)`String`;
Type typeOf((Literal)`<Percentage _>`)	= (Type)`Percentage`;
Type typeOf((Literal)`<Date _>`)		= (Type)`Date`;
Type typeOf((Literal)`<Time _>`) 		= (Type)`Time`;
Type typeOf((Literal)`<Period _>`) 		= (Type)`Period`;
Type typeOf((Literal)`<Frequency _>`) 	= (Type)`Frequency`;
Type typeOf((Literal)`<Money _>`) 		= (Type)`Money`;
Type typeOf((Literal)`<Currency _>`) 	= (Type)`Currency`;
Type typeOf((Literal)`<Term _>`) 		= (Type)`Term`;
Type typeOf((Literal)`<IBAN _>`)	 	= (Type)`IBAN`;
