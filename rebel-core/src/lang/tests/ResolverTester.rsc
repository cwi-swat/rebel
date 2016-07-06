@license{
Copyright (c) 2016, CWI
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
@contributor{Jouke Stoel - jouke.stoel@cwi.nl - CWI}
module lang::tests::ResolverTester

import lang::Syntax;
import lang::Parser;
import lang::Resolver;
import lang::Importer;

Refs testResolveAll(loc file) {
	Module modul = parseModule(file);
	return resolve({modul} + loadImports(modul));
}

Ref testResolveImports(loc file) {
	Module modul = parseModule(file);
	return resolveImports({modul} + loadImports(modul));
}

Ref testResolveEventRefs(loc file) {
	Module modul = parseModule(file);
	return resolveEventReferences({modul} + loadImports(modul));
}

Ref testResolveFunctionRefs(loc file) {
	Module modul = parseModule(file);
	return resolveFunctionReferences({modul} + loadImports(modul));
}

Ref testResolveKeywordRefs(loc file) {
	Module modul = parseModule(file);
	return resolveKeywordReferences({modul} + loadImports(modul));
}

Ref testResolveInvariantRefs(loc file) {
	Module modul = parseModule(file);
	return resolveInvariantReferences({modul} + loadImports(modul));
}

Ref testResolveLifeCycleEventRefs(loc file) {
	Module modul = parseModule(file);
	return resolveLifeCycleEventReferences({modul} + loadImports(modul));
}

Ref testResolveLifeCycleStateRefs(loc file) {
	Module modul = parseModule(file);
	return resolveLifeCycleStateReferences({modul} + loadImports(modul));
}

Ref testResolveInheritance(loc file) {
	Module modul = parseModule(file);
	return resolveInheritance({modul} + loadImports(modul));
}

Ref testResolveSpecRefs(loc file) {
	Module modul = parseModule(file);
	return resolveSpecRefs({modul} + loadImports(modul));
}
