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
