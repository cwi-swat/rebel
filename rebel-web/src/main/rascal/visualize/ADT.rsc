@license{
Copyright (c) 2016, CWI
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
@contributor{Jouke Stoel - jouke.stoel@cwi.nl - CWI}
module visualize::ADT

data JsStatement
	= codeOnly(str code)
	| docAndCode(str doc, str code)
	;

data JsParam 
	= typeOnly(str name, str tipe)
	| withValue(str name, str tipe, str val)
	;

data JsState 
	= initialState(str name)
	| finalState(str name)
	| state(str name)
	;
	
data JsReferenceType
	= incoming()
	| outgoing()
	| both()
	;	
	
data JsExternalMachine = externalMachine(str fqn, str name, JsReferenceType referenceType);
data JsTransition 
	= trans(str from, str to, str via)
	| transToExternal(str from, str toMachine)
	| transToExternal(str from, str toMachine, str toEvent)
	| transFromExternal(str fromMachine, str fromEvent, str to)
	;
	
data JsEvent = event(str id, str name, str doc, list[JsParam] config, list[JsParam] params, list[JsStatement] preconditions, list[JsStatement] postconditions, list[JsStatement] sync);
data JsField = field(str name, str tipe);
data JsInheritance
	= extends(str name, str fqn)
	| none()
	;
	
data JsSpecModifier
	= noMod()
	| abstract()
	| external()
	;
	
data JsSpec = spec(str fqn, str name, str doc, JsSpecModifier modifier, JsInheritance inheritsFrom, 
	set[JsInheritance] extendedBy, set[JsField] fields, set[JsEvent] events, set[JsState] states, 
	set[JsTransition] transitions, set[JsExternalMachine] externalMachines, 
	set[JsTransition] transitionsToExternalMachines, set[JsTransition] transitionsFromExternalMachines);    
