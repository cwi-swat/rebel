module visualize::ADT

data JsStatement
	= jsCodeOnly(str code)
	| jsDocAndCode(str doc, str code)
	;

data JsParam 
	= typeOnly(str name, str tipe)
	| withValue(str name, str tipe, str val)
	;

data JsState 
	= jsInitialState(str name)
	| jsFinalState(str name)
	| jsState(str name)
	;
	
data JsReferenceType
	= incoming()
	| outgoing()
	| both()
	;	
	
data JsExternalMachine = jsEM(str fqn, str name, JsReferenceType rt);
data JsTransition 
	= jsTrans(str from, str to, str via)
	| jsTransToExternal(str from, str toMachine)
	| jsTransToExternal(str from, str toMachine, str toEvent)
	| jsTransFromExternal(str fromMachine, str fromEvent, str to)
	;
	
data JsEvent = jsEvent(str id, str name, str doc, list[JsParam] config, list[JsParam] params, list[JsStatement] preconditions, list[JsStatement] postconditions, list[JsStatement] sync);
data JsField = jsField(str name, str tipe);
data JsInheritance
	= extends(str name, str fqn)
	| none()
	;
	
data JsSpecModifier
	= noMod()
	| abstract()
	| external()
	;
	
data JsSpec = jsSpec(str fqn, str name, str doc, JsSpecModifier specMod, JsInheritance inheritsFrom, 
	set[JsInheritance] extendedBy, set[JsField] fields, set[JsEvent] events, set[JsState] states, 
	set[JsTransition] transitions, set[JsExternalMachine] externalMachines, 
	set[JsTransition] transitionsToExternal, set[JsTransition] transitionsFromExternal);     
