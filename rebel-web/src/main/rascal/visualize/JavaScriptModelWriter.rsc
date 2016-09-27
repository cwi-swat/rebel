@license{
Copyright (c) 2016, CWI
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
@contributor{Jouke Stoel - jouke.stoel@cwi.nl - CWI}
module visualize::JavaScriptModelWriter

import visualize::ADT;

import List;
import visualize::JsonUtil;

import IO;

str asJsStringVar(set[JsSpec] specs) =
	"<("" | "<it><line> \n" | /<line:.*>[\n]/ := toJson(specs))>";

str toJson(set[JsSpec] specs) =
	"[
	'	<intercalate(",\n", [toJson(sp) | sp <- specs])>
	'];
	";	

str toJson(JsSpec sp) = 
	"{
	'	\"fqn\":\"<jsonEsc(sp.fqn)>\", 
	'	\"name\":\"<jsonEsc(splitter(sp.name))>\",
	'	\"documentation\":\"<jsonEsc(sp.doc)>\",
	'	\"modifier\":\"<toJson(sp.modifier)>\",
	'	\"inheritsFrom\": <toJson(sp.inheritsFrom)>,
	'	\"extendedBy\":[<intercalate(",\n", [toJson(ex) | ex <- sp.extendedBy])>],
	'	\"fields\":[<intercalate(",\n", [toJson(field) | JsField field <- sp.fields])>],
	'	\"events\":[<intercalate(",\n", [toJson(evnt) | evnt <- sp.events])>],
	'	\"states\":[<intercalate(",\n", [toJson(s) | s <- sp.states])>],
	'	\"transitions\":[<intercalate(",\n", [toJson(t) | t <- sp.transitions])>],
	'	\"externalMachines\":[<intercalate(",\n", [toJson(m) | m <- sp.externalMachines])>],
	'	\"transitionsToExternalMachines\":[<intercalate(",\n", [toJson(t) | t <- sp.transitionsToExternalMachines])>],
	'	\"transitionsFromExternalMachines\":[<intercalate(",\n", [toJson(t) | t <- sp.transitionsFromExternalMachines])>]
	'}";

str toJson(extends(str name, str fqn)) = "{\"name\":\"<jsonEsc(name)>\", \"url\":\"<jsonEsc(fqn)>\"}";
default str toJson(none()) = "{}";

str toJson(abstract()) = "abstract";
str toJson(external()) = "external";
default str toJson(noMod()) = "";

str toJson(JsField field) = "{\"name\":\"<jsonEsc(field.name)>\", \"type\":\"<jsonEsc(field.tipe)>\"}";

str toJson(JsEvent evnt) = "{
	'	\"id\": \"event_<jsonEsc(evnt.id)>\",
	'	\"label\": \"<jsonEsc(evnt.name)>\",
	'	\"doc\": \"<jsonEsc(evnt.doc)>\",
	'	\"config\": [<intercalate(",", [toJson(c) | c <- evnt.config])>],
	' 	\"params\": [<intercalate(",", [toJson(p) | p <- evnt.params])>],
	' 	\"preconditions\": [<intercalate(",", [toJson(p) | p <- evnt.preconditions])>],
	' 	\"postconditions\": [<intercalate(",", [toJson(p) | p <- evnt.postconditions])>],
	' 	\"sync\": [<intercalate(",", [toJson(s) | s <- evnt.sync])>]
	}";
	
str toJson(jsCodeOnly(str code)) = "{\"code\":\"<jsonEsc(code)>\"}";
str toJson(jsDocAndCode(str doc, str code)) = "{\"doc\":\"<jsonEsc(doc)>\", \"code\":\"<jsonEsc(code)>\"}";

str toJson(JsExternalMachine em) = "{\"id\":\"externalmachine_<jsonEsc(em.name)>\", \"label\":\"<jsonEsc(splitter(em.name))>\", \"url\":\"<jsonEsc(em.fqn)>\", \"referenceType\":\"<toJson(em.rt)>\"}";

str toJson(jsTrans(str from, str to, str via)) = "{\"from\":\"state_<jsonEsc(from)>\", \"to\":\"state_<jsonEsc(to)>\", \"via\":\"event_<jsonEsc(via)>\"}";
str toJson(jsTransToExternal(str from, str toMachine)) = "{\"from\":\"event_<jsonEsc(from)>\", \"to\":\"externalmachine_<jsonEsc(toMachine)>\"}";
str toJson(jsTransToExternal(str from, str toMachine, str toEvent)) = "{\"from\":\"event_<jsonEsc(from)>\", \"to\":\"externalmachine_<jsonEsc(toMachine)>\", \"toEvent\":\"event_<jsonEsc(toEvent)>\"}";
str toJson(jsTransFromExternal(str fromMachine, str fromEvent, str to)) = "{\"fromMachine\":\"externalmachine_<jsonEsc(fromMachine)>\", \"fromEvent\":\"event_<jsonEsc(fromEvent)>\", \"to\":\"event_<jsonEsc(to)>\"}";

str toJson(jsInitialState(str name)) = "{\"id\":\"state_<jsonEsc(name)>\", \"label\": \"\", \"initial\": true}";
str toJson(jsFinalState(str name)) = "{\"id\":\"state_<jsonEsc(name)>\", \"label\":\"\", \"final\": true}";
str toJson(jsState(str name)) = "{\"id\":\"state_<jsonEsc(name)>\", \"label\":\"<jsonEsc(splitter(name))>\"}";

str toJson(typeOnly(str name, str tipe)) = "{\"name\":\"<jsonEsc(name)>\", \"type\":\"<jsonEsc(tipe)>\"}";
str toJson(withValue(str name, str tipe, str val)) = "{\"name\":\"<jsonEsc(name)>\", \"type\":\"<jsonEsc(tipe)>\", \"value\":\"<jsonEsc(val)>\"}";

str toJson(outgoing()) = "out";
str toJson(incoming()) = "in";
str toJson(both()) = "both";


private str splitter(str orig) = orig;
