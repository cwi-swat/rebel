@license{
Copyright (c) 2016, CWI
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
@contributor{Jouke Stoel - jouke.stoel@cwi.nl - CWI}
module Plugin

import lang::Syntax;
import lang::Builder;
import lang::Resolver;
import lang::Parser;
import Checker;

import visualize::VisualisationServer;

import util::IDE;
import util::Prompt;
import ParseTree;
import vis::ParseTree;
import IO;
import Set;

import Node;
import String;
import DateTime;

import util::Benchmark;
import util::Maybe;
import util::HtmlDisplay;


anno rel[loc, loc] Tree@hyperlinks; 

void main() {
  int startPort = 4300;
  int endPort = 4310;
  map[loc rebelSrcRoot, loc baseUrl] runningVisInstances = ();
  list[int] visualisationPorts = [startPort..endPort];

	REBEL_LANGUAGE = "Rebel Language";

	registerLanguage(REBEL_LANGUAGE,"ebl", parseModule);
	
	contribs = {
		annotator(Module (Module m) {
		  <msgs, builtResult> = load(m@\loc.top, modulPt = just(m), log = println);
		  // TEMP TEMP TEMP, print all error messages to the console because not all errors are visible in the editor
		  iprintln(msgs);
		  
		  Module annotatedMod = m[@messages=msgs];
		  if (just(Built built) := builtResult) {
		    annotatedMod = annotatedMod[@hyperlinks=getAllHyperlinks(m@\loc, built.refs)];
		  }
		  
	    return annotatedMod;
    }),
		popup(
			menu("Rebel actions", [
				action("Simulate", (Module current, loc file) {
					if (/Specification s := current) {
						startSimulation(file.top, noOpTestRunner);
					} else {
						alert("Only specifications can be simulated");
					}
				}),

				action("Run (bounded) model checker", (Module current, loc file) {
					if (/Specification s := current) {
						int k = 100;//toInt(prompt("What should be the maximum search depth?"));						
						checkAndSimulate(file.top, k);
					} else {
						alert("Only can start simulations of Specifications");
					}
				
				}),
				action("Visualize", (Module current, loc file) {
					if (/Specification s := current) {
            loc baseDirOfMod = resolveBaseDir(current);
            
            if (baseDirOfMod notin runningVisInstances) {
              int port = startPort;
              
              while (baseDirOfMod notin runningVisInstances && port < endPort) {
                try {
                  loc servingBase = |http://localhost|[port=port];
                  serve(baseDirOfMod, config = appConfig(baseUrl = servingBase));
                  runningVisInstances[baseDirOfMod] = servingBase;
                  
                } catch ex: port += 1;
              }
            }
            
            if (baseDirOfMod in runningVisInstances) {          
              htmlDisplay(runningVisInstances[baseDirOfMod][fragment="<current.modDef.fqn>"]);
            } else {
              alert("Unable to start visualisation server, no port available");
            }            
					} else {
						alert("Only can visualize Specifications");
					}
				})
			])
		)		
	};
	registerContributions(REBEL_LANGUAGE, contribs);
}

loc resolveBaseDir(Module m) {
  loc base = m@\loc.top.parent;
  
  for (package <- reverse(["<p>" | /VarName p := m.modDef.fqn]), endsWith(base.path, "<package>")) {
    base = base.parent;
  }
  
  return base;
}


void reset(){
	clearLanguages();
	main();
}

private Reff getAllHyperlinks(loc currentUnit, Refs allRefs) =
	getHyperlinks(currentUnit, 
		allRefs.imports + 
		allRefs.eventRefs + 
		allRefs.functionRefs + 
		allRefs.invariantRefs + 
		allRefs.lifeCycleRefs + 
		allRefs.stateRefs +
		allRefs.keywordRefs +
		allRefs.inheritance +
		allRefs.syncedEventRefs +
		allRefs.specRefs); 

private Reff getHyperlinks(loc currentUnit, Reff refs) =
	{<from, to> | <from, to> <- refs, currentUnit.top == from.top};
