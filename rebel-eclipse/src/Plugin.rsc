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

import testlang::Syntax;
import testlang::Parser;
import testlang::Loader;
import testlang::Resolver;
import testlang::Interpreter;
import analysis::ModelChecker;
import analysis::CommonAnalysisFunctions; 

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
	str REBEL_LANGUAGE = "Rebel Language";
	str REBEL_TEST_LANGUAGE = "Rebel Test Language";

	registerLanguage(REBEL_LANGUAGE,"ebl", parseModule);
	registerLanguage(REBEL_TEST_LANGUAGE, "tebl", parseTestModule);
	
	registerContributions(REBEL_LANGUAGE, getRebelContribs());
	registerContributions(REBEL_TEST_LANGUAGE, getRebelTestContribs());
}

set[Contribution] getRebelContribs() {
  int startPort = 4300;
  int endPort = 4310;
  map[loc rebelSrcRoot, loc baseUrl] runningVisInstances = ();
  list[int] visualisationPorts = [startPort..endPort];
 
  return {
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
    syntaxProperties(#start[Module]),
    popup(
      menu("Rebel actions", [
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
              htmlDisplay((runningVisInstances[baseDirOfMod] + "vis")[fragment="<current.modDef.fqn>"]);
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
}

set[Contribution] getRebelTestContribs() = 
  {
    annotator(TestModule (TestModule m) {
      tuple[set[Message], TestLoaderResult] result = loadTestModule(m@\loc.top, modulePt = just(m));
      
      TestModule annotatedMod = m[@hyperlinks=getAllTestHyperlinks(m@\loc, result<1>.refs)];
      annotatedMod = annotatedMod[@messages=result<0>];
      
      return annotatedMod;
    }),
    syntaxProperties(#start[TestModule]),
    popup(
      menu("Rebel actions", [
        action("Check", (TestModule current, loc x) {
          if (just(Check ck) := isCheckDefinition(x, current)) {
            tuple[set[Message], TestLoaderResult] tlr = loadTestModule(current@\loc.top, modulePt = just(current));
             
            if (reachable() := interpretCheck(ck, tlr<1>)) {
              alert("Check is satisfiable");
            } else {
              alert("Check is NOT satisfiable within given bounds");
            }
          } else {
            alert("Selected code is not a check");
          } 
        }),
        action("Check and visualize", (TestModule current, loc x) {
          if (just(Check ck) := isCheckDefinition(x, current)) {
            tuple[set[Message], TestLoaderResult] tlr = loadTestModule(current@\loc.top, modulePt = just(current));

            if (reachable(list[State] trace) := interpretCheck(ck, tlr<1>, requireTrace = true)) {
              alert("Check is satisfiable");
              printTrace(trace);
            } else {
              alert("Check is NOT satisfiable within given bounds");
            }
          } else {
            alert("Selected code is not a check");
          } 
        })
      ])
    )
  };
  
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

private Reff getAllTestHyperlinks(loc currentTestModule, TestRefs refs) =
  getHyperlinks(currentTestModule, refs.imports + refs.specs + refs.states + refs.fields + refs.setupRefs);

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
	
void printTrace(list[State] t) {
  for (State st <- t) {
    println("<st.nr>:
            '  now = <st.now>");

    if (step(str entity, str event, list[Variable] transitionParameters) := st.step) {
      println("  step: <entity>.<event> <for (v <- transitionParameters) {>
              '    var <v.name> (type: <v.tipe>) = <v.val> <}>
              '");
    }
    
    println("<for (i <- st.instances) {>
            '  instance: <i.entityType>, key = <intercalate(",", i.id)> <for (v <- i.vals) {>
            '    var <v.name> (type: <v.tipe>) = <((uninitialized(_,_) !:= v) ? v.val : "uninitialized")> <}>  
            '<}>
            '");
  }
}

void printState(State st) {
  println("<st.nr>:
          'now = <st.now>
          '<for (i <- st.instances) {>
          'instance: <i.entityType>, key = <intercalate(",", i.id)> <for (v <- i.vals) {>
          '  var <v.name> (type: <v.tipe>) = <v.val> <}>  
          '<}>
          '");  
}	
