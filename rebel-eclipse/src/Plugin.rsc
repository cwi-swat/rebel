module Plugin

import lang::Syntax;
import lang::Parser;
import lang::Importer;
import lang::Resolver;
import Checker;

//import execution::simulation::Simulation;
//import execution::modelchecker::ModelChecker;
//import execution::testrunner::profile::ProfileTestRunner;
//import execution::DataTypes;
//
//import execution::documentation::documentgenerator::DocumentGenerator;

//import vis::StateEventGraph;

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

//import execution::documentation::DescriptionFileReader;
//import execution::documentation::IDEDocAnnotator;

anno rel[loc, loc] Tree@hyperlinks; 

void main() {
	REBEL_LANGUAGE = "Rebel Language";

	registerLanguage(REBEL_LANGUAGE,"ebl", parseModule);
	
	contribs = {
		annotator(Module (Module m) {
			set[Module] imports = loadImports(m);
			Refs refs = resolve(m + imports);
      		msgs = check(m, imports, refs);

	      	return m[@messages=msgs][@hyperlinks=getAllHyperlinks(m@\loc, refs)];
    	}),
		popup(
			menu("Rebel actions", [
				group("Simulation", [
					action("Start simulation", (Module current, loc file) {
						println("Starting simulation");
						if (/Specification s := current) {
							startSimulation(file.top, noOpTestRunner);
						} else {
							alert("Only specifications can be simulated");
						}
					}),
					action("Start simulation with Profile Test Runner", (Module current, loc file) {
						if (/Specification s := current) {
							println("Starting simulation");
							startSimulation(file.top, profileTestRunner);
						} else {
							alert("Only specifications can be simulated");
						}
					})
				]),

				group("Model checking", [
					action("Run (bounded) model checker", (Module current, loc file) {
						if (/Specification s := current) {
							int k = 100;//toInt(prompt("What should be the maximum search depth?"));						
							checkAndSimulate(file.top, k);
						} else {
							alert("Only can start simulations of Specifications");
						}
				
					})
				]),
				group("Visualization", [
					action("Visualize States and Events", (Module current, loc file) {
						if (/Specification s := current) {
							m = implodeModule(current);
							imports = loadImports(m);
							refs = resolve(m + imports);
							
							visualizeStateEventGraph(m, imports, refs);
						} else {
							alert("Only can visualize state and events of Specification");
						}
					})
				]),
				menu("Documentation options", [
					action("Generate doc (in English)", (Module current, loc file) {
						if (/Specification s := current) {
							generatePDF(file.top, "en");	
						}
					}),
					action("Generate doc (in Dutch)", (Module current, loc file) {
						if (/Specification s := current) {
							generatePDF(file.top, "nl");
						}
					})
				])
			])
		)		
	};
	registerContributions(REBEL_LANGUAGE, contribs);
}

void reset(){
	clearLanguages();
	main();
}

private Ref getAllHyperlinks(loc currentUnit, Refs allRefs) =
	getHyperlinks(currentUnit, 
		allRefs.imports + 
		allRefs.eventRefs + 
		allRefs.functionRefs + 
		allRefs.invariantRefs + 
		allRefs.lifeCycleRefs + 
		allRefs.stateRefs +
		allRefs.keywordRefs +
		allRefs.inheritance + 
		allRefs.specRefs); 

private Ref getHyperlinks(loc currentUnit, Ref refs) =
	{<from, to> | <from, to> <- refs, currentUnit.top == from.top};
