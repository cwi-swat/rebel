module lang::ExtendedSyntax

extend lang::Syntax;

syntax Specification = 
	Annotations annos SpecModifier? modifier "specification" TypeName name Extend? extend "{" Fields fields FunctionDefs functions EventRefs eventRefs EventDefs events InvariantRefs invariantRefs InvariantDefs invariants LifeCycle lifeCycle "}";
	
syntax StateFrom =
	Int nr ":" LifeCycleModifier? mod VarName from StateTo* destinations; 

syntax FunctionDefs = "functionDefs" "{" FunctionDef* defs "}"; 
syntax EventDefs = "eventDefs" "{" EventDef* events "}";
syntax InvariantDefs = "invariantDefs" "{" InvariantDef* defs "}";

lexical VarName = ([_] !<< [_][a-z A-Z 0-9 _]* !>> [a-z A-Z 0-9 _]) \Keywords;

