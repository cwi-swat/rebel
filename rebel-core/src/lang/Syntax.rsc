@license{
Copyright (c) 2016, CWI
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
@contributor{Jouke Stoel - jouke.stoel@cwi.nl - CWI}
module lang::Syntax

extend lang::std::Layout;
extend lang::std::Comment;
extend lang::std::Id;

start syntax Module
	= ModuleDef modDef Import* imports Specification spec
	| ModuleDef modDef Import* imports LibraryModule* decls
	;
	
syntax ModuleDef = "module" FullyQualifiedName fqn;

syntax FullyQualifiedName = ({VarName "."}+ packages ".")? modulePath TypeName modName;

syntax FullyQualifiedVarName = (FullyQualifiedName fqn ".")? VarName name;

syntax Import = "import" FullyQualifiedName fqn;

syntax LibraryModule
	= @Foldable EventDef eventDef
	| @Foldable FunctionDef functionDef 
	| @Foldable InvariantDef invariantDef 
	; 
 
// Library rules

syntax EventDef = Annotations annos "event" FullyQualifiedVarName name EventConfigBlock? configParams "(" {Parameter ","}* transitionParams")" "{" Preconditions? pre Postconditions? post SyncBlock? sync "}";

syntax EventConfigBlock = "[" {Parameter ","}+ params "]";

syntax Preconditions = "preconditions" "{" Statement* stats"}";

syntax Postconditions = "postconditions" "{" Statement* stats "}";

syntax SyncBlock = "sync" "{" Statement* stats "}";

syntax FunctionDef = Annotations annos "function" FullyQualifiedVarName name "(" {Parameter ","}* params ")" ":" Type returnType "=" Statement statement;

syntax InvariantDef = Annotations annos "invariant" FullyQualifiedVarName name "{" Statement* stats "}";

// Specification rules

syntax Specification = Annotations annos SpecModifier? modifier "specification" TypeName name Extend? extend "{" Fields? fields EventRefs? events InvariantRefs? invariants LifeCycle? lifeCycle "}";

syntax Extend = "extends" FullyQualifiedName parent;

syntax Fields =  @Foldable "fields" "{" FieldDecl* fields "}";

syntax EventRefs =  @Foldable eventInstances: "events" "{" EventRef* events "}";

syntax EventRef = FullyQualifiedVarName eventRef "[" {ConfigParameter ","}* config "]";

syntax InvariantRefs =  @Foldable "invariants" "{" FullyQualifiedVarName* invariants "}";

syntax LifeCycle = "lifeCycle" "{" StateFrom* from "}";

syntax StateFrom = LifeCycleModifier? mod VarName from StateTo* destinations; 

syntax StateTo = "-\>" VarName to ":" StateVia via;

syntax StateVia = {VarName ","}+ refs;
	
// Generic rules
syntax ConfigParameter = VarName name "=" Expr val; 

syntax Parameter = VarName name ":" Type tipe DefaultValue? defaultValue;
syntax DefaultValue = "=" Expr val;

syntax Statement  
	= bracket "(" Statement ")"
  	| "case" Expr "{" Case+ cases "}" ";"
  	| Annotations annos Expr ";"
  	;  
  	
syntax Case = Literal lit "=\>" Statement stat;

syntax Expr
  	= bracket "(" Expr ")"
	| literal: Literal!reference lit 
  	| reference: Ref ref
    | VarName function "(" {Expr ","}* exprs ")"
    | left property: Expr lhs "." Expr field 
    | "{" Expr lower ".." Expr upper"}"
	| left Expr var!accessor "[" Expr indx "]"
  	| "(" {MapElement ","}* mapElems ")"
  	| staticSet: "{" {Expr ","}* setElems "}"
  	| "{" Expr elem "|" Expr loopVar "\<-" Expr set "}"
  	| "{" Expr init "|" Statement reducer "|" Expr loopVar "\<-" Expr set "}" 
	> new: "new" Expr expr
  	| "not" Expr expr
  	| "-" Expr
  	> left	( Expr lhs "*" Expr rhs
		    | isMember: Expr lhs "in" Expr rhs
		    | Expr lhs "/" Expr rhs
		    | Expr lhs "%" Expr rhs
		  	)
  	> left 	( Expr lhs "+" Expr rhs
    		| subtract: Expr lhs "-" Expr rhs
    		)
	> non-assoc	( smallerThan: Expr lhs "\<" Expr rhs
				| smallerThanEquals: Expr lhs "\<=" Expr rhs
				| greaterThan: Expr lhs "\>" Expr rhs
				| greaterThanEquals: Expr lhs "\>=" Expr rhs
				| equals: Expr lhs "==" Expr rhs
				| notEqual: Expr lhs "!=" Expr rhs
				)
 	> left and: Expr lhs "&&" Expr rhs
  	> left Expr lhs "||" Expr rhs
	> right ( Expr cond "?" Expr whenTrue ":" Expr whenFalse
			| Expr cond "-\>" Expr implication
			)
	| "initialized" Expr
	| "finalized" Expr
	| Expr lhs "instate" Expr rhs
  	;
 
syntax MapElement =  Expr key ":" Expr val;
 
syntax FieldDecl 
	= VarName name ":" Type tipe Annotations meta
	;	
	  
syntax Ref 
	= FullyQualifiedVarName field
	| FullyQualifiedName tipe
	| this: "this"
	| "it"
	; 
	
syntax Type 
	= @category="Type" "Boolean"
  	| @category="Type" "Period"
  	| @category="Type" "Integer"
  	| @category="Type" "Money"
  	| @category="Type" "Currency"
  	| @category="Type" "Date"
  	| @category="Type" "Frequency"
  	| @category="Type" "Percentage"
  	| @category="Type" "Period"
  	| @category="Type" "Term"
  	| @category="Type" "String"
  	| @category="Type" "map" "[" Type ":" Type "]"
  	| @category="Type" "set" "[" Type "]"
  	| @category="Type" Term
  	| @category="Type" "Time"
  	| @category="Type" "IBAN"
  	| @category="Type" Type "-\>" Type
  	| bracket @category="Type" "(" {Type ","}+ ")" 
  	| @category="Type"  TypeName custom
  	;
  	
syntax Literal
 	= @category="Constant" Int
  	| @category="Constant" Bool
  	| @category="Constant" Period
  	| @category="Constant" Frequency
  	| @category="Constant" Term term
  	| @category="Constant" Date
  	| @category="Constant" Time
  	| @category="Constant" Percentage
  	| @category="Constant" String
  	| @category="Constant" Money
  	| @category="Constant" Currency
  	| @category="Constant" IBAN
  	;

syntax Date = Int day Month month Int? year;
	
lexical Time
	= now: "now"
	| epoch: "t" Int millsSince1970
	;
	
syntax Annotations = Annotation* annos;	

syntax Annotation 
	= @category="Comment" "@" VarName name
	| @Foldable @category="Comment" "@" VarName name TagString tagString
	;

lexical TagString
	= "\\" !<< "{" ( ![{}] | ("\\" [{}]) | TagString)* contents "\\" !<< "}";
	
syntax Term = Int factor Period period;

syntax Money = Currency cur MoneyAmount amount;

lexical SpecModifier 
	= "abstract"
	| "external"
	; 

lexical LifeCycleModifier = "initial" | "final";

lexical Currency 
	= "EUR" | "USD" 
	| "CUR" '_' ([A-Z][A-Z][A-Z]) name
	;

lexical IBAN = iban: [A-Z] !<< ([A-Z][A-Z]) countryCode ([0-9][0-9]) checksum [0-9 A-Z]+ accountNumber !>> [0-9 A-Z];

lexical TypeName = ([A-Z] !<< [A-Z][a-z 0-9 _][a-z A-Z 0-9 _]* !>> [a-z A-Z 0-9 _]) \Keywords; 
lexical VarName = ([a-z] !<< [a-z][a-z A-Z 0-9 _]* !>> [a-z A-Z 0-9 _]) \Keywords;

lexical Month = "Jan" | "Feb" | "Mar" | "Apr" | "May" | "Jun" | "Jul" | "Aug" | "Sep" | "Oct" | "Nov" | "Dec";
lexical Frequency =  "Daily" | "Weekly" | "Monthly" | "Quarterly" | "Yearly";
lexical Period =  "Day" | "Week" | "Month" | "Quarter" | "Year";
lexical Bool =  "True" | "False";
lexical Percentage = [0-9]+ "%";
lexical Int = [0-9]+ | "Inf";
lexical String = "\"" ![\"]*  "\"";
lexical MoneyAmount = [0-9]+ whole [.] ([0-9][0-9][0-9]?) decimals; 

keyword Keywords = "Jan" | "Feb" | "Mar" | "Apr" | "May" | "Jun" | "Jul" | "Aug" | "Sep" | "Oct" | "Nov" | "Dec" ; 
keyword Keywords = "Date" | "Integer" | "Period" | "Frequency" | "Percentage" | "Boolean" | "String" | "Time" | "Money" | "Currency" | "Term" | "IBAN";
keyword Keywords = "this" | "now" | "new" | "exists" | "finalized";
keyword Keywords = "EUR" | "USD" | "CUR";

keyword Keywords = "Daily" | "Monthly" | "Quarterly" | "Yearly" | "Day" | "Month" | "Quarter" | "Year" | "True" | "False" | 
					"case" | "Inf" | "preconditions" | "postconditions" | 
					"all" | "no" | "some" | "lone" | "one" | "initial" | "final" | 
					"it" | "in" | "mod" | "not" ; 
