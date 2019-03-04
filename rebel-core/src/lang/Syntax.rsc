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

extend lang::CommonSyntax;
 
start syntax Module
	= ModuleDef modDef Import* imports Specification spec
	| ModuleDef modDef Import* imports LibraryModule* decls
	;

syntax LibraryModule
	= @Foldable EventDef eventDef
	| @Foldable FunctionDef functionDef 
	| @Foldable InvariantDef invariantDef
	;  
  
// Library rules

syntax EventDef = Annotations annos "event" FullyQualifiedVarName name EventConfigBlock? configParams "(" {Parameter ","}* transitionParams")" "{" Preconditions? pre Postconditions? post MaybeSyncBlock sync "}";

syntax MaybeSyncBlock = SyncBlock?;

syntax EventConfigBlock = "[" {Parameter ","}+ params "]"; 

syntax Preconditions = "preconditions" "{" Statement* stats"}";

syntax Postconditions = "postconditions" "{" Statement* stats "}";

syntax SyncBlock = "sync" "{" SyncStatement* stats "}";

syntax FunctionDef = Annotations annos "function" FullyQualifiedVarName name "(" {Parameter ","}* params ")" ":" Type returnType "=" Statement statement;

syntax InvariantDef = Annotations annos "invariant" FullyQualifiedVarName name "{" Statement* stats "}";

// Specification rules

syntax Specification = 
  spec:Annotations annos SpecModifier? modifier "specification" TypeName name Extend? extend "{" Fields? optFields EventRefs? optEventRefs InvariantRefs? optInvariantRefs LifeCycle? optLifeCycle "}";

syntax Extend = "extends" FullyQualifiedName parent;

syntax Fields =  @Foldable "fields" "{" FieldDecl* fields "}";

syntax EventRefs =  @Foldable eventInstances: "events" "{" EventRef* events "}";

syntax EventRef 
  = ref: FullyQualifiedVarName eventRef "[" {ConfigParameter ","}* config "]"
  | interfaceDecl: VarName name "(" Parameter ","* params ")"
  ;

syntax InvariantRefs =  @Foldable "invariants" "{" FullyQualifiedVarName* invariants "}";

syntax LifeCycle = "lifeCycle" "{" StateFrom* from "}";

syntax StateFrom = LifeCycleModifier? mod VarName from StateTo* destinations; 

syntax StateTo = "-\>" VarName to ":" StateVia via;

syntax StateVia = {VarName ","}+ refs;
	
// Generic rules
syntax ConfigParameter = VarName name "=" Expr val;  

syntax Parameter = VarName name ":" Type tipe DefaultValue? defaultValue;
syntax DefaultValue = "=" Expr val;

syntax SyncStatement
  = Annotations doc SyncExpr expr ";" 
  ;
  
syntax SyncExpr
  = not: "not" SyncExpr expr
  | syncEvent: TypeName specName "[" Expr id "]" "." VarName event "(" {Expr ","}* params ")" 
  ;

syntax Statement  
	= bracket "(" Statement ")"
	| "case" Expr "{" Case+ cases "}" ";"
	| Annotations annos Expr expr ";"
	;  
  	
syntax Case = Literal lit "=\>" Statement stat;

//syntax Expr
//	= bracket "(" Expr ")"
//  //| literal: Literal!reference lit 
//	| reference: Ref ref
//  | VarName function "(" {Expr ","}* exprs ")"
//  | left fieldAccess: Expr lhs "." VarName field 
//  | "{" Expr lower ".." Expr upper"}"
//  | Expr var!accessor "[" Expr indx "]"
//	| "(" {MapElement ","}* mapElems ")"
//	| staticSet: "{" {Expr ","}* setElems "}"
//	| comprehension: "{" VarName elemName ":" Expr set "|" {Expr ","}+ conditions "}"
//	| cardanality: "|" Expr set "|"
//	| universalQuantifier: "forall" VarName elemName ":" Expr set "|" {Expr ","}+ conditions
//	| existentialQuantifier: "exists" VarName elemName ":" Expr set "|" {Expr ","}+ conditions
//  > new: "new" Expr expr
//	| "not" Expr expr
//	//| "-" Expr
//  > Expr cond "?" Expr whenTrue ":" Expr whenFalse
//	> left	( Expr lhs "*" Expr rhs
//	    | isMember: Expr lhs "in" Expr rhs
//	    | Expr lhs "/" Expr rhs
//	    | Expr lhs "%" Expr rhs
//	  	)
//	> left 	( Expr lhs "+" Expr rhs
//  		| subtract: Expr lhs "-" Expr rhs
//  		)
//  > non-assoc	( smallerThan: Expr lhs "\<" Expr rhs
//			| smallerThanEquals: Expr lhs "\<=" Expr rhs
//			| greaterThan: Expr lhs "\>" Expr rhs
//			| greaterThanEquals: Expr lhs "\>=" Expr rhs
//			| equals: Expr lhs "==" Expr rhs
//			| notEqual: Expr lhs "!=" Expr rhs
//			)
//  > "initialized" Expr
//  | "finalized" Expr
//  | Expr lhs "instate" StateRef sr
//  > left and: Expr lhs "&&" Expr rhs
//	> left Expr lhs "||" Expr rhs
//	| right Expr cond "-\>" Expr implication
//	;
 
syntax StateRef
  = VarName state
  | "{" VarName+ states "}"
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
	
syntax Annotations = Annotation* annos;	

syntax Annotation 
	= @category="Comment" key: "@" "key"
	| @category="Comment" ref: "@" "ref" "=" FullyQualifiedName spc
	| @Foldable @category="Comment" doc:"@" VarName name TagString tagString
	;

lexical TagString
	= "\\" !<< "{" ( ![{}] | ("\\" [{}]) | TagString)* contents "\\" !<< "}";

lexical SpecModifier 
	= "abstract"
	| "external"
	| "singleton"
	; 

lexical LifeCycleModifier = "initial" | "final";

keyword Keywords = "this" | "now" | "case" | "Inf" | "preconditions" | "postconditions" | 
					         "all" | "no" | "some" | "lone" | "one" | "initial" | "final" | 
					         "it" | "in" | "mod" | "not"; 
