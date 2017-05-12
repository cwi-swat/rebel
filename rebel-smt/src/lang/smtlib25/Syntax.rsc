module lang::smtlib25::Syntax

start syntax Script = script: Command* commands; 
 
syntax Command 
	= setLogic: 				"(" "set-logic" Logic logic ")"
	| setOption:				"(" "set-option" Option opt ")"
	| setInfo:					"(" "set-info" Info inf ")"
	| getInfo:					"(" "get-info" Info inf ")"
	| declareSort:				"(" "declare-sort" SortId sortName Int? arity ")"
	| defineSort:				"(" "define-sort" SortId sortName "(" SortId* sorts ")" Sort type ")"
	| declareConst:				"(" "declare-const" Id name Sort sort ")"
	| declareFunction:			"(" "declare-fun" Id name "(" Sort* paramSorts ")" Sort returnSort ")"
	| @Foldable defineFunction:	"(" "define-fun" Id name "(" SortedVar* params ")" Sort returnSort Formula body ")"  
	| @Foldable \assert:		"(" "assert" Formula term ")"
	| checkSatisfiable:			"(" "check-sat" ")"
	| getValue:					"(" "get-value" "(" Formula* terms ")" ")"
	| getUnsatCore:				"(" "get-unsat-core" ")"
	| getModel:					"(" "get-model" ")"
	| eval:						"(" "eval" Formula term ")"
	| echo:						"(" "echo" String text ")"
	| push:						"(" "push" Int nr ")"
	| pop:						"(" "pop" Int nr ")"
	| exit:						"(" "exit" ")"
	; 

syntax Sort
	= @category="Type" custom: 		SortId name
	| @category="Type" combined:	"(" Sort+ sorts ")"
	;
	
syntax SortedVar 
	= sortedVar: "(" Id name Sort sort ")"
	; 
	
syntax VarBinding
	= varBinding: "(" Id name Formula term ")"
	;

syntax QualifiedId
	= as:"(" "as" Id name Sort sort ")"
	| simple: Id name 
	;

syntax Formula
	= var:			QualifiedId name
	| lit:			Literal lit
	| functionCall:	"(" QualifiedId name Formula+ params ")"	
	| let: 			"(" "let" "(" VarBinding+ binding ")" Formula term ")"
	| forall:		"(" "forall" "(" SortedVar+ vars ")" Formula term ")" 
	| exists:		"(" "exists" "(" SortedVar+ vars ")" Formula term ")"
	| attributed:	"(" "!" Formula term Attribute+ att ")"
	;

// Syntax from theory core
syntax Sort = @category="Type" \bool: "Bool";

syntax Formula
	= \not:		"(" "not" Formula term ")"
	| implies:	"(" "=\>" Formula lhs Formula rhs")"
	| and:		"(" "and" Formula+ forms")"
	| or:		"(" "or" Formula+ forms ")"
	| xor:		"(" "xor" Formula+ forms ")"
	| eq:		"(" "=" Formula lhs Formula rhs ")"
	| distinct:	"(" "distinct" Formula+ forms ")"
	| ite:		"(" "ite" Formula condition Formula then Formula else ")"
	;  

syntax Literal = boolVal:	Boolean bool;

// End of theory core syntax

// Syntax of theory of int

syntax Sort = @category="Type" \int:	"Int";

syntax Formula
	= neg:	"(" "-" Formula val ")"
	| sub:	"(" "-" Formula lhs Formula+ rhss ")"
	| add:	"(" "+" Formula lhs Formula+ rhss ")"
	| mul:	"(" "*" Formula lhs Formula+ rhss ")"
	| div:	"(" "div" Formula lhs Formula+ rhss ")"
	| \mod:	"(" "%" Formula lhs Formula rhs ")"
	| abs:	"(" "abs" Formula term ")"
	| lte:	"(" "\<=" Formula lhs Formula rhs ")"
	| lt:	"(" "\<" Formula lhs Formula rhs ")"
	| gte:	"(" "\>=" Formula lhs Formula rhs ")"
	| gt:	"(" "\>" Formula lhs Formula rhs ")"
	;
	
syntax Literal = intVal: Int i;

// End of theory.int syntax

// Syntax for the theory of Real numbers

syntax Sort = @category="Type" \real: "Real";

syntax Literal = realVal: Real r;

syntax Formula
	= realDiv: "(" "/" Formula lhs Formula+ rhss ")"
	// others are already defined in the theory of integer numbers
	; 

// End of theory of Real numbers

// Syntax for the theory of FixedSizeBitVectors

syntax Sort 
	= @category="Type" bitVec: 		"(" "_" "BitVec" Int size ")"
	;

syntax Formula = bitVecConst:	"(" "_" "bv" Int intVal Int size ")";

syntax Formula
	= bvadd:	"(" "bvadd" Formula lhs Formula rhs ")"
	| bvsub:	"(" "bvsub" Formula lhs Formula rhs ")"
	| bvneg:	"(" "bvneg" Formula val ")"
	| bvmul:	"(" "bvmul" Formula lhs Formula rhs ")"
	| bvurem:	"(" "bvurem" Formula lhs Formula rhs ")"
	| bvsrem:	"(" "bvsrem" Formula lhs Formula rhs ")"
	| bvsmod:	"(" "bvsmod" Formula lhs Formula rhs ")"
	| bvshl:	"(" "bvshl" Formula lhs Formula rhs ")"
	| bvlshr:	"(" "bvlshr" Formula lhs Formula rhs ")"
	| bvashr:	"(" "bvashr" Formula lhs Formula rhs ")"
	;
	
syntax Formula
	= bvor:		"(" "bvor" Formula lhs Formula rhs ")"
	| bvand:	"(" "bvand" Formula lhs Formula rhs ")"
	| bvnot:	"(" "bvnot" Formula val ")"
	| bvnand:	"(" "bvnand" Formula lhs Formula rhs ")"
	| bvnor:	"(" "bvnor" Formula lhs Formula rhs ")"
	| bvxnor:	"(" "bvxnor" Formula lhs Formula rhs ")"
	;
	
syntax Formula
	= bvule:	"(" "bvule" Formula lhs Formula rhs ")"
	| bvult:	"(" "bvult" Formula lhs Formula rhs ")"
	| bvuge:	"(" "bvuge" Formula lhs Formula rhs ")"
	| bvugt:	"(" "bvugt" Formula lhs Formula rhs ")"
	| bvsle:	"(" "bvsle" Formula lhs Formula rhs ")"
	| bvslt:	"(" "bvslt" Formula lhs Formula rhs ")"
	| bvsge:	"(" "bvsge" Formula lhs Formula rhs ")"
	| bvsgt:	"(" "bvsgt" Formula lhs Formula rhs ")"
	;

syntax Literal
	= bvHex:	Hex hVal
	| bvBin:	Bin bVal	 
	;
	
// Syntax for the theory of Arrays
syntax Sort
	= @category="Type"  array:	"(" "Array" Sort index Sort elem ")"; 

syntax Formula
	=  select:	"(" "select" Formula arr Formula idx ")"
	|  store:	"(" "store" Formula arr Formula idx Formula val ")"
	;
// End of Syntax for the theory of Arrays


// Syntax for the theory of Algabraic Data Types
syntax Command
	= @Foldable declareDataTypes: "(" "declare-datatypes" "(" SortId* sortNames ")" "(" DataTypeDefinition* definitions ")" ")"
	;  
	
syntax DataTypeDefinition 
	= dataTypeDef: "(" SortId name Constructor+ cons ")";

syntax Constructor
	= cons:			Id name
	| combinedCons:	"(" Id name SortedVar* vars ")"
	;
// End of syntax for Algabraic Data Types

// Syntax for the theory of String
syntax Sort
  = @category="Type" string: "String"
  ;
  
syntax Literal = strVal: String s;
// End of syntax for String

syntax Logic 
	= horn:		"HORN"
	| qfAx:		"QF_AX"
	| qfIdl:	"QF_IDL"
	| qfUf:		"QF_UF"
	| qfBv:		"QF_BV"
	| qfRdl:	"QF_RDL"
	| qfLia:	"QF_LIA"
	| qfUfidl:	"QF_UFIDL"
	| qfUfbv:	"QF_UFBV"
	| qfAbv:	"QF_ABV"
	| qfLra:	"QF_LRA"
	;
	
syntax Option
	= custom: 	":" AttributeValue name AttributeValue val
	;

syntax Info
	= customInfo: 	":" AttributeValue name
	;

syntax Attribute
	= named:					":" "named" AttributeValue val
	| pattern:	":" "pattern" "(" Formula* terms ")"
	;

lexical Int = [0-9] !<< [0-9]+ !>> [0-9];
lexical Real = [0-9] !<< [0-9]+ [.] [0-9]+ !>> [0-9];

lexical Hex = "#" "x" [0-9 a-f]+;
lexical Bin = "#" "b" [0-1]+;
lexical String = "\"" ![\"]* val "\"";

lexical Id = ([a-z A-Z 0-9 _.] !<< [a-z A-Z _][a-z A-Z 0-9 _.]* !>> [a-z A-Z 0-9 _.]) \ Keywords;
lexical SortId = ([a-z A-Z 0-9 _] !<< [A-Z _][a-z A-Z 0-9 _]* !>> [a-z A-Z 0-9 _]) \ Keywords;

lexical Boolean = "true" | "false";

lexical AttributeValue = [a-z A-Z 0-9 _.\-$%|/,?#\[\]] !<< [a-z A-Z 0-9 _.\-$%|:/,?#\[\]]* !>> [a-z A-Z 0-9 _.\-$%|:/,?#\[\]];

layout Standard 
  = WhitespaceOrComment* !>> [\u0009-\u000D \u0020 \u0085 \u00A0 \u1680 \u180E \u2000-\u200A \u2028 \u2029 \u202F \u205F \u3000] !>> ";";
  
lexical WhitespaceOrComment 
  = whitespace: Whitespace
  | comment: Comment
  ; 
  
lexical Comment = @lineComment @category="Comment" ";" ![\n\r]* $;

lexical Whitespace 
  = [\u0009-\u000D \u0020 \u0085 \u00A0 \u1680 \u180E \u2000-\u200A \u2028 \u2029 \u202F \u205F \u3000]
  ; 

keyword Keywords = "Int" | "Bool" | "Array" | "Real" | "BitVec" | "String" | "bv" | "_" | "set-logic" | "set-option" | "set-info" | "declare-sort" |
	"define-sort" | "declare-const" | "declare-fun" | "define-fun" | "check-sat" | "get-value" | "declare-datatypes" | "as" |
	"get-unsat-core" | "get-model" | "push" | "pop" | "exit" | "sat" | "unsat" | "unknown" | "true" | "false" |
	"select" | "store" | "and" | "or" | "not" | "xor" | "abs" | "distinct" | "ite" | "model" | "let" | "as" |
	"bvadd" | "bvsub" | "bvneg" | "bvmul" | "bvurem" | "bvsrem" | "bvsmod" | "bvshl" | "bvlshr" | "bvashr"  |
	"bvor" | "bvand" | "bvnot" | "bvnand" | "bvnor" | "bvxnor" | "div" |
	"bvule" | "bvult" | "bvuge" | "bvugt" | "bvsle" | "bvslt" | "bvsge" | "bvsgt"
	;
