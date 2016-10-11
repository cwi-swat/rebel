module testlang::Syntax

extend lang::CommonSyntax;

extend lang::std::Layout;
extend lang::std::Id;
extend lang::std::Comment;

start syntax TestModule = testModule: ModuleDef modDef Import* imports TestDef* testDefs;

syntax TestDef 
  = setup: StateSetup setup;
  
syntax StateSetup = "state" VarName name "{" SetupStatement* body "}";

syntax SetupStatement 
  = nowSetup:     "now" "is" DateTime now ";"
  | entitySetup:  Int? nr StateRef? state TypeName entity FieldValueDeclarations? values ";"  
  ;
 
syntax StateRef
  = VarName state
  | "uninitialized"
  ; 
  
syntax FieldValueDeclarations
  = single: SingleInstanceFieldValueDeclaration singleInstance
  | multiple: MultipleInstanceFieldValueDeclaration+ multipleInstances
  ;

syntax SingleInstanceFieldValueDeclaration = "with" {FieldValueDeclaration DeclSeperator}+ decls;

syntax MultipleInstanceFieldValueDeclaration = "-" "one" "with" {FieldValueDeclaration DeclSeperator}+ decls;

syntax FieldValueDeclaration = VarName field Expr val;

syntax Expr
  = Literal l
  ;

lexical DeclSeperator = "," | "and";

keyword Keywords = "state" | "and" | "with" | "one" | "uninitialized";