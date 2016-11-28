module testlang::Syntax

extend lang::CommonSyntax;

extend lang::std::Layout;
extend lang::std::Id;
extend lang::std::Comment;

start syntax TestModule = testModule: ModuleDef modDef Import* imports TestDef* testDefs;

syntax TestDef  
  = setup: StateSetup setup
  | check: Check check
  ;
  
syntax StateSetup = "state" VarName name "{" SetupStatement* body "}";

syntax SetupStatement 
  = nowSetup:     "now" "is" DateTime now ";"
  | entitySetup:  Int? nr StateRef? state TypeName entity FieldValueConstraints? constraints ";"  
  ; 
 
syntax StateRef
  = VarName state
  | "uninitialized"
  ; 
  
syntax FieldValueConstraints
  = single: SingleInstanceFieldValueConstraints singleInstance
  | multiple: MultipleInstanceFieldValueConstraints+ multipleInstances
  ;

syntax SingleInstanceFieldValueConstraints = "with" {FieldValueConstraint DeclSeperator}+ decls;

syntax MultipleInstanceFieldValueConstraints = "-" "one" "with" {FieldValueConstraint DeclSeperator}+ decls;

syntax FieldValueConstraint = Expr constraint;

syntax Check = "check" CheckStatement stat;

syntax CheckStatement
  = VarName ref "reachable" StepBounds bounds ";"
  ;

syntax StepBounds
  = max:    "in" "max" Int stepNr Step
  | exact:  "in" "exactly" Int stepNr Step
  | between: "between" Int lower "and" Int upper Step 
  ;

lexical Step = "step" | "steps";

lexical DeclSeperator = "," | "and";

keyword Keywords = "state" | "and" | "with" | "one" | "uninitialized";