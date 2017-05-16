module lang::CommonSyntax

extend lang::std::Layout;
extend lang::std::Comment;
extend lang::std::Id; 

syntax ModuleDef = "module" FullyQualifiedName fqn;

syntax FullyQualifiedName = ({VarName "."}+ packages ".")? modulePath TypeName modName;
syntax FullyQualifiedVarName = (FullyQualifiedName fqn ".")? VarName name; 

syntax Import = "import" FullyQualifiedName fqn;

syntax Expr
  = bracket "(" Expr ")"
  > literal: Literal!reference lit 
  | reference: Ref ref
  | VarName function "(" {Expr ","}* exprs ")"
  | left fieldAccess: Expr lhs "." VarName field 
  | "{" Expr lower ".." Expr upper"}"
  | Expr var!accessor "[" Expr indx "]"
  | "(" {MapElement ","}* mapElems ")"
  | staticSet: "{" {Expr ","}* setElems "}"
  | comprehension: "{" VarName elemName ":" Expr set "|" {Expr ","}+ conditions "}"
  | cardanality: "|" Expr set "|"
  | universalQuantifier: "forall" VarName elemName ":" Expr set "|" {Expr ","}+ conditions
  | existentialQuantifier: "exists" VarName elemName ":" Expr set "|" {Expr ","}+ conditions
  > new: "new" Expr expr
  | "not" Expr expr
  | "-" Expr
  > Expr cond "?" Expr whenTrue ":" Expr whenFalse
  > left  ( Expr lhs "*" Expr rhs
      | isMember: Expr lhs "in" Expr rhs
      | Expr lhs "/" Expr rhs
      | Expr lhs "%" Expr rhs
      )
  > left  ( Expr lhs "+" Expr rhs
      | subtract: Expr lhs "-" Expr rhs
      )
  > non-assoc ( smallerThan: Expr lhs "\<" Expr rhs
      | smallerThanEquals: Expr lhs "\<=" Expr rhs
      | greaterThan: Expr lhs "\>" Expr rhs
      | greaterThanEquals: Expr lhs "\>=" Expr rhs
      | equals: Expr lhs "==" Expr rhs
      | notEqual: Expr lhs "!=" Expr rhs
      )
  > "initialized" Expr
  | "finalized" Expr
  | Expr lhs "instate" StateRef sr
  > left and: Expr lhs "&&" Expr rhs
  > left Expr lhs "||" Expr rhs
  | right Expr cond "-\>" Expr implication
  ;

syntax StateRef
  = VarName state
  | "{" VarName+ states "}"
  ; 
 
syntax MapElement =  Expr key ":" Expr val;
     
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
  | @category="Type" "InterestNorm"
  | @category="Type" "InterestTariff"
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
  | @category="Constant" DateTime
  | @category="Constant" Percentage
  | @category="Constant" String
  | @category="Constant" Money
  | @category="Constant" Currency
  | @category="Constant" IBAN
  | @category="Constant" InterestNorm
  | @category="Constant" InterestTariff
  ;
  
syntax Literal
  = @category="Constant" anyVal: "ANY"
  ;
  

syntax Date = Int day Month month Int? year;
  
syntax Time 
  = hhmm: [0-9][0-9]? hour ":" [0-9][0-9]? minutes
  | hhmmss: [0-9][0-9]? hour ":" [0-9][0-9]? minutes ":" [0-9][0-9]? seconds
  ;

syntax DateTime 
  = Date date "," Time time
  | "now"
  ;
  
syntax Term = Int factor Period period;

syntax Money = Currency cur MoneyAmount amount;

syntax InterestTariff 
  = fixed:            "fixed" Percentage p
  | normBased:        "norm" InterestNorm norm 
  | withPosAddition:  InterestTariff base "++" InterestTariff posAddition
  | withNegAddition:  InterestTariff base "--" InterestTariff negAddition
  | withMinMaxTariff: InterestTariff base "bounded by" ("min" "=" InterestTariff min)? ("max" "=" InterestTariff max)? 
  ; 

lexical InterestNorm = "EURIBOR" | "AIRBOR" | "LIBOR" | "INGBASIS" | "LIMITBASED";

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
lexical Percentage = [0-9]+ per "%";
lexical Int = [0-9]+ | "Inf";
lexical String = "\"" ![\"]*  "\"";
lexical MoneyAmount = [0-9]+ whole [.] ([0-9][0-9][0-9]?) decimals; 

keyword Keywords = "this" | "now";
keyword Keywords = "Jan" | "Feb" | "Mar" | "Apr" | "May" | "Jun" | "Jul" | "Aug" | "Sep" | "Oct" | "Nov" | "Dec" ; 
keyword Keywords = "Daily" | "Monthly" | "Quarterly" | "Yearly" | "Day" | "Month" | "Quarter" | "Year" | "True" | "False"; 
keyword Keywords = "Date" | "Integer" | "Period" | "Frequency" | "Percentage" | "Boolean" | "String" | "Time" | "Money" | "Currency" | "Term" | "IBAN" | "InterestTariff" | "InterestNorm" ;
keyword Keywords = "EUR" | "USD" | "CUR";
keyword Keywords = "Daily" | "Monthly" | "Quarterly" | "Yearly" | "Day" | "Month" | "Quarter" | "Year" | "True" | "False"; 
keyword Keywords = "EURIBOR" | "AIRBOR" | "LIBOR" | "INGBASIS";
