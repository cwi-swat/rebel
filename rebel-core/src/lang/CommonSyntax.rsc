module lang::CommonSyntax

syntax ModuleDef = "module" FullyQualifiedName fqn;

syntax FullyQualifiedName = ({VarName "."}+ packages ".")? modulePath TypeName modName;

syntax Import = "import" FullyQualifiedName fqn;


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
  | @category="Constant" DateTime
  | @category="Constant" Percentage
  | @category="Constant" String
  | @category="Constant" Money
  | @category="Constant" Currency
  | @category="Constant" IBAN
  ;
  
syntax Literal
  = @category="Constant" anyVal: "ANY"
  ;
  

syntax Date = Int day Month month Int? year;
  
syntax Time = hhmmss: [0-9][0-9]? hour ":" [0-9][0-9]? minutes (":" [0-9][0-9]? seconds)?;

syntax DateTime 
  = Date date "," Time time
  | "now"
  ;
  
syntax Term = Int factor Period period;

syntax Money = Currency cur MoneyAmount amount;

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

keyword Keywords = "Jan" | "Feb" | "Mar" | "Apr" | "May" | "Jun" | "Jul" | "Aug" | "Sep" | "Oct" | "Nov" | "Dec" ; 
keyword Keywords = "Daily" | "Monthly" | "Quarterly" | "Yearly" | "Day" | "Month" | "Quarter" | "Year" | "True" | "False"; 
keyword Keywords = "Date" | "Integer" | "Period" | "Frequency" | "Percentage" | "Boolean" | "String" | "Time" | "Money" | "Currency" | "Term" | "IBAN";
keyword Keywords = "EUR" | "USD" | "CUR";