module lang::smtlib25::AST

data Script = script(list[Command] commands);

data Command 
	= setLogic(Logic logic)
	| setOption(Option opt)
	| setInfo(Info inf)
	| getInfo(Info inf)
	| declareSort(str sortName)
	| declareSort(str sortName, int arity)
	| defineSort(str sortName, list[str] sorts, Sort sort)
	| declareConst(str name, Sort sort)
	| declareFunction(str name, list[Sort] paramSorts, Sort returnSort)
	| defineFunction(str name, list[SortedVar] params, Sort returnSort, Formula body)  
	| \assert(Formula term)
	| checkSatisfiable()
	| getValue(list[Formula] terms)
	| getUnsatCore()
	| getModel()
	| eval(Formula term) 
	| echo(str text)
	| push(int nr)
	| pop(int nr)
	| exit()
	| comment(str com)
	; 

data Sort
	= custom(str name)
	| combined(list[Sort] sorts)
	;
	
data SortedVar 
	= sortedVar(str name, Sort sort)
	; 
	
data VarBinding
	= varBinding(str name, Formula term)
	;

data QualifiedId
	= as(str name, Sort sort) 
	| simple(str name)
	;

data Formula
	= var(QualifiedId name)
	| lit(Literal lit)
	| functionCall(QualifiedId name, list[Formula] params)	
	| let(list[VarBinding] binding, Formula term)
	| forall(list[SortedVar] vars, Formula term)
	| exists(list[SortedVar] vars, Formula term)
	| attributed(Formula term, list[Attribute] att)
	;

// AST from theory core
data Sort = \boolean();

data Formula
	= \not(Formula term)
	| implies(Formula lhs, Formula rhs)
	| and(list[Formula] forms)
	| or(list[Formula] forms)
	| xor(list[Formula] forms)
	| equal(Formula lhs, Formula rhs)
	| distinct(list[Formula] forms)
	| ite(Formula condition, Formula \then, Formula \else)
	;  

data Literal = boolVal(bool val);

// End of theory core AST

// AST of theory of int
data Sort = \integer();

data Formula
	= neg(Formula val)
	| sub(Formula lhs, list[Formula] rhss)
	| add(Formula lhs, list[Formula] rhss)
	| mul(Formula lhs, list[Formula] rhss)
	| div(Formula lhs, list[Formula] rhss)
	| \mod(Formula lhs, Formula rhs)
	| abs(Formula term)
	| lte(Formula lhs, Formula rhs)
	| lt(Formula lhs, Formula rhs)
	| gte(Formula lhs, Formula rhs)
	| gt(Formula lhs, Formula rhs)
	;
	
data Literal = intVal(int i);

// End of theory.int data

// data for the theory of Real numbers

data Sort = \real();

data Literal = realVal(real r);

data Formula
	= realDiv(Formula lhs, list[Formula] rhss)
	// others are already defined in the theory of integer numbers
	; 

// End of theory of Real numbers

// data for the theory of String
data Sort = string();

data Literal = strVal(str s);

// data for the theory of FixedSizeBitVectors

data Sort 
	= bitVec(int size)
	;

data Formula = bitVecConst(int intVal, int size);

data Formula
	= bvadd(Formula lhs, Formula rhs)
	| bvsub(Formula lhs, Formula rhs)
	| bvneg(Formula val)
	| bvmul(Formula lhs, Formula rhs)
	| bvurem(Formula lhs, Formula rhs)
	| bvsrem(Formula lhs, Formula rhs)
	| bvsmod(Formula lhs, Formula rhs)
	| bvshl(Formula lhs, Formula rhs)
	| bvlshr(Formula lhs, Formula rhs)
	| bvashr(Formula lhs, Formula rhs)
	;
	
data Formula
	= bvor(Formula lhs, Formula rhs)
	| bvand(Formula lhs, Formula rhs)
	| bvnot(Formula val)
	| bvnand(Formula lhs, Formula rhs)
	| bvnor(Formula lhs, Formula rhs)
	| bvxnor(Formula lhs, Formula rhs)
	;
	
data Formula
	= bvule(Formula lhs, Formula rhs)
	| bvult(Formula lhs, Formula rhs)
	| bvuge(Formula lhs, Formula rhs)
	| bvugt(Formula lhs, Formula rhs)
	| bvsle(Formula lhs, Formula rhs)
	| bvslt(Formula lhs, Formula rhs)
	| bvsge(Formula lhs, Formula rhs)
	| bvsgt(Formula lhs, Formula rhs)
	;

data Literal
	= bvHex(str hVal)
	| bvBin(str bVal)	 
	;
	
// Syntax for the theory of Arrays
data Sort = array(Sort index, Sort elem); 

data Formula
	=  select(Formula arr, Formula idx)
	|  store(Formula arr, Formula idx, Formula val)
	;
// End of Syntax for the theory of Arrays


// Syntax for the theory of Algabraic Data Types
data Command
	= declareDataTypes(list[str] sortNames, list[DataTypeDefinition] definitions)
	;  
	
data DataTypeDefinition 
	= dataTypeDef(str name, list[Constructor] cons);

data Constructor
	= cons(str name)
	| combinedCons(str name, list[SortedVar] vars)
  ;

data Literal
  = adt(str consName, list[Formula] vals)
  ; 

// End of syntax for Algabraic Data Types

data Logic 
	= horn()
	| qfAx()
	| qfIdl()
	| qfUf()
	| qfBv()
	| qfRdl()
	| qfLia()
	| qfUfidl()
	| qfUfbv()
	| qfAbv()
	| qfLra()
	;

data Option
	= custom(str name, str val)
	;

data Info
	= customInfo(str name)
	;

data Attribute
	= named(str val)
	| pattern(list[Formula] terms)
	;