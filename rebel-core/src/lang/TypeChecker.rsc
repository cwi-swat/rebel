module lang::TypeChecker

extend lang::Syntax;

syntax Type 
	= "$$INVALID$$"
	;
	
Type typeOf((Literal)`<Int _>`) 		= (Type)`Integer`;
Type typeOf((Literal)`<Bool _>`) 		= (Type)`Boolean`;
Type typeOf((Literal)`<String _>`) 		= (Type)`String`;
Type typeOf((Literal)`<Percentage _>`)	= (Type)`Percentage`;
Type typeOf((Literal)`<Date _>`)		= (Type)`Date`;
Type typeOf((Literal)`<Time _>`) 		= (Type)`Time`;
Type typeOf((Literal)`<Period _>`) 		= (Type)`Period`;
Type typeOf((Literal)`<Frequency _>`) 	= (Type)`Frequency`;
Type typeOf((Literal)`<Money _>`) 		= (Type)`Money`;
Type typeOf((Literal)`<Currency _>`) 	= (Type)`Currency`;
Type typeOf((Literal)`<Term _>`) 		= (Type)`Term`;
Type typeOf((Literal)`<IBAN _>`)	 	= (Type)`IBAN`;
