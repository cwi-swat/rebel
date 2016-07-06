module lang::tests::TypeCheckerTester

import lang::TypeChecker;
import lang::Syntax;
import ParseTree;

test bool testTypeOf() {
	return typeOf([Literal]"100") == (Type)`Integer` 
	&& typeOf([Literal]"True") == (Type)`Boolean` 
	&& typeOf([Literal]"\"some Strin\"") == (Type)`String` 
	&& typeOf([Literal]"50%") == (Type)`Percentage` 
	&& typeOf([Literal]"1 Apr 2016") == (Type)`Date` 
	&& typeOf([Literal]"now") == (Type)`Time` 
	&& typeOf([Literal]"Quarter") == (Type)`Period` 
	&& typeOf([Literal]"Quarterly") == (Type)`Frequency` 
	&& typeOf([Literal]"EUR 100.00") == (Type)`Money` 
	&& typeOf([Literal]"EUR") == (Type)`Currency` 
	&& typeOf([Literal]"2 Month") == (Type)`Term` 
	&& typeOf([Literal]"NL12INGB0001234567") == (Type)`IBAN`
	;
}