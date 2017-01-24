@license{
  Copyright (c) 2009-2015 CWI
  All rights reserved. This program and the accompanying materials
  are made available under the terms of the Eclipse Public License v1.0
  which accompanies this distribution, and is available at
  http://www.eclipse.org/legal/epl-v10.html
}
@doc{
	Synopsis: Grammar of the SMTLIBv2 response
}
@contributor{Jouke Stoel - stoel@cwi.nl (CWI)}

module lang::smtlib25::response::Syntax

extend lang::smtlib25::Syntax;

start syntax Response
	= response: CheckSat sat
	| response: GetValue value
	| response: GetUnsatCore unsatCore
	| response: GetModel model
	;
	
syntax CheckSat 
	= sat: "sat"  
	| unsat: "unsat"
	| unknown: "unknown"
	;
	
syntax GetUnsatCore = unsatCore: "(" Labell* labels ")";

syntax GetValue = foundValues:"(" FoundValue* values ")";
syntax FoundValue = foundValue:"(" Formula var Formula val ")";

syntax GetModel = model:"(" "model" Command* interpretedFunctions ")";

lexical Labell = [a-z A-Z 0-9 _.$%|:/,?#\[\]] !<< [a-z A-Z 0-9 _.-$%|:/,?#\[\]]* !>> [a-z A-Z 0-9 _.$%|:/,?#\[\]];