@license{
  Copyright (c) 2009-2015 CWI
  All rights reserved. This program and the accompanying materials
  are made available under the terms of the Eclipse Public License v1.0
  which accompanies this distribution, and is available at
  http://www.eclipse.org/legal/epl-v10.html
}
@doc{
	Synopsis: Parse the response that a SMT solver returns
}
@contributor{Jouke Stoel - stoel@cwi.nl (CWI)}

module lang::smtlib25::response::Parser

import lang::smtlib25::response::Syntax;

import ParseTree;
import IO;

Response parseResponse(str response) = parse(#start[Response], response).top;
Response parseResponse(loc file) = parse(#start[Response], file).top;	 