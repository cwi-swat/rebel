module lang::Parser

import lang::Syntax;

import ParseTree;
import IO;
import util::Maybe;

Module parseModule(loc file) = parse(#start[Module], file, allowAmbiguity=false).top;
Module parseModule(str x, loc file) = parse(#start[Module], x, file).top;

Maybe[Tree] isAmbiguous(Tree script) = just(a)
	when /a:amb(_) := script;
default Maybe[set[Tree]] isAmbiguous(Tree script) = nothing();