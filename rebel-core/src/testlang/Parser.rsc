module testlang::Parser

import testlang::Syntax;

import ParseTree;
import IO;

TestModule parseTestModule(loc file)        = parse(#start[TestModule], file).top;
TestModule parseTestModule(str x)           = parse(#start[TestModule], x).top;
TestModule parseTestModule(str x, loc file) = parse(#start[TestModule], x, file).top;
