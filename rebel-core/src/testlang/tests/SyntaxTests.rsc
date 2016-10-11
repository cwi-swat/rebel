module testlang::tests::SyntaxTests

import testlang::Syntax;
import testlang::Parser;

import IO;

test bool parseFile(loc file) {
  try {
    parseTestModule(file);
    return true;
  } catch ex: {
    println(ex); 
    return false;
  }
}