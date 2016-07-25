module util::TestUtils

import lang::Syntax;
import lang::Parser;

import ParseTree;

Module parseModule(str modul) = parse(#start[Module], modul).top;

bool eq(value first, value second) {
  if(first == second) 
    return true; 
  else {
    throw "`<first>` was not equal to `<second>`";
  }
}

bool neq(value first, value second) {
  if(first != second) 
    return true; 
  else {
    throw "`<first>` was equal to `<second>`";
  }
}