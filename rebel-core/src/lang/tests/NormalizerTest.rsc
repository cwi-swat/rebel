@license{
Copyright (c) 2016, CWI
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
@contributor{Jouke Stoel - jouke.stoel@cwi.nl - CWI}
module lang::tests::NormalizerTest

import lang::Parser;
import lang::Importer;
import lang::Resolver;
import lang::Flattener;

import lang::Normalizer;
import lang::ExtendedSyntax;

import IO;
import Message;

Module testNormalizeSpec(loc file) { 
  Module spc = parseModule(file);
  ImporterResult importResult = loadImports(spc);
  Refs refs = resolve({spc} + importResult<1>);
  
  FlattenerResult flattenResult = flatten(spc, importResult<1>);
  NormalizeResult result = phase1(flattenResult.flattenedModule, importResult<1>, refs);
  
  for (Message msg <- flattenResult<0> + importResult<0> + result<0>) {
    println(msg);
  }

  return result<1>;
}

Module testNormalizeSpec() = testNormalizeSpec(|project://rebel-core/examples/account/saving/SimpleSavings.ebl|);

Module testInlining(loc file) {
  Module spc = parseModule(file);
  ImporterResult importResult = loadImports(spc);
  Refs refs = resolve({spc} + importResult<1>);
  
  FlattenerResult flattenResult = flatten(spc, importResult<1>);
  NormalizeResult result =  inline(flattenResult.flattenedModule, importResult<1>, refs);
  
  for (Message msg <- flattenResult<0> + importResult<0> + result<0>) {
    println(msg);
  }
  
  return result<1>;
}
