module Plugin

import lang::Syntax;
import lang::Parser;

import util::IDE;
import ParseTree;

void main() {
	registerLanguage("Rebel Language","ebl", parseModule);

    registerContributions("Rebel Language", {
        syntaxProperties(#start[Module],
         fences = {<"{","}">,<"(",")">}, 
         lineComment = "//", 
         blockComment = <"/*"," *","*/">)
    });
}