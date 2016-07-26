@license{
  Copyright (c) 2009-2015 CWI
  All rights reserved. This program and the accompanying materials
  are made available under the terms of the Eclipse Public License v1.0
  which accompanies this distribution, and is available at
  http://www.eclipse.org/legal/epl-v10.html
}
@contributor{Paul Klint - Paul.Klint@cwi.nl - CWI}
module util::ag::ParseTreeVis

// Visualization of ParseTrees

import lang::rascal::format::Grammar;
import lang::rascal::format::Escape;
import vis::Figure;
import vis::Render;
import vis::KeySym;

import ParseTree;
import IO;
import String;
import ValueIO;
import Set;
import Node;

public void renderParsetree(Tree t){
	render(space(visParsetree(t),std(gap(4,15)),std(resizable(true))));
}

public Figure visParsetree(Tree t){
  switch(t){
  
   case b:appl(Production prod, list[Tree] args) : {
        if (skipped() == prod) {
            return box(text("skipped"),size(5),popup(unparse(b)));
        }
   		if(\lex(_) := prod.def){
   			return box(text(unparse(b) + "<getKeywordParameters(b)>"),size(5));
   		}
   		if(prod.def has string){
   			return box(text(prod.def.string),size(5));
   		}
   		if(\layouts(_) := prod.def){
   			return box(text("<getKeywordParameters(b)>"),size(5),fillColor("grey"),popup(unparse(b)));
   		}
	     FProperty p = popup(topProd2rascal(prod));
	     return tree(ellipse(text("<getKeywordParameters(b)>"), size(5), gap(5), lineWidth(2),p),[visParsetree(c) | c <- args], gap(20));
     }
     
     case amb(set[Tree] alternatives):{
         FProperty p = popup("Ambiguous: <size(alternatives)>");
        // viewTrees(root, toList(alternatives));
         return tree(ellipse(size(10), fillColor("red"), p),[visParsetree(c) | c <- alternatives]);
      }
     
    case char(int c) : {
        return  box(text(escape(stringChar(c)), fontColor("blue")));
    }

    case cycle(Symbol symbol, int cycleLength) : {
         FProperty p = popup("Cycle-<cycleLength> of <symbol>");
         return tree(ellipse(size(10), fillColor("yellow"), p), []);
    }
  }
  throw "viewTree1: missing case for: <t>";
}

private FProperty popup(str s){
	return mouseOver(box(text(s), grow(1.2), resizable(false),fillColor("yellow")));
}

private bool allChars(list[Tree] trees){
  return all(char(_) <- trees);
}

private str getChars(list[Tree] trees){
  list[int] chars = [ c | t <- trees, char(int c) := t];
  return stringChars(chars);
}

public FProperty popup(str s){
return mouseOver(box(text(s), grow(1.2), resizable(false), fillColor("yellow")));
}

public void tree2(){
   render(tree(ellipse(size(60), fillColor("green"), popup("Ellipse A")),
       [ ellipse(size(90), fillColor("red"), popup("Ellipse B")),
         ellipse(size(120), fillColor("blue"), popup("Ellipse C")),
         ellipse(size(150), fillColor("purple"), popup("Ellipse D")),
         ellipse(size(180), fillColor("lightblue"), popup("Ellipse E")),
         box(size(60), fillColor("orange"), popup("Box F")),
         box(size(60), fillColor("brown"), popup("Box G")),
         box(size(60), fillColor("black"), popup("Box H")),
         box(size(60), fillColor("grey"), popup("Box I")),
         ellipse(size(60), fillColor("white"), popup("Ellipse J"))
       ],  gap(30),  lineWidth(2), fillColor("black"), std(shadow(true)))); 
}

