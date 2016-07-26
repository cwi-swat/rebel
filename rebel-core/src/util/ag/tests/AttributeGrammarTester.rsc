module util::ag::tests::AttributeGrammarTester

import IO;
import Traversal;
import Node;
import util::Math;
import String;
import List;
import Type;
import ParseTree;

import util::ag::AttributeGrammar;
import util::TestUtils;
import util::ag::ParseTreeVis;

// Syntax
start syntax MyTree = nod: "(" MyTree left "," MyTree right ")"
                    | leaf: Leaf leaf
                    ;

layout MyLayout = [\ \t\n\r]*;
                    
lexical Leaf = [0-9]+;

// Add inherited Attribute
data Tree(str scope = "default");

public MyTree testTree = clean((MyTree)`(1, (2, 3))`);

//public MyTree annotated = t[scope = inheritedHelper("myScope")];
public MyTree annotated = testTree[scope = "myNewScope"]; 

value newScope = "myNewScope";
public MyTree inherited = inherit(annotated);

test bool inheritNotDefaultTest() = neq(inherited.scope, "default");
test bool inheritRootKeptValueTest() = eq(inherited.scope, "myNewScope");
test bool inheritEverywhereTest() = ( true | it && eq(tree.scope, "myNewScope") | MyTree tree := inherited );

test bool inheritShouldOnlyInheritedToChildren() {
  tree = clean((MyTree)`(1, (2, 3))`);
  
  scopeValue = "Only on Subtree";
  
  // only annotated subtree
  annotatedTree = visit(tree) {
    case subtree: (MyTree)`(2, 3)` => subtree[scope=scopeValue]
  }
  result = inherit(annotatedTree);
  
  if(/MyTree subtree:(MyTree)`(2, 3)` := result) {
    //println("matched on subtree <subtree>");
    subtrees = [t | /MyTree t := subtree];
    return (true | it && eq(t.scope, scopeValue) | MyTree t := subtree) &&
           (true | it && neq(t.scope, scopeValue) | /MyTree t := result, t notin subtrees);
  } else {
    throw "could not find subtree (2, 3) in <tree>";
  }
    
  return false;
}

// Add synthesized Attribute
data Tree(str synth = "");

public MyTree singleLeafAnnotated() {
 return visit(testTree) {
    case leaf: (MyTree)`3` => leaf[synth="bottom-up"]
  }
} 

public MyTree allLeafsAnnotated() {
 return visit(testTree) {
    case Leaf leaf => leaf[synth="bottom-up"]
  }
}

public MyTree allLeafsDifferentAnnotated() {
 return visit(testTree) {
    case l:(MyTree)`1` => l[synth="1"]
    case l:(MyTree)`2` => l[synth="2"]
    case l:(MyTree)`3` => l[synth="3"]
  }
}

test bool synthesizeShouldSynthesizeAllNodes() {
  synthesized = synthesize(allLeafsAnnotated(), #str, keywordParamNamesWithDefault = ("synth": "bottom-up"));
  
 visit(synthesized) {
    case t:(MyTree)`1`         => {eq(t.synth, "bottom-up"); t;}
    case t:(MyTree)`2`         => {eq(t.synth, "bottom-up"); t;}
    case t:(MyTree)`3`         => {eq(t.synth, "bottom-up"); t;}
    case t:(MyTree)`(2,3)`     => {eq(t.synth, "bottom-upbottom-up"); t;}
    case t:(MyTree)`(1,(2,3))` => {eq(t.synth, "bottom-upbottom-upbottom-up"); t;}
    case MyTree failsafe       => {throw "tree not exhaustively matched: <failsafe>";}
  }
  
  // if it didnt fail, it is good
  return true;
}

test bool synthesizeShouldCombineCorrectly() {
  synthesized = synthesize(allLeafsDifferentAnnotated(), #str, keywordParamNamesWithDefault = ("synth": "xxx"));
  
  visit(synthesized) {
    case t:(MyTree)`1`         => {eq(t.synth, "1"); t;}
    case t:(MyTree)`2`         => {eq(t.synth, "2"); t;}
    case t:(MyTree)`3`         => {eq(t.synth, "3"); t;}
    case t:(MyTree)`(2,3)`     => {eq(t.synth, "23"); t;}
    case t:(MyTree)`(1,(2,3))` => {eq(t.synth, "123"); t;}
    case MyTree failsafe       => {throw "tree not exhaustively matched: <failsafe>";}
  }
  
  // if it didnt fail, it is good
  return true;
}

test bool synthesizeShouldSynthesizeOnlyNodesUp() {
  synthesized = synthesize(singleLeafAnnotated(), keywordParamNamesWithDefault = ("synth": ""));
  
  list[node] getParents() {
    top-down-break visit(synthesized) {
      case Tree leaf: (MyTree)`3` : return getTraversalContextNodes();
    };
  };
  
  // only parents of the leaf should have the inherited value 
  list[MyTree] parents = [p | MyTree p <- getParents(), bprintln(p), bprintln(getKeywordParameters(p))];
  
  return (true | it && eq(t.synth, "bottom-up") | t <- parents) 
    && (true | it && eq(t.synth, "") | /MyTree t := synthesized, t notin parents);
}

str synth2Compose(Leaf leaf, list[str] fromChildren) = leaf.synth2.attr; 
//str synth2Compose((MyTree)`(<MyTree left>, <MyTree right>)`, list[str] fromChildren) = left.synth2.attr + right.synth2.attr;
str synth2Compose(MyTree tree, list[str] fromChildren) = tree.left.synth2.attr + tree.right.synth2.attr
  when bprintln("try tree is nod (<tree is nod>) on <typeOf(tree)> <tree>"), tree is nod;
default str synth2Compose(_, _) = "default";

Synthesized[Tree, str] synth2Default =
  < "default" // as large as possible, but doesn't scale: solution http://stackoverflow.com/questions/19524735/are-there-constants-for-infinity
  , synth2Compose
  >;

data Tree(Synthesized[Tree, str] synth2 = synth2Default);

test bool synthesizeShouldCombineWithDefaultValues() {
  MyTree tree = visit(testTree) {
    case leaf: (MyTree)`3` => leaf[synth2=synth2Default[attr="explicit"]]
  };
 
  synthesized = synthesize(tree, #str, keywordParamNamesWithDefault = ("synth2": synth2Default));
  
  visit(synthesized) {
    case t:(MyTree)`1`         => {eq(t.synth2.attr, "default"); t;}
    case t:(MyTree)`2`         => {eq(t.synth2.attr, "default"); t;}
    case t:(MyTree)`3`         => {eq(t.synth2.attr, "explicit"); t;}
    case t:(MyTree)`(2,3)`     => {eq(t.synth2.attr, "defaultexplicit"); t;}
    case t:(MyTree)`(1,(2,3))` => {eq(t.synth2.attr, "defaultdefaultexplicit"); t;}
    case MyTree failsafe       => {throw "tree not exhaustively matched: <failsafe>";}
  }
  
  // if it didnt fail, it is good
  return true;
}

test bool synthesizeShouldNotOverrideNonDefaultValues() {
  MyTree tree = visit(testTree) {
    case leaf: (MyTree)`(2,3)` => leaf[synth2="explicitOn(2,3)"]
  };

  synthesized = synthesize(tree, #str, keywordParamNamesWithDefault = ("synth2": "default"));
  
  visit(synthesized) {
    case t:(MyTree)`1`         => {eq(t.synth2, "default"); t;}
    case t:(MyTree)`2`         => {eq(t.synth2, "default"); t;}
    case t:(MyTree)`3`         => {eq(t.synth2, "default"); t;}
    case t:(MyTree)`(2,3)`     => {eq(t.synth2, "explicitOn(2,3)"); t;}
    case t:(MyTree)`(1,(2,3))` => {eq(t.synth2, "defaultexplicitOn(2,3)"); t;}
    case MyTree failsafe       => {throw "tree not exhaustively matched: <failsafe>";}
  }
  
  // if it didnt fail, it is good
  return true;
}


// TODO see if possible to put this method in.
int minCompute(Tree leaf, list[int] fromChildren) = toInt("<leaf>")
  when leaf is Leaf;
int minCompute(Tree tree, list[int] fromChildren) = min(fromChildren)
  when // bprintln("try tree is nod (<tree is nod>) on <typeOf(tree)> <tree>"),
       tree is nod;
       // , bprintln("result <fromChildren> -\> <min(fromChildren)>");
default int minCompute(Tree _, list[int] _) = 1000000;

//int(Tree, list[int]) minComputeFun = minCompute;

Synthesized[Tree, int] minDefault =
  < 1000000 // as large as possible, but doesn't scale: solution http://stackoverflow.com/questions/19524735/are-there-constants-for-infinity
  //, minComputeFun
  , int(Tree t, list[int] fromChildren) {
      //println("input compute: <t>: <fromChildren>");
      switch(t) { // TODO how to get actual leaf value out of this?
        case Leaf leaf          : return toInt("<leaf>");
        case tree: MyTree       : return min(fromChildren);
      }
      return 100; // todo? do we realy want this here?
    }
  >;

data Tree(Synthesized[MyTree, int] min = minDefault);

test bool findMin() {
  MyTree tree = clean((MyTree)`(3, (1, 10))`);

  //Synthesized[MyTree, value] minDefaultValue = minDefault;

  MyTree synthesized = synthesize(tree, #int, keywordParamNamesWithDefault = ("min": minDefault));
  //renderParsetree(synthesized);
  
  //visit(inherited) {
  //  case t:(MyTree)`3`         => {eq(t.min, 1); t;}
  //  case t:(MyTree)`1`         => {eq(t.repMin, 1); t;}
  //  case t:(MyTree)`10`         => {eq(t.repMin, 1); t;}
  //  //case t:(MyTree)`(2,3)`     => {eq(t.synth2, "explicitOn(2,3)"); t;}
  //  //case t:(MyTree)`(1,(2,3))` => {eq(t.synth2, "defaultexplicitOn(2,3)"); t;}
  //  case MyTree failsafe       => {throw "tree not exhaustively matched: <failsafe>";}
  //}
  
  //result = synthesize(inherited);
  
  // if it didnt fail, it is good
  Synthesized[MyTree, int] min = synthesized.min;
  return eq(min.attr, 1);
}


// repMin
Synthesized[Tree, MyTree(int)] repMinDefault =
  < MyTree(int i) { return (MyTree)`1000000`; } // as large as possible, but doesn't scale: solution http://stackoverflow.com/questions/19524735/are-there-constants-for-infinity
  //, minComputeFun
  , MyTree(int)(Tree t, list[MyTree(int)] fromChildren) {
      //println("input compute: <t>: <fromChildren>");
      switch(t) { // TODO how to get actual leaf value out of this?
        case Leaf leaf          : return MyTree(int i) { return parse(#MyTree, "<i>"); }; // TODO: How to write this down nicely
        case (MyTree)`(<MyTree left>, <MyTree right>)`    : return MyTree(int i) {
          //iprintln(fromChildren);
          MyTree leftTree = left.repMin.attr(i); 
          MyTree rightTree = right.repMin.attr(i); 
          return parse(#MyTree, "(<leftTree>, <rightTree>)"); 
        };
        case tree: MyTree       : return fromChildren[0];
      }
      //return 100; // todo? do we realy want this here?
    }
  >;

data Tree(Synthesized[Tree, MyTree(int)] repMin = repMinDefault);

test bool repMinTest() {
  MyTree tree = clean((MyTree)`(3, (1, 10))`);

  // todo totally broken, should be inherited attr?
  MyTree synthesized = synthesize(tree, #int, keywordParamNamesWithDefault = ("min": minDefault));
  synthesized2 = synthesize(synthesized, #MyTree(int), keywordParamNamesWithDefault = ("repMin": repMinDefault));
  
  //printKws(synthesized);
  //renderParsetree(synthesized2);
  
  int min = synthesized.min.attr;
  
  println("found min: <min>");
  
  //println(synthesized);
  //println(synthesized2);
  
  
  MyTree(int) treeBuilder = synthesized2.repMin.attr;
  
  MyTree result = treeBuilder(min);
  //println(result);
  
  return eq(result, (MyTree)`(1, (1, 1))`);
}

//test bool repMinSinglePassTest() {
//  MyTree tree = clean((MyTree)`(3, (1, 10))`);
//
//  // todo totally broken, should be inherited attr?
//  MyTree synthesized = synthesize(tree, #int, keywordParamNamesWithDefault = ("min": minDefault, "repMin": repMinDefault));
//  
//  //printKws(synthesized);
//  //renderParsetree(synthesized2);
//  
//  int min = synthesized.min.attr;
//  
//  println("found min: <min>");
//  
//  println(synthesized);
//  
//  
//  MyTree(int) treeBuilder = synthesized.repMin.attr;
//  
//  MyTree result = treeBuilder(min);
//  println(result);
//  
//  return eq(result, (MyTree)`(1, (1, 1))`);
//}

// TODO real usage case, how would I want to use it?
data Tree(int min2 = 0);

//test
bool agUsage() {
  MyTree tree = clean((MyTree)`(3, (1, 10))`);

  MyTree method(MyTree current, MyTree parent)  {
      //println("input compute: <t>: <fromChildren>");
      switch(current) { 
        case leaf: Leaf         : return leaf.val;
        case tree: MyTree       : return min(tree.left.min2, tree.right.min2);
      }
    };
    
  return false;
}