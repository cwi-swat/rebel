module util::ag::AttributeGrammar

import ParseTree;
import IO;
import Traversal;
import Node;
import Map;
import Relation;
import Set;

import util::TestUtils;
import util::MultiMap;

//test
//start syntax MyTree = "(" MyTree left "," MyTree right ")"
//                    | Leaf
//                    ;
//
//layout MyLayout = [\ \t\n\r]*;
//                    
//lexical Leaf = [0-9]+;

// lib code
// to be able to access the kw param feature, you have to remove the loc annotation first (until we remove annotations):
public &T<:Tree clean(&T<:Tree e) = delAnnotationsRec(e); 
 
// Function that will calculate the inherited value for you
//alias Inherited[&T] = &T();

public void printKws(Tree input) {
  top-down visit(input) {
    case Tree x : if(appl(_,_) := x) {rprintln(x); println("<x>: <getKeywordParameters(x)>");  } 
  }
}

public &TREE<:Tree inherit(&TREE<:Tree input) {
  //println("input: <input> kws: <getKeywordParameters(input)>");

  // Helper to mark if node has been handled
  set[Tree] inheritedHandled = {};
  
  // TODO more interesting logic to update existing ones
  map[str,value] getInheritedAttributes(node n) = getKeywordParameters(n); 
  
  &TREE result = input;
  
  solve (result) {
    result = top-down visit(result) {
    case Tree t: {
      list[node] parents = getTraversalContextNodes();
      //println("current: <"<t>">, \n\t searching in : <[ "<p>" | p <- parents[1..]]>");
      if(appl(_, _) := t, // bprintln("found appl"), 
        !(t in inheritedHandled), // bprintln("not yet handled"), 
        Tree parent <- parents[1..], // bprintln("has parent"),
         !isEmpty(getInheritedAttributes(parent)) //, bprintln("has relevent")
         ) {
          map[str,value] kwParams = getInheritedAttributes(parent);
          //println("\tfound inherited: <kwParams>");
 
          &TREE updatedTree = setKeywordParameters(t, kwParams);
          //println("updated: <updatedTree> kws: <getKeywordParameters(updatedTree)>");
          inheritedHandled += updatedTree;
          insert updatedTree;
      } else {
        //if (MyTree t2 := t) {
        //  vs = getKeywordParameters(t);
        //  println("keeping: <t> kws: <vs>");
        //}
        insert t;
      }
    }
  };
  //vs = getKeywordParameters(result);
  //println("solve iter: <result> kws: <vs>");
  }
  
  //println("result: <result> kws: <printKws(result)>");
  //println("result: <result> kws: <getKeywordParameters(result)>");
  return result;
}

public &T() defaultValue(&T t) {
  return &T() {return t;};
}

alias Synthesized[&TREE, &ATTR] =
  tuple[ &ATTR attr // (Function that will calculate) the synthesized value for you
       , &ATTR(&TREE input, list[&ATTR] fromChildren) compute // Function dat will calculate the attribute value given the node
       ];

/**
  `synthesize` takes a `Tree` and bubbles all the keyword parameters up to the root using a combine function
**/
public &TREE<:Tree synthesize(&TREE<:Tree input, type[&ATTR] typeHelper, map[str, Synthesized[Tree, &ATTR]] keywordParamNamesWithDefault = () ) {

  // skip all layout nodes
  list[Tree] childrenOf(appl(_, list[Tree] args)) = args[0,2..];
  list[Tree] childrenOf(Tree t) = [];
  
  // for now explicitly passed, github issue for generic implementation: https://github.com/usethesource/rascal/issues/974
  map[str, Synthesized[Tree, &ATTR]] getDefinedSynthesizedAttributes(type[Tree] \type) {
    return (attr : attrValue | str attr <- keywordParamNamesWithDefault, Synthesized[Tree, &ATTR] attrValue := keywordParamNamesWithDefault[attr]);
    // ( attr : defaultValue(keywordParamNamesWithDefault[attr]) | attr <- keywordParamNamesWithDefault); //( "scope": value() {return "default";} ); 
  }

  // get all relevant attributes of the children of n
  MultiMap[str, Synthesized[Tree, &ATTR]] getSynthesizedAttributes(Tree n) { 
    //println("<n>");
    	children = childrenOf(n);
    	//println("children: <children>");
        // filter out literals (TODO is this enough for all situations?)
    	list[node] childNodes = [c | node c <- children, appl(prod(\lit(_), _, _), _) !:= c ];
     	//println("\nchildNodes: <childNodes>");
     
    	// get the relevant attributes
    	list[map[str, Synthesized[Tree, &ATTR]]] childAttributes = [ {
    	  // explicit set kw params
    	  map[str,value] kws = getKeywordParameters(child);
    	  //println("\tfound on child <child>: <(kw : attr.attr | kw <- kws, Synthesized[Tree, &ATTR] attr := kws[kw])>");
    	  map[str, Synthesized[Tree, &ATTR]] synthAttrs = 
    	    (kw : attrValue | str kw <- getKeywordParameters(child), Synthesized[Tree, &ATTR] attrValue := kws[kw]);
      //println("\tsynthAttrs found on child <child>: <synthAttrs>");
    	  // which are defined?
    	  map[str, Synthesized[Tree, &ATTR]] attributeNames = getDefinedSynthesizedAttributes(#&TREE);
    	  // TODO filter on `Synthesized` Type
    	  // get all defined attributes, but not explicitely set
    	  map[str, Synthesized[Tree, &ATTR]] missingWithDefault =
    	    ( attributeName: attributeNames[attributeName] | str attributeName <- attributeNames, attributeName notin domain(kws));
    	  //println("misisng: <missingWithDefault>");  
    	  
    	  map[str, Synthesized[Tree, &ATTR]] result = missingWithDefault + synthAttrs;
    	  //println("\tfound for <child> synth: <[ca.attr | Synthesized[Tree, &ATTR] ca <- range(result)]>");
    	  result;
    	} | child <- childNodes];
    	//println("childAttributes for <n>: <[ca.attr | Synthesized[Tree, &ATTR] ca <- range(childAttributes)]>");
    	
    	MultiMap[str, Synthesized[Tree, &ATTR]] empty = ();
    	MultiMap[str, Synthesized[Tree, &ATTR]] result = (empty | add(it, k, ck) | map[str, Synthesized[Tree, &ATTR]] c <- childAttributes
    	                                                                         , str k <- c
    	                                                                         , Synthesized[Tree, &ATTR] ck := c[k]);
    	
    	//println("<n> result: <result>");
    	return result;
  }
  
  // TODO make real implementation - extract from definition in the end
  &ATTR(Tree input, list[&ATTR] fromChildren) extractCompute(Tree tree, str attributeName) {
    return keywordParamNamesWithDefault[attributeName].compute;
    //return &ATTR(Tree t, list[&ATTR] fromChildren) {
    //  println("called");
    //  
    //  switch(t) {
    //    case leaf(val)          : return val;
    //    case \node(left, right) : return min(fromChildren);
    //  }
    //  println("no match on <t>");
    //  return 0;
    //};
  };
    
  // join attributes using the given function
  map[str, Synthesized[Tree, &ATTR]] joinAttributes(Tree tree, MultiMap[str, Synthesized[Tree, &ATTR]] attributes) {
    //value fold(fun, list[value] values) = ( "" | fun(it, val) | value val <- values );
    
    //return (kw : fold(fun, values) | str kw <- attributes, list[value] values := attributes[kw] );
       
    map[str, Synthesized[Tree, &ATTR]] result = ( attribute : updatedValue
                                                | str attribute <- attributes//, bprintln("attributes: <attributes>")
    													                   , list[Synthesized[Tree, &ATTR]] attributeValues := attributes[attribute]//, bprintln("attributeValues: <attributeValues>")
    													                   , list[&ATTR] currentValues := [attributeValue.attr | attributeValue <- attributeValues]//, bprintln("currentValues: <currentValues>")
    													                   , &ATTR(Tree, list[&ATTR]) compute := extractCompute(tree, attribute)
    													                   //, bprintln("compute? <compute> + result <compute(tree, currentValues)>")
    													                   , updatedValue := attributeValues[0][attr = compute(tree, currentValues) ] // TODO this is not safe
    													                   );
    return result;    													                          
  };
  
  // Helper to mark if node has been handled
  set[Tree] synthesisHandled = {};
 
  Tree handleTree(Tree t) {
    MultiMap[str, Synthesized[Tree, &ATTR]] attributes = getSynthesizedAttributes(t);
    //println("<t> found synth attributes <attributes>");
    map[str, Synthesized[Tree, &ATTR]] joinedAttributes = joinAttributes(t, attributes);
    //println("<t> found joined attributes <joinedAttributes>");
    
    // explicitly set synth attributes override copied from child
    // TODO fix order here for interdependent attributes
    map[str, Synthesized[Tree, &ATTR]] attributesSetOnSelf = 
      (attr : synth | kwParams := getKeywordParameters(t), attr <- kwParams, Synthesized[Tree, &ATTR] synth := kwParams[attr]);
    //println("found on self <attributesSetOnSelf>");
    
    if(!isEmpty(joinedAttributes)) {
    // if current node has explicitly set value, use that else, compute from children
      map[str, Synthesized[Tree, &ATTR]]  synthesizedAttributes = joinedAttributes + attributesSetOnSelf;
      Tree updatedTree = setKeywordParameters(t, synthesizedAttributes);
    //println("updated: <updatedTree> kws: <getKeywordParameters(updatedTree)>");
    
      synthesisHandled += updatedTree;
      return updatedTree;
    } else {
      synthesisHandled += t;
      return t;
    }
  };
 
  &TREE result = input; 
  solve(result) {
    result = bottom-up visit(result) {
      case Tree t => handleTree(t) 
        when appl(prod(\lit(_), _, _), _)     !:= t, // no literal
             appl(prod(\layouts(_), _, _), _) !:= t, // no layout
             t notin synthesisHandled
    }
    //vs = getKeywordParameters(result);
    //println("solve iter: <result> kws: <vs>");
  };
  
  return result;
}

