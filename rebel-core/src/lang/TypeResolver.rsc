@license{
Copyright (c) 2016, CWI
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
}
@contributor{Jouke Stoel - jouke.stoel@cwi.nl - CWI}
module lang::TypeResolver

import IO;
import lang::ExtendedSyntax;
extend lang::Syntax;
syntax Type = "$$INVALID$$";
import Node;
import ParseTree;
import Set;

// Invalid type should have originator location
data ResolvedType = invalidType() | validType(Type resolvedType);
data ScopeType = global(loc globalScope) | local(loc localScope); // store affecting locations
data ScopeKey = scopeKey(ScopeType scopeType, loc declareLocation, Type variableType); 
alias Scope = map[str, ScopeKey]; // todo: multiple entries for same keyword?

// visit nodes bottom-up (breadth-first traversal) and append map with types
// todo: interesting for IDE typechecking specifications, SMT proof and code generation
map[loc, ResolvedType] getTypeMapping(Specification spec) {
    Scope getGlobalScope(Specification spec) = ("<f.name>" : scopeKey(global(spec@\loc), f@\loc, f.tipe) | FieldDecl f <- spec.fields.fields) when spec.fields has fields;
    default Scope getGlobalScope(Specification spec) = ();
    return visitNode(spec, getGlobalScope(spec), ());
}

map[loc, ResolvedType] visitNode(Specification s, Scope scope, map[loc, ResolvedType] typeMap) {
    println("We have a scope: <scope>");
    
    // TODO: use scope everywhere and append it blabla

    if (s has events) {
        for (EventDef ev <- s.events.events) {
            typeMap = visitNode(ev, scope, typeMap);
        }
    }
    return typeMap;
}

map[loc, ResolvedType] visitNode(EventDef ev, Scope scope, map[loc, ResolvedType] typeMap) { // todo perhaps add a variable scope? maybe not necessary due to ref
    for (Parameter p <- ev.transitionParams) typeMap[ev@\loc] = validType(p.tipe);
    
    Scope appendParameterScope(Scope scope, EventDef event) {
        for (Parameter p <- event.transitionParams) {
            scope["<p.name>"] = scopeKey(local(event@\loc), p@\loc, p.tipe); 
        }
        return scope;
    }
    scope = appendParameterScope(scope, ev); // TODO test this
    typeMap = visitNode(ev.pre, scope, typeMap);
    typeMap = visitNode(ev.post, scope, typeMap);
    // TODO: syncblock

    return typeMap;
}

map[loc, ResolvedType] visitNode(Preconditions? pre, Scope scope, map[loc, ResolvedType] typeMap) = visitNode(p.stats, scope, typeMap) when (/Preconditions p := pre);
default map[loc, ResolvedType] visitNode(Preconditions? _, Scope scope, map[loc, ResolvedType] typeMap) = typeMap;

map[loc, ResolvedType] visitNode(Postconditions? post, Scope scope, map[loc, ResolvedType] typeMap) = visitNode(removePostConditionPrefix(p.stats), scope, typeMap) when (/Postconditions p := post);
default map[loc, ResolvedType] visitNode(Postconditions? _, Scope scope, map[loc, ResolvedType] typeMap) = typeMap;
Statement* removePostConditionPrefix(Statement* stats) = visit (stats) { case (Expr)`new this.<VarName v>` => (Expr)`<VarName v>` };

map[loc, ResolvedType] visitNode((Statement)`<Annotations _><Expr e>;`, Scope scope, map[loc, ResolvedType] typeMap) = visitNode(e, scope, typeMap);
default map[loc, ResolvedType] visitNode(Statement s, Scope scope, map[loc, ResolvedType] typeMap) {
    println("Unsupported statement type");
    return typeMap;
}

map[loc, ResolvedType] visitNode(Statement* stats, Scope scope, map[loc, ResolvedType] typeMap) {
    for (Statement stat <- stats) typeMap = visitNode(stat, scope, typeMap);
    return typeMap;
}

map[loc, ResolvedType] visitNode(n:(Expr)`<Expr lhs> * <Expr rhs>`, Scope scope, map[loc, ResolvedType] typeMap) {
    typeMap = visitNode(lhs, scope, typeMap);
    typeMap = visitNode(rhs, scope, typeMap);

    println("Checking <n>");
    if (typeMap[lhs@\loc] is invalidType || typeMap[rhs@\loc] is invalidType) {
        return addInvalidTypeToMap(n, typeMap); // cascades to upper level
    }
    
    lhsType = typeMap[lhs@\loc].resolvedType;
    rhsType = typeMap[rhs@\loc].resolvedType;

    Type resolvedType = invalidType();
    if (lhsType == (Type)`Integer`) {
        if (rhsType == (Type)`Integer`) resolvedType = (Type)`Integer`;
        else if (rhsType == (Type)`Percentage`) resolvedType = (Type)`Percentage`;
        else if (rhsType == (Type)`Money`) resolvedType = (Type)`Money`;
    }
    else if (lhsType == (Type)`Date`) {
        if (rhsType == (Type)`Date`) resolvedType = (Type)`Term`;
        else if (rhsType == (Type)`Integer`) resolvedType = (Type)`Date`;
    }
    println("Resolved type for <n> to <resolvedType>");
    
    typeMap[n@\loc] = resolvedType;
    return typeMap;
}

map[loc, ResolvedType] visitNode(n:(Expr)`<Expr lhs> + <Expr rhs>`, Scope scope, map[loc, ResolvedType] typeMap) {
    typeMap = visitNode(rhs, scope, typeMap);
    typeMap = visitNode(lhs, scope, typeMap);

    println("Checking <n>");
    if (typeMap[lhs@\loc] is invalidType || typeMap[rhs@\loc] is invalidType) {
        return addInvalidTypeToMap(n, typeMap); // cascades to upper level
    }

    lhsType = typeMap[lhs@\loc].resolvedType;
    rhsType = typeMap[rhs@\loc].resolvedType;

    ResolvedType resolvedType = invalidType();
    if (lhsType == rhsType) {
        if (lhsType == (Type)`Integer`) {
            if (rhsType == (Type)`Integer`) resolvedType = validType((Type)`Integer`);
        }
        else if (lhsType == (Type)`Date`) {
            if (rhsType == (Type)`Date`) resolvedType = validType((Type)`Term`);
            else if (rhsType == (Type)`Integer`) resolvedType = validType((Type)`Date`); // Is this ok? or should we limit to terms
            else if (rhsType == (Type)`Term`) resolvedType = validType((Type)`Date`);
        }
    }
    println("Resolved type for <n> to <resolvedType>");
    
    typeMap[n@\loc] = resolvedType;
    return typeMap;
}


map[loc, ResolvedType] visitNode(n:(Expr)`<Expr lhs> - <Expr rhs>`, Scope scope, map[loc, ResolvedType] typeMap) {
    typeMap = visitNode(rhs, scope, typeMap);
    typeMap = visitNode(lhs, scope, typeMap);

    println("Checking <n>");
    if (typeMap[lhs@\loc] is invalidType || typeMap[rhs@\loc] is invalidType) {
        return addInvalidTypeToMap(n, typeMap); // cascades to upper level
    }

    lhsType = typeMap[lhs@\loc].resolvedType;
    rhsType = typeMap[rhs@\loc].resolvedType;

    ResolvedType resolvedType = invalidType();
    if (lhsType == (Type)`Integer`) {
	   if (rhsType == (Type)`Integer`) resolvedType = validType((Type)`Integer`);
    }
	else if (lhsType == (Type)`Date`) {
        if (rhsType == (Type)`Date`) resolvedType = validType((Type)`Term`);
        else if (rhsType == (Type)`Integer`) resolvedType = validType((Type)`Date`); // Is this ok? or should we limit to terms
	    else if (rhsType == (Type)`Term`) resolvedType = validType((Type)`Date`);
    }
    else if (lhsType == (Type)`Money` && rhsType == (Type)`Money`) resolvedType = validType((Type)`Money`);
    else if (lhsType == (Type)`Time` && rhsType == (Type)`Date`) resolvedType = validType((Type)`Date`); // assumption that time gets converted to date basis
    else if (lhsType == (Type)`Date` && rhsType == (Type)`Time`) resolvedType = validType((Type)`Date`); // assumption that time gets converted to date basis
    println("Resolved type for <n> to <resolvedType>");
    
    typeMap[n@\loc] = resolvedType;
    return typeMap;
}

map[loc, ResolvedType] visitNode(n:(Expr)`<Expr lhs> in <Expr rhs>`, Scope scope, map[loc, ResolvedType] typeMap) {
    typeMap = visitNode(lhs, scope, typeMap);
    typeMap = visitNode(rhs, scope, typeMap);
    
    println("Checking <n>");

    if (typeMap[lhs@\loc] is invalidType || typeMap[rhs@\loc] is invalidType) {
        return addInvalidTypeToMap(parent, typeMap); // cascades to upper level
    }
    
    lhsType = typeMap[rhs@\loc];
    rhsType = typeMap[rhs@\loc];
    invalidExp = (lhsType is invalidType || rhsType is invalidType);
    ResolvedType resolvedType = invalidType();
    if (!invalidExp) {
        if ((Type)`set [ <Type tipe> ]` := rhsType.resolvedType) {
           println("the type of lhs is <lhsType.resolvedType>");
           if (lhsType.resolvedType == rhsType.tipe) resolvedType = validType((Type)`Bool`);
        }
        // TODO: maps?
    }
    
    typeMap[n@\loc] = resolvedType;
    return typeMap;
}

map[loc, ResolvedType] visitNode(n:(Expr)`{<{Expr ","}* setElems>}`, Scope scope, map[loc, ResolvedType] typeMap) {
    elements = [ e | Expr e <- setElems];
    if (isEmpty(elements)) {
         // empty set
         throw "The empty set is not supported: <n>";
    }

    // Visit set elements
    for (Expr e <- elements) typeMap = visitNode(e, scope, typeMap);

    elementTypes = [ typeMap[e@\loc] | Expr e <- elements ];
    distinctTypeCount = size(toSet(elementTypes)); 
    if (distinctTypeCount > 1) {
        throw "Sets can only be defined homogenous: <n>";
    }
    assert(distinctTypeCount == 1);
    // Deduce type from first element in the list
    typeMap[n@\loc] = typeMap[elements[0]@\loc];
    return typeMap;
}

map[loc, ResolvedType] visitNode(n:(Expr)`<Expr lhs> \> <Expr rhs>`, Scope scope, map[loc, ResolvedType] typeMap) = checkComparisonExpression(n, lhs, rhs, scope, typeMap);
map[loc, ResolvedType] visitNode(n:(Expr)`<Expr lhs> \< <Expr rhs>`, Scope scope, map[loc, ResolvedType] typeMap) = checkComparisonExpression(n, lhs, rhs, scope, typeMap);
map[loc, ResolvedType] visitNode(n:(Expr)`<Expr lhs> != <Expr rhs>`, Scope scope, map[loc, ResolvedType] typeMap) = checkComparisonExpression(n, lhs, rhs, scope, typeMap);
map[loc, ResolvedType] visitNode(n:(Expr)`<Expr lhs> == <Expr rhs>`, Scope scope, map[loc, ResolvedType] typeMap) = checkComparisonExpression(n, lhs, rhs, scope, typeMap);
map[loc, ResolvedType] visitNode(n:(Expr)`<Expr lhs> \>= <Expr rhs>`, Scope scope, map[loc, ResolvedType] typeMap) = checkComparisonExpression(n, lhs, rhs, scope, typeMap);
map[loc, ResolvedType] visitNode(n:(Expr)`<Expr lhs> \<= <Expr rhs>`, Scope scope, map[loc, ResolvedType] typeMap) = checkComparisonExpression(n, lhs, rhs, scope, typeMap);
map[loc, ResolvedType] checkComparisonExpression(Expr parent, Expr lhs, Expr rhs, Scope scope, map[loc, ResolvedType] typeMap) {
    typeMap = visitNode(lhs, scope, typeMap);
    typeMap = visitNode(rhs, scope, typeMap);
    
    println("Checking <parent>");
    
    if (typeMap[lhs@\loc] is invalidType || typeMap[rhs@\loc] is invalidType) {
        return addInvalidTypeToMap(parent, typeMap); // cascades to upper level
    }
    
    lhsType = typeMap[lhs@\loc].resolvedType;
    rhsType = typeMap[rhs@\loc].resolvedType;

    ResolvedType resolvedType = invalidType();
    if (lhsType == rhsType) resolvedType = validType((Type)`Bool`);
    typeMap[parent@\loc] = resolvedType;

    return typeMap;    
}



map[loc, ResolvedType] addInvalidTypeToMap(Tree n, map[loc, ResolvedType] typeMap) {
    typeMap[n@\loc] = invalidType();
    return typeMap;
}

map[loc, ResolvedType] addResolvedTypeToMap(Tree n, map[loc, ResolvedType] typeMap, Type t) {
    println("Resolve: <n> to <t>");
    typeMap[n@\loc] = validType(t);
    return typeMap;
}

default map[loc, ResolvedType] visitNode(Expr e, Scope scope, map[loc, ResolvedType] typeMap) = addResolvedTypeToMap(e, typeMap, (Type)`Integer`);
map[loc, ResolvedType] visitNode((Expr)`<Time t>`, Scope scope, map[loc, ResolvedType] typeMap) = addResolvedTypeToMap(t, typeMap, (Type)`Time`);
map[loc, ResolvedType] visitNode((Expr)`<Ref r>`, Scope scope, map[loc, ResolvedType] typeMap) = addResolvedTypeToMap(r, typeMap, (Type)`Ref`);
// TODO: support more types
// TODO: resolve refs by scope
map[loc, ResolvedType] visitNode(n:(Expr)`<Int x>`, Scope scope, map[loc, ResolvedType] typeMap) = addResolvedTypeToMap(n, typeMap, (Type)`Integer`);
map[loc, ResolvedType] visitNode(n:(Expr)`<Bool _>`, Scope scope, map[loc, ResolvedType] typeMap) = addResolvedTypeToMap(n, typeMap, (Type)`Boolean`);
map[loc, ResolvedType] visitNode(n:(Expr)`<String _>`, Scope scope, map[loc, ResolvedType] typeMap) = addResolvedTypeToMap(n, typeMap, (Type)`String`);
map[loc, ResolvedType] visitNode(n:(Expr)`<Percentage _>`, Scope scope, map[loc, ResolvedType] typeMap) = addResolvedTypeToMap(n, typeMap, (Type)`Percentage`);
map[loc, ResolvedType] visitNode(n:(Expr)`<Date _>`, Scope scope, map[loc, ResolvedType] typeMap) = addResolvedTypeToMap(n, typeMap, (Type)`Date`);
map[loc, ResolvedType] visitNode(n:(Expr)`<Period _>`, Scope scope, map[loc, ResolvedType] typeMap) = addResolvedTypeToMap(n, typeMap, (Type)`Period`);
map[loc, ResolvedType] visitNode(n:(Expr)`<Frequency _>`, Scope scope, map[loc, ResolvedType] typeMap) = addResolvedTypeToMap(n, typeMap, (Type)`Frequency`);
map[loc, ResolvedType] visitNode(n:(Expr)`<Money _>`, Scope scope, map[loc, ResolvedType] typeMap) = addResolvedTypeToMap(n, typeMap, (Type)`Money`);
map[loc, ResolvedType] visitNode(n:(Expr)`<Currency _>`, Scope scope, map[loc, ResolvedType] typeMap) = addResolvedTypeToMap(n, typeMap, (Type)`Currency`);
map[loc, ResolvedType] visitNode(n:(Expr)`<Term _>`, Scope scope, map[loc, ResolvedType] typeMap) = addResolvedTypeToMap(n, typeMap, (Type)`Term`);
map[loc, ResolvedType] visitNode(n:(Expr)`<IBAN _>`, Scope scope, map[loc, ResolvedType] typeMap) = addResolvedTypeToMap(n, typeMap, (Type)`IBAN`);