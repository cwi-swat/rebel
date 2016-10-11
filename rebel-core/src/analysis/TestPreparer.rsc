module analysis::TestPreparer

import testlang::Syntax;
import testlang::Resolver;

import lang::ExtendedSyntax;
import lang::Builder;
import lang::Finder;

import analysis::Simulator;

import ParseTree;
import util::Maybe;
import String;
import DateTime;
import IO;

State constructStateSetup(StateSetup setup, TestRefs refs, set[Built] builtSpecs) {
  Literal (Type) idGenerator = idGenerator();
  
  DateTime getValueOfNow() {
    if ((SetupStatement)`now is <DateTime now>;` <- setup.body) {
      return now;
    } else {
      // return current date and time
      datetime now = now();
      return [DateTime]"<now.day> <toMonth(now.month)> <now.year>, <right("<now.hour>", 2, "0")>:<right("<now.minute>",2,"0")>";
    }
  }
  
  EntityInstance constructInstance(Module m, Maybe[StateRef] state, list[FieldValueDeclaration] decls) {
    map[str, Literal] setupVals = ( "<decl.field>": l | FieldValueDeclaration decl <- decls, /Literal l := decl.val);   
    
    map[str, Type] nonKeySpecFields = ( "<f.name>" : f.tipe | FieldDecl f <- m.spec.fields.fields, /(Annotation)`@key` !:= f.meta, !startsWith("<f.name>", "_"));
    map[str, Type] keyFields = ( "<name>" : tipe | (FieldDecl)`<VarName name> : <Type tipe> @key` <- m.spec.fields.fields);
    
    list[Variable] vars = [var(name, nonKeySpecFields[name], val) | str name <- nonKeySpecFields, Literal val := ((name in setupVals) ? setupVals[name] : (Literal)`ANY`)];
    list[Variable] keys = [var(name, keyFields[name], val) | str name <- keyFields, Literal val := ((name in setupVals) ? setupVals[name] : idGenerator(keyFields[name]))];     
    
    if (just(StateRef sr) := state) {
      if ((StateRef)`uninitialized` := sr, /(StateFrom)`<Int nr>: <LifeCycleModifier? lcm> <VarName _> <StateTo* _>` := m.spec.lifeCycle, /(LifeCycleModifier)`initial` := lcm) {
        vars += var("_state", (Type)`Integer`, (Literal)`<Int nr>`);
      } else if ((StateFrom)`<Int nr> : <LifeCycleModifier? lcm> <VarName from> <StateTo* _>` <- m.spec.lifeCycle.from, "<from>" == "<sr>") {
        vars += var("_state", (Type)`Integer`, (Literal)`<Int nr>`);
      }
    }
    
    return instance("<m.modDef.fqn>", [v.val | v <- keys], keys + vars);
  }
  
  list[EntityInstance] instances = [];
  
  for (<loc specRef, loc specDef> <- refs.specs, 
        just(Module m) := findNormalizedSpecModuleContaining(specDef, builtSpecs), 
        just((SetupStatement)`<Int? nr> <StateRef? state> <TypeName entity> <FieldValueDeclarations? values>;`) := findSetupStatementContaining(specRef, setup)) {
    
    if (/Int _ !:= nr || toInt("<nr>") == 1) {
      list[FieldValueDeclaration] fvds = [d | /(SingleInstanceFieldValueDeclaration)`with <{FieldValueDeclaration DeclSeperator}+ decls>` := values, FieldValueDeclaration d <- decls];
     
      instances += constructInstance(m, (/StateRef sr := state) ? just(sr) : nothing(), [fvd | FieldValueDeclaration fvd <- fvds]); 
    } else {
      for (/(MultipleInstanceFieldValueDeclaration)`- one with <{FieldValueDeclaration DeclSeperator}+ decls>` <- values) {
        instances += constructInstance(m, (/StateRef sr := state) ? just(sr) : nothing(), [fvd | FieldValueDeclaration fvd <- decls]);
      }
    }
  }
  
  return state(0, getValueOfNow(), instances);
}

private Maybe[SetupStatement] findSetupStatementContaining(loc ref, StateSetup setup) {
  for (SetupStatement stat <- setup.body, contains(stat@\loc, ref)) {
    return just(stat);
  } 
  
  return nothing();
}

private Literal (Type) idGenerator(str IBANPrefix = "NL10INGB000000") {
  int accountIter = 0;
  int intIter = 0;

  Literal generateId((Type)`IBAN`) { accountIter += 1; return [Literal]"<IBANPrefix><accountIter>"; }
  Literal generateId((Type)`Integer`) {intIter += 1; return [Literal]"<intIter>"; }
  default Literal generateId(Type t) { throw "Id proposal for type \'<t>\' not yet implemented"; }
  
  return generateId;
}

private str toMonth(int m) { 
  switch(m) {
    case 1: return "Jan";
    case 2: return "Feb";
    case 3: return "Feb";
    case 4: return "Feb";
    case 5: return "Feb";
    case 6: return "Feb";
    case 7: return "Feb";
    case 8: return "Feb";
    case 9: return "Feb";
    case 10: return "Feb";
    case 11: return "Feb";
    case 12: return "Feb";
  }
}
