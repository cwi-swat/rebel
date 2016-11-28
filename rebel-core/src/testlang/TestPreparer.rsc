module testlang::TestPreparer

import testlang::Syntax;
import testlang::Resolver;

import lang::ExtendedSyntax;
import lang::Builder;
import lang::Finder;

import analysis::CommonAnalysisFunctions;

import ParseTree;
import util::Maybe;
import String;
import DateTime;
import IO;

State constructStateSetup(StateSetup setup, TestRefs refs, set[Built] builtSpecs) {
  println(setup);
  
  Expr (Type) idGenerator = idGenerator();
  
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
    map[str, Expr] setupVals = ( "<decl.field>": val | FieldValueDeclaration decl <- decls, /Expr val := decl.val);   
    
    map[str, Type] nonKeySpecFields = ( "<f.name>" : f.tipe | FieldDecl f <- m.spec.fields.fields, /(Annotation)`@key` !:= f.meta, !startsWith("<f.name>", "_"));
    map[str, Type] keyFields = ( "<f.name>" : f.tipe | FieldDecl f <- m.spec.fields.fields, /(Annotation)`@key` := f.meta);
    
    list[Variable] vars = [var(name, nonKeySpecFields[name], val) | str name <- nonKeySpecFields, Expr val := ((name in setupVals) ? setupVals[name] : (Expr)`ANY`)];
    list[Variable] keys = [var(name, keyFields[name], val) | str name <- keyFields, Expr val := ((name in setupVals) ? setupVals[name] : idGenerator(keyFields[name]))];     
     
    if (just(StateRef sr) := state) {
      if ((StateRef)`uninitialized` := sr, /(StateFrom)`<Int nr>: <LifeCycleModifier? lcm> <VarName _> <StateTo* _>` := m.spec.lifeCycle, /(LifeCycleModifier)`initial` := lcm) {
        vars += var("_state", (Type)`Integer`, (Expr)`<Int nr>`);
      } else if ((StateFrom)`<Int nr> : <LifeCycleModifier? lcm> <VarName from> <StateTo* _>` <- m.spec.lifeCycle.from, "<from>" == "<sr>") {
        vars += var("_state", (Type)`Integer`, (Expr)`<Int nr>`);
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
      list[MultipleInstanceFieldValueDeclaration] fds = [fvd | /fvd:(MultipleInstanceFieldValueDeclaration)`- one with <{FieldValueDeclaration DeclSeperator}+ decls>` <- values];
      
      for (int i <- [0..toInt("<nr>")]) {
        list[FieldValueDeclaration] fvds = [];
        if (size(fds) > i) {
          fvds = [fvd | FieldValueDeclaration fvd <- fds[i].decls];
        }
        
        instances += constructInstance(m, (/StateRef sr := state) ? just(sr) : nothing(), fvds);
      }
    }
  }
  
  return state(0, getValueOfNow(), instances, noStep());
}

private Maybe[SetupStatement] findSetupStatementContaining(loc ref, StateSetup setup) {
  for (SetupStatement stat <- setup.body, contains(stat@\loc, ref)) {
    return just(stat);
  } 
  
  return nothing();
}

private Expr (Type) idGenerator(str IBANPrefix = "NL10INGB000000") {
  int accountIter = 0;
  int intIter = 0;

  Expr generateId((Type)`IBAN`) { accountIter += 1; println("Generated IBAN = <IBANPrefix><accountIter>"); return [Expr]"<IBANPrefix><accountIter>"; }
  Expr generateId((Type)`Integer`) {intIter += 1; return [Expr]"<intIter>"; }
  default Expr generateId(Type t) { throw "Id proposal for type \'<t>\' not yet implemented"; }
  
  return generateId;
}

private str toMonth(int m) { 
  switch(m) {
    case 1: return "Jan";
    case 2: return "Feb";
    case 3: return "Mar";
    case 4: return "Apr";
    case 5: return "May";
    case 6: return "Jun";
    case 7: return "Jul";
    case 8: return "Aug";
    case 9: return "Sep";
    case 10: return "Oct";
    case 11: return "Nov";
    case 12: return "Dec";
  }
}
