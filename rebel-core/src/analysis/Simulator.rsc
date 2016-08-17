module analysis::Simulator

import lang::ExtendedSyntax;

import lang::smtlib25::AST;

import IO;
import Set;
import String;
import List;

alias RebelLit = lang::Syntax::Literal;

data TransitionResult
	= failed(str reason)
	| successful(State new)
	;

data Variable = var(str name, Type tipe, value val);
data EntityInstance = instance(str entityType, list[lang::Syntax::Literal] id, bool initialized, list[Variable] vals);  
data State = state(int nr, DateTime now, list[EntityInstance] instances);

data Setup = setup(map[str, int] maxAllowedInstances);

TransitionResult initialize(str entity, str transitionToFire, list[Variable] transitionParams, State current, set[Module] spcs) {  
  list[Command] smt = declareSmtTypes(spcs) + 
                      declareSmtVariables(entity, transitionToFire, transitionParams, spcs) +
                      declareSmtSpecLookup(spcs);
  
  return failed("Not yet completed implementation"); 
}  

TransitionResult transition(str entity, str id, str transitionToFire, list[Variable] transitionParams, State current, set[Module] spcs) {	
  list[Command] smt = declareSmtTypes(specs);
  
  return failed("Not yet completed implementation"); 
}  

list[Command] declareSmtSpecLookup(set[Module] mods) {
  list[Command] smt =[];

  for (/normalized(_, _, TypeName name, _, Fields fields, _, _, _, _, _, _) := mods) {
    // lookup @key fields
    list[Sort] sortsOfKey = [toSort(tipe) | /(FieldDecl)`<VarName _>: <Type tipe> @key` := fields];
    smt += declareFunction("spec_<name>", [custom("State")] + sortsOfKey, custom("<name>"));  
    smt += declareFunction("spec_<name>_initialized", [custom("<name>")], \bool());
  }
  
  return smt;
}

list[Command] declareSmtTypes(set[Module] specs) {
  // first declare the build in Rebel types
  list[Command] smt = declareRebelTypesAsSmtSorts();
  
  // Add the state sort as undefined sort
  smt += declareSort("State");
  
  // Add 'specification' types as undefined sorts
  smt += toList({declareSort("<spc.name>") | /Specification spc := specs});
  
  return smt; 
}

list[Command] declareSmtVariables(str entity, str transitionToFire, list[Variable] transitionParams, set[Module] spcs) {
  // declare functions for all entity fields
  list[Command] smt = [declareFunction("field_<spc.name>_<f.name>", [custom("<spc.name>")], toSort(f.tipe)) | /Specification spc := spcs, /FieldDecl f := spc.fields];
  
  smt += [declareFunction("eventParam_<entity>_<transitionToFire>_<v.name>", [custom("State")], toSort(v.tipe)) | Variable v <- transitionParams];
  
  return smt; 
}

list[Command] translateState(State state) {
  // Declare the current and next state variables
  list[Command] smt = [declareConst("current", custom("State")), declareConst("next", custom("State"))];
  
  // Assert the current value for 'now'
  smt += [declareFunction("now", [custom("State")], custom("DateTime")), \assert(eq(functionCall(simple("now"), [var(simple("current"))]), lit(toLit(state.now))))];
  
  // Add whether the entities are initialized or not
  smt += [\assert(not(functionCall(simple("spec_<ei.entityType>_initialized"), [functionCall(simple("spec_<ei.entityType>"), [var(simple("current")), *[lit(toLit(i)) | lang::Syntax::Literal i <- ei.id]])]))) | EntityInstance ei <- state.instances, !ei.initialized] + 
         [\assert(functionCall(simple("spec_<ei.entityType>_initialized"), [functionCall(simple("spec_<ei.entityType>"), [var(simple("current")), *[lit(toLit(i)) | lang::Syntax::Literal i <- ei.id]])])) | EntityInstance ei <- state.instances, ei.initialized];;
  
  // Assert all the current values of the entities
  smt += [\assert(eq(functionCall(simple("field_<ei.entityType>_<v.name>"), [functionCall(simple("spec_<ei.entityType>"), [var(simple("current")), *[lit(toLit(i)) | lang::Syntax::Literal i <- ei.id]])]), lit(toLit(v.val)))) | EntityInstance ei <- state.instances, ei.initialized, Variable v <- ei. vals];
  
  return smt; 
}

list[Command] translateTransitionParams(str entity, str transitionToFire, list[Variable] params) =
  [\assert(eq(functionCall(simple("eventParam_<entity>_<transitionToFire>_<p.name>"), [var(simple("next"))]), lit(toLit(p.val)))) | Variable p <- params]; 

list[Command] translateEventToSingleAsserts(EventDef evnt) {
  return [];
}

Formula translateStat((Statement)`(<Statement s>)`) = translateStat(s);
Formula translateStat((Statement)`<Annotations _> <Expr e>;`) = translateExp(e);

Formula translateExpr((Expr)`this.<VarName field>`) = field;
Formula translateExpr((Expr)`<Expr expr>.<VarName field>`) = field;

Formula translateExpr((Expr)`(<Expr e>)`) = translateExpr(e);
Formula translateExpr((Expr)`<Literal l>`) = lit(translateLit(l));
Formula translateExpr((Expr)`<Ref r>`) = var(simple("<ref>"));
Formula translateExpr((Expr)`<VarName function>(<{Expr ","}* params>)`) = functionCall(simple("<function>"), [translateExpr(p) | Expr p <- params]);
Formula translateExpr((Expr)`<Expr lhs>.<VarName field>`) = functionCall(simple("<field>"), [translateExpr(lhs)]); 
 
  //| "{" Expr lower ".." Expr upper"}"
  //| left Expr var!accessor "[" Expr indx "]"
  //| "(" {MapElement ","}* mapElems ")"
  //| staticSet: "{" {Expr ","}* setElems "}"
  //| "{" Expr elem "|" Expr loopVar "\<-" Expr set "}"
  //| "{" Expr init "|" Statement reducer "|" Expr loopVar "\<-" Expr set "}" 
  //> new: "new" Expr expr
  //| "not" Expr expr
  //| "-" Expr
  //> left  ( Expr lhs "*" Expr rhs
  //    | isMember: Expr lhs "in" Expr rhs
  //    | Expr lhs "/" Expr rhs
  //    | Expr lhs "%" Expr rhs
  //    )
  //> left  ( Expr lhs "+" Expr rhs
  //    | subtract: Expr lhs "-" Expr rhs
  //    )
  //> non-assoc ( smallerThan: Expr lhs "\<" Expr rhs
  //    | smallerThanEquals: Expr lhs "\<=" Expr rhs
  //    | greaterThan: Expr lhs "\>" Expr rhs
  //    | greaterThanEquals: Expr lhs "\>=" Expr rhs
  //    | equals: Expr lhs "==" Expr rhs
  //    | notEqual: Expr lhs "!=" Expr rhs
  //    )
  //> left and: Expr lhs "&&" Expr rhs
  //> left Expr lhs "||" Expr rhs
  //> right ( Expr cond "?" Expr whenTrue ":" Expr whenFalse
  //  | Expr cond "-\>" Expr implication
  //  )
  //| "initialized" Expr
  //| "finalized" Expr
  //| Expr lhs "instate" Expr rhs
Sort toSort((Type)`Currency`) = \int();
Sort toSort((Type)`Date`) = custom("Date");
Sort toSort((Type)`Time`) = custom("Time");
Sort toSort((Type)`DateTime`) = custom("DateTime");
Sort toSort((Type)`IBAN`) = custom("IBAN");
Sort toSort((Type)`Money`) = custom("Money");
Sort toSort((Type)`Integer`) = \int();
Sort toSort((Type)`Frequency`) = \int();
default Sort toSort(Type t) { throw "Sort conversion for <t> not yet implemented"; }

Literal toLit(value v) = toLit(l) when lang::Syntax::Literal l := v;

Literal toLit((Literal)`<Int i>`) = toLit(i);
Literal toLit((Literal)`<IBAN i>`) = toLit(i);

Literal toLit((Literal)`<Money m>`) = toLit(m);

Literal toLit(Money m) = adt("consMoney", [strVal("<m.cur>"), toLit(m.amount)]);
Literal toLit(MoneyAmount ma) = intVal(toInt("<ma.whole>") * 100 + toInt("<ma.decimals>"));

Literal toLit(DateTime dt) = adt("consDateTime", [toLit(dt.date), toLit(dt.time)]);
Literal toLit(Date d) = adt("consDate", [toLit(d.day), toLit(d.month),toLit(year)]) when d has year, /Int year := d.year;
Literal toLit(Date d) = adt("consDate", [toLit(d.day), toLit(d.month), toLit(0)]) when !(d has year); 
Literal toLit(Time t) = adt("consTime", [toLit(toInt("<t.hour>")), toLit(toInt("<t.minutes>")), toLit(toInt("<sec>"))]) when t has sewconds, /Int sec := t.seconds; 
Literal toLit(Time t) = adt("consTime", [toLit(toInt("<t.hour>")), toLit(toInt("<t.minutes>")), toLit(0)]) when !(t has seconds) ; 
Literal toLit(IBAN i) = adt("consIBAN", [toLit("<i.countryCode>"), toLit(toInt("<i.checksum>")), toLit("<i.accountNumber>")]);

Literal toLit((Month)`Jan`) = intVal(1); 
Literal toLit((Month)`Feb`) = intVal(2);
Literal toLit((Month)`Mar`) = intVal(3);
Literal toLit((Month)`Apr`) = intVal(4);
Literal toLit((Month)`May`) = intVal(5);
Literal toLit((Month)`Jun`) = intVal(6); 
Literal toLit((Month)`Jul`) = intVal(7);
Literal toLit((Month)`Aug`) = intVal(8);
Literal toLit((Month)`Sep`) = intVal(9);
Literal toLit((Month)`Oct`) = intVal(10);
Literal toLit((Month)`Nov`) = intVal(11);
Literal toLit((Month)`Dec`) = intVal(12);

Literal toLit(Int i) = intVal(toInt("<i>"));
Literal toLit(int i) = intVal(i);

Literal toLit(String s) = strVal("<s>");
Literal toLit(str s) = strVal(s);

default Literal toLit(value l) { throw "toLit(..) not implemented for <l>"; }

list[Command] declareRebelTypesAsSmtSorts() {   
  set[tuple[str,Sort]] rebelTypes = {<"Currency", \int()>,
                                     <"Frequency", \int()>,
                                     <"Percentage", \int()>,
                                     <"Period", \int()>,
                                     <"Term", \int()>};
                             
  return [defineSort(name, [], sort) | <str name, Sort sort> <- rebelTypes] +
         [declareDataTypes([], [dataTypeDef("IBAN", [combinedCons("consIBAN", [sortedVar("countryCode", string()), sortedVar("checksum",\int()), sortedVar("accountNumber", string())])])]),
          declareDataTypes([], [dataTypeDef("Money", [combinedCons("consMoney", [sortedVar("currency", string()), sortedVar("amount", \int())])])]),
          declareDataTypes([], [dataTypeDef("Date", [
            combinedCons("consDate", [sortedVar("date", \int()), sortedVar("month", \int()), sortedVar("year", \int())]), 
            cons("undefDate")])]),
          declareDataTypes([], [dataTypeDef("Time", [
            combinedCons("consTime", [sortedVar("hour", \int()), sortedVar("minutes", \int()), sortedVar("seconds", \int())]), 
            cons("undefTime")])]),
          declareDataTypes([], [dataTypeDef("DateTime", [combinedCons("consDateTime", [sortedVar("date", custom("Date")), sortedVar("time", custom("Time"))]), cons("undefDateTime")])])                                   
          ];                                  
}

