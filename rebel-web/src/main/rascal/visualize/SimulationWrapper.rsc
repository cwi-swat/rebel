module visualize::SimulationWrapper

import analysis::Simulator;
import lang::ExtendedSyntax;

data Param = param(str name, str \type);

data Variable 
  = simVar(str name, str \type, str \value)
  | simUninitialized(str name, str \type)
  ;
  
alias Variables = list[Variable];

data EntityInstance = simInstance(str entityType, list[str] ids, list[Variable] vals);  
data State = simState(int nr, str nowTS, list[EntityInstance] instances);

State toWeb(state(int nr, DateTime now, list[EntityInstance] instances)) 
  = simState(nr, "<now>", [toWeb(ei) | ei <- instances]);

State toSim(simState(int nr, str now, list[EntityInstance] instances))
  = state(nr, [DateTime]"<now>", [toSim(ei) | ei <- instances]);

EntityInstance toWeb(instance(str entityType, list[RebelLit] id, list[Variable] vals)) 
  = simInstance(entityType, ["<i>" | i <- id], [toWeb(v) | v <- vals]);

EntityInstance toSim(simInstance(str entityType, list[str] ids, list[Variable] vals))
  = instance(entityType, [[Literal]"<i>" | i <- ids], [toSim(v) | v <- vals]);

Variable toWeb(var(str name, Type tipe, value val)) 
  = simVar(name, "<tipe>", "<val>");

Variable toWeb(uninitialized(str name, Type tipe))
  = simUninitialized(name, "<tipe>");

Variable toSim(simVar(str name, str tipe, str val))
  = var(name, [Type]"<tipe>", [Literal]"<val>");

Variable toSim(simUninitialized(str name, str tipe))
  = uninitialized(name, [Type]"<tipe>")
  ;

list[Variable] toSim(list[Variable] vars) = [toSim(v) | v <- vars];
  
list[Param] toWeb(list[Param] params) = [toWeb(p) | p <- params];
  
Param toWeb(param(str name, Type tipe))
  = param(name, "<tipe>");