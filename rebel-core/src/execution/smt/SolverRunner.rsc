module analysis::SolverRunner

import execution::smtlib2::\solve::Z3;
import execution::smtlib2::command::Z3Ast;
import execution::smtlib2::command::response::Ast;
import execution::smtlib2::theory::ints::Ast;

import IO;

alias SolverPID = int;

SolverPID startSolver() {
	pid = startZ3();
	// make sure that proofs and unsatisfiable core are produced
	run(pid, script([setOption(produceProofs(true)), setOption(produceUnsatCores(true))]), debug=true);
	
	return pid;
}

void stopSolver(SolverPID pid) {
	stopZ3(pid);
}

void openScope(SolverPID pid) {
	runSolver(pid, [push(1)]);
}

void closeScope(SolverPID pid) {
	runSolver(pid, [pop(1)]);
}

bool isSatisfiable(SolverPID pid, list[Command] commands) = 
	returnedSatisfiable(runSolver(pid, commands + checkSatisfiable()));

bool isSatisfiableWithIsolation(SolverPID pid, list[Command] commands) =
	returnedSatisfiable(runSolver(pid, [push(1), *commands, checkSatisfiable(), pop(1)]));
	
void loadContext(SolverPID pid, list[Command] commands) {
	if (!(none() := runSolver(pid, commands))) {
		throw "ModelChecker SMT context could not be loaded";		
	}
}

private bool returnedSatisfiable(Response resp) {
	switch(resp) {
		case /sat() : return true;
		case /unsat(): return false;
		case /unknown(): throw "Could not compute satisfiability";
	}
}

list[FoundValue] getValues(SolverPID pid, list[Expr] variables) {
	resp = runSolver(pid, [getValue(variables)]);
	if (/foundValues(m:_) := resp) {
		return m;
	}
	
	return [];
}

list[str] getUnsatCore(SolverPID pid) {
	resp = runSolver(pid, [getUnsatCore()]);
	
	if (/unsatCore(labels) := resp) {
		return labels;
	} else {
		return [];
	}
}

private Response runSolver(SolverPID pid, list[Command] commands) {
	try {
		return run(pid, script(commands), debug=true);
	}
	catch er: throw "Error while running SMT solver, reason: <er>"; 	
}
