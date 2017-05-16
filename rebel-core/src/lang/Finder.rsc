module lang::Finder

import lang::ExtendedSyntax;
import lang::Builder;
import lang::Resolver;

import util::Maybe;
import ParseTree;
import IO;

bool contains(loc l1, loc l2) = l1.top == l2.top && l1 >= l2;

Maybe[Built] findBuilt(loc locInNormalizedMod, set[Built] mods) {
  if (Built b <- mods, b.inlinedMod@\loc.top == locInNormalizedMod.top) {
    return just(b);
  } else {
    return nothing();
  }
} 

Maybe[Built] findBuiltBeloningToEvent(loc locEventDef, set[Built] mods) {
  if (Built b <- mods, Module m := b.normalizedMod, m has spec, EventDef evnt <- m.spec.events.events, evnt@\loc == locEventDef) {
    return just(b);
  } else {
    return nothing();
  }
} 

Maybe[Module] findInlinedSpec(loc specDef, set[Built] mods) {
  if (Built b <- mods, b.inlinedMod has spec, b.inlinedMod.spec@\loc == specDef) {
    return just(b.inlinedMod);
  } 
  else {
    return nothing();
  }
}

Maybe[EventDef] findInlinedEventDef(loc evntToFind, set[Built] builds) {
  if (Built b <- builds, Module m := b.inlinedMod, m has spec, EventDef evnt <- m.spec.events.events, contains(evnt@\loc, evntToFind)) {
    return just(evnt);
  } else {
    return nothing();
  } 
}

Maybe[EventDef] findNormalizedEventDef(loc evntToFind, set[Built] builds) {
  if (Built b <- builds, Module m := b.normalizedMod, m has spec, EventDef evnt <- m.spec.events.events, contains(evnt@\loc, evntToFind)) {
    return just(evnt);
  } else {
    return nothing();
  } 
} 

Maybe[EventRef] findInlinedEventRef(loc evntToFind, set[Built] builds) {
  if (Built b <- builds, Module m := b.inlinedMod, m has spec, EventRef evnt <- m.spec.eventRefs.events, evnt@\loc == evntToFind) {
    return just(evnt);
  } else {
    return nothing();
  } 
} 

Maybe[Module] findNormalizedSpecModuleContaining(loc specToFind, set[Built] builds) {
  if (Built b <- builds, Module m := b.normalizedMod, m has spec, contains(m@\loc, specToFind)) {
    return just(m);
  } else {
    return nothing(); 
  }
}

Maybe[StateFrom] findNormalizedStateFrom(loc stateToFind, set[Built] builds) {
  if (Built b <- builds, Module m := b.normalizedMod, m has spec, StateFrom sf <- m.spec.lifeCycle.from, sf@\loc == stateToFind) {
    return just(sf);
  } else {
    return nothing();
  }  
}

Maybe[FunctionDef] findFunctionDef(loc funcToFind, set[Built] builds) {
  if (Built b <- builds, Module m := b.normalizedMod, m has spec, FunctionDef f <- m.spec.functions.defs, f@\loc == funcToFind) {
    return just(f);
  } else {
    return nothing();
  }
}
