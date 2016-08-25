module lang::Builder

import Message;
import util::Maybe;
import util::FileSystem;

import lang::Normalizer;
import lang::ExtendedSyntax;

alias Built = Module;

tuple[set[Message], Maybe[Built] load