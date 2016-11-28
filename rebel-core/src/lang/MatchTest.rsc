module lang::tests::MatchTest

data Nat = zero() | succ(Nat pred);

bool matching2([*Nat _, succ(x), *Nat _]) = true;
default bool matching2(list[Nat] _) = false;

bool matching3(list[Nat] n) = true when /succ(_) := n;
default bool matching3(list[Nat] _) = false;
