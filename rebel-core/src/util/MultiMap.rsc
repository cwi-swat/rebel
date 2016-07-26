module util::MultiMap

import util::TestUtils;

alias MultiMap[&K, &V] = map[&K, list[&V]];

MultiMap[&K, &V] add(MultiMap[&K, &V] m, &K key, &V val) { 
  if(m[key]?) {
    return m[key] = m[key] + val;
  } else {
    return m[key] = [val];
  }
}

MultiMap[int, str] mm =  (1 : ["a"]);

test bool updateWithNewKey()           = eq(add(mm, 2, "b"), (1: ["a"], 2:["b"]));
test bool updateWithExistingExisting() = eq(add(mm, 1, "b"), (1: ["a", "b"]));