module visualize::tests::JsonUtilTest

import visualize::JsonUtil;

test bool escapeControlCharN() = jsonEscape("a\nb") == "a\\\nb";
test bool escapeQuote() = jsonEscape("a\"b") == "a\\\"b";  

test bool escapeAll() = jsonEscape("a\nb\"cd") == "a\\\nb\\\"cd";