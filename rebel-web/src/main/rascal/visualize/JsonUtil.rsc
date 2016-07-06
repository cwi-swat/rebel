module visualize::JsonUtil

import IO;
import String;

str jsonEsc(str s) = (s | func(it) | func <- escapeFunctions());

set[str(str)] escapeFunctions() = { 
	jsonEscapeControlN, jsonEscapeControlB, jsonEscapeControlF, 
	jsonEscapeControlR, jsonEscapeControlT, 
	jsonEscapeDoubleQuote, jsonEscapeSingleQuote, jsonEscapeBackslash
};

str jsonEscapeControlN(str s) = replaceAll(s, "\n", "\\n");
str jsonEscapeControlB(str s) = replaceAll(s, "\b", "\\b");
str jsonEscapeControlF(str s) = replaceAll(s, "\f", "\\f");
str jsonEscapeControlR(str s) = replaceAll(s, "\r", "\\r");
str jsonEscapeControlT(str s) = replaceAll(s, "\t", "\\t");

str jsonEscapeDoubleQuote(str s) = replaceAll(s, "\"", "\\\"");
str jsonEscapeSingleQuote(str s) = replaceAll(s, "\'", "\\\'");
str jsonEscapeBackslash(str s) = replaceAll(s, "\\", "\\\\");