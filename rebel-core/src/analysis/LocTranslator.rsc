module analysis::LocTranslator

import String;
import ValueIO;

str locToStr(loc l) = replace(l);
loc strToLoc(str locStr) = replace(locStr); 

str replace(loc l) {
	str locStr = "<l>";
	locStr = replaceAll(locStr, "|", "_");
	locStr = replaceAll(locStr, "\<", "$");
	locStr = replaceAll(locStr, "\>", "%");
	locStr = replaceAll(locStr, "(", "[");
	locStr = replaceAll(locStr, ")", "]");
	
	return "|<locStr>|";
}

loc replace(str locStr) {
	if (/^\|_<scheme:.*>:\/\/<file:.*>_\[<os:[0-9]*>,<oe:[0-9]*>,\$<bl:[0-9]*>,<bc:[0-9]*>\%,\$<el:[0-9]*>,<ec:[0-9]*>\%\]\|$/ := locStr) {
		return readTextValueString(#loc, "|<scheme>://<file>|(<os>,<oe>,\<<bl>,<bc>\>,\<<el>,<ec>\>)");
		
	} else {
		throw "\'<locStr>\' could not be translated to a loc";
	}	
}

