module analysis::SmtResponseTranslator

import lang::smtlib25::Syntax;
import lang::smtlib25::response::Syntax;
import lang::smtlib25::response::Parser;

import solver::SolverRunner;

import String;
import util::Math;

str parseSmtResponse(str smtOutput) {
  Response resp = parseResponse(smtOutput);
  
  if ((Response)`((<Formula _> <Formula newVal>))` := resp) {
    return formatAsRebelLit(newVal);
  } 
  
  throw "Unable to parse new value";
}

list[str] parseSmtUnsatCore(str unsatCoreOutput) {
  Response resp = parseResponse(unsatCoreOutput);
  
  list[str] result = [];
  
  if ((Response)`<GetUnsatCore unsatCore>` := resp, Labell l <- unsatCore.labels) {
    result += "<l>";
  }
  
  return result;
}

str formatAsRebelLit((Formula)`(consDate <Formula date> <Formula month>)`) = "<date> <formatMonth(toInt("<month>"))>";
str formatAsRebelLit((Formula)`(consDate <Formula date> <Formula month> <Formula year>)`) = "<date> <formatMonth(toInt("<month>"))> <year>";

str formatAsRebelLit((Formula)`(consTime <Formula hour> <Formula minutes>)`) = "<hour>:<minutes>";
str formatAsRebelLit((Formula)`(consTime <Formula hour> <Formula minutes> <Formula seconds>)`) = "<hour>:<minutes>:<seconds>";

str formatAsRebelLit((Formula)`(consDateTime <Formula date> <Formula time>)`) = "<formatAsRebelLit(date)>, <formatAsRebelLit(time)>";

str formatAsRebelLit((Formula)`(consIBAN <String cc> <Formula checksum> <String nr>)`) = "<cc.val><left("<checksum>", 2, "0")><nr.val>";
str formatAsRebelLit((Formula)`(consMoney <String currency> <Formula amount>)`) = "<currency.val><floor(toInt("<amount>") / 100)>.<left("<toInt("<amount>") % 100>", 2, "0")>";

default str formatAsRebelLit((Formula)`<Formula f>`) = "<f>";


str formatMonth(1)  = "Jan";
str formatMonth(2)  = "Feb";
str formatMonth(3)  = "Mar";
str formatMonth(4)  = "Apr";
str formatMonth(5)  = "May";
str formatMonth(6)  = "Jun";
str formatMonth(7)  = "Jul";
str formatMonth(8)  = "Aug";
str formatMonth(9)  = "Sep";
str formatMonth(10) = "Oct";
str formatMonth(11) = "Nov";
str formatMonth(12) = "Dec";
