module analysis::SmtResponseTranslator

import lang::smtlib25::response::Syntax; 
import lang::smtlib25::response::Parser; 
  
import String;
import util::Math; 
import IO;
 
str parseSmtResponse(str smtOutput, str (int) stringConstantLookup) {
  GetValue resp = [GetValue]"<smtOutput>"; 
  
  if ((GetValue)`((<Formula _> <Formula newVal>))` := resp) {
    str result = formatAsRebelLit(newVal, stringConstantLookup); 
    return result;  
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

str formatAsRebelLit((Formula)`(consDate <Formula date> <Formula month>)`, str (int) scl) = "<date> <formatMonth(toInt("<month>"))>";
str formatAsRebelLit((Formula)`(consDate <Formula date> <Formula month> <Formula year>)`, str (int) scl) = "<date> <formatMonth(toInt("<month>"))> <year>";

str formatAsRebelLit((Formula)`(consTime <Formula hour> <Formula minutes>)`, str (int) scl) = "<hour>:<minutes>";
str formatAsRebelLit((Formula)`(consTime <Formula hour> <Formula minutes> <Formula seconds>)`, str (int) scl) = "<hour>:<minutes>:<seconds>";

str formatAsRebelLit((Formula)`(consDateTime <Formula date> <Formula time>)`, str (int) scl) = "<formatAsRebelLit(date, scl)>, <formatAsRebelLit(time, scl)>";

str formatAsRebelLit((Formula)`(consIBAN <Formula cc> <Formula checksum> <Formula nr>)`, str (int) scl) = "<scl(toInt("<cc>"))><right("<checksum>", 2, "0")><scl(toInt("<nr>"))>";

str formatAsRebelLit((Formula)`(consMoney <Formula currency> <Formula amount>)`, str (int) scl) = "<scl(toInt("<currency>"))><floor(am / 100)>.<left("<am % 100>", 2, "0")>" 
  when (Formula)`<Int a>` := amount,
       int am := toInt("<a>");

str formatAsRebelLit((Formula)`(consMoney <Formula currency> <Formula amount>)`, str (int) scl) = "- <scl(toInt("<currency>"))><floor(am / 100)>.<left("<am % 100>", 2, "0")>"
  when (Formula)`(- <Int a>)` := amount,
       int am := toInt("<a>"); 

default str formatAsRebelLit((Formula)`<Formula f>`, str (int) scl) = "<f>";

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
