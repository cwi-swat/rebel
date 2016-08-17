module analysis::TimeGenerator

import lang::smtlib25::AST;

import DateTime;
import IO;
import util::Math;

data TimeInterval
  = hours()
  | minutes()
  | seconds()
  ;

list[Command] generateDateTimeFunctions(datetime startDate, datetime endDate, TimeInterval interval = hours()) =
  [generateDateToIntFunction(startDate, endDate), 
   generateTimeToIntFunction(interval), 
   generateIsValidDateFunction(),
   generateIsValidTimeFunction()];

Command generateDateToIntFunction(datetime startDate, datetime endDate) =
  defineFunction("_dateToInt", [sortedVar("date", custom("Date"))], \int(), generateDateToIntBody(startDate, endDate));
  

Command generateTimeToIntFunction(TimeInterval interval) =
  defineFunction("_timeToInt", [sortedVar("time", custom("Time"))], \int(), generateTimeToIntBody(interval));

Command generateIsValidDateFunction() =
  defineFunction("_isValidDate", [sortedVar("date", custom("Date"))], \bool(), 
    and([
      gte(functionCall(simple("year"), [var(simple("date"))]), lit(intVal(1900))),
      lte(functionCall(simple("year"), [var(simple("date"))]), lit(intVal(2100))),
      gte(functionCall(simple("month"), [var(simple("date"))]), lit(intVal(1))),
      lte(functionCall(simple("month"), [var(simple("date"))]), lit(intVal(12))),
      gte(functionCall(simple("date"), [var(simple("date"))]), lit(intVal(1))),
      lte(functionCall(simple("date"), [var(simple("date"))]), lit(intVal(31))),
      not(eq(functionCall(simple("_dateToInt"), [var(simple("date"))]), neg(lit(intVal(1)))))
    ])    
  );
  
Command generateIsValidTimeFunction() =
  defineFunction("_isValidTime", [sortedVar("time", custom("Time"))], \bool(),
    and([
      gte(functionCall(simple("hour"), [var(simple("time"))]), lit(intVal(0))),
      lte(functionCall(simple("hour"), [var(simple("time"))]), lit(intVal(23))),
      gte(functionCall(simple("minutes"), [var(simple("time"))]), lit(intVal(0))),
      lte(functionCall(simple("minutes"), [var(simple("time"))]), lit(intVal(59))),
      gte(functionCall(simple("seconds"), [var(simple("time"))]), lit(intVal(0))),
      lte(functionCall(simple("seconds"), [var(simple("time"))]), lit(intVal(59)))
    ]));  
      
Formula generateDateToIntBody(datetime startDate, datetime endDate) {
  Formula body = neg(lit(intVal(1))); 
  datetime currentDate = endDate;
  
  for (int current <- [daysDiff(startDate, endDate)..0]) { 
    body = ite(eq(var(simple("date")), toSmtDate(currentDate)), lit(intVal(current)), body);  
    currentDate = decrementDays(currentDate);
  }
   
  return body;
}

Formula generateTimeToIntBody(TimeInterval interval) {
  Formula body = neg(lit(intVal(1)));
  
  for (int current <- [timeThreshold(interval)..0]) { 
    body = ite(eq(var(simple("time")), toSmtTime(current, interval)), lit(intVal(current)), body);
  }
  
  return body;
}

Formula toSmtDate(datetime date) =
  lit(adt("consDate", [lit(intVal(date.day)),lit(intVal(date.month)),lit(intVal(date.year))]));
  
Formula toSmtTime(int current, hours()) =
  lit(adt("consTime", [lit(intVal(current)), lit(intVal(0)), lit(intVal(0))]));  
  
Formula toSmtTime(int current, minutes()) =
  lit(adt("consTime", [lit(intVal(floor(current / 60))), lit(intVal(current % 60)), lit(intVal(0))]));

Formula toSmtTime(int current, seconds()) {
  int hour = floor(current / 3600);
  int minutes = floor((current - (hour * 3600)) / 60);
  int seconds = current - (hour * 3600 + minutes * 60); 
  
  return lit(adt("consTime", [lit(intVal(hour)), lit(intVal(minutes)), lit(intVal(seconds))]));
}

int timeThreshold(hours()) = 24;
int timeThreshold(minutes()) = 1440; // nr of minutes in a day
int timeThreshold(seconds()) = 86400; // nr of seconds in a day