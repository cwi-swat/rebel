module web::Uri

start syntax Top = URI;

lexical URI = absolute: "/" {Part "/"}* parts;

lexical Part = @category="Constant" String; //[A-Za-z][A-Za-z0-9\-._%]*;
  //= @category="Constant" String
  //| @category="Constant" Int
  //> @category="Type" File
  //; 

lexical File = [A-Za-z][A-Za-z0-9\-._%]* file "." [A-Za-z0-9%]+$ extension;
lexical String = [A-Za-z][A-Za-z0-9\-._%]*;
lexical Int = [0-9]+;