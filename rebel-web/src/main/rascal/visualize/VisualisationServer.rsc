module visualize::VisualisationServer

import lang::Builder;

import util::Webserver;
import util::Maybe;
import IO;
import Message;
import String;

import visualize::ModelGenerator;
import visualize::ADT; 
import web::Uri;

import util::Editors;

data AppConfig = appConfig(loc baseUrl = |http://localhost:9001|, loc staticFileBase = |project://rebel-web/src/main/webapp/dynamic|);
data AppRunContext = appContext(loc rebelBaseDir, AppConfig config);

alias ShutdownHandle = void ();

data Request 
  = get(URI uri)
  | put (URI uri, Body content)
  | post(URI uri, Body content)
  | delete(URI uri)
  | head(URI uri)
  ;

Request rewrite(get(str path)) = get([URI]"<path>"); 

ShutdownHandle serve(loc rebelBaseDir, AppConfig config = appConfig()) {
  AppRunContext ctx = appContext(rebelBaseDir, config);
  
  Response handleInternal(Request req) = handle(rewrite(req), ctx);

  serve(config.baseUrl, handleInternal);
   
  void sd() { shutdown(config.baseUrl); }
  return sd;  
}

Response handle(get((URI)`/`), AppRunContext ctx) = fileResponse(getStaticFile("index.html", ctx), mimeTypes["html"], ());
Response handle(get((URI)`/static/<{Part "/"}* path>/<Part file>`), AppRunContext ctx) = fileResponse(getStaticFile("<path>/<file>", ctx), mimeTypes[getExtension("<file>")], ()) when staticFileExists("<path>/<file>", ctx);

Response handle(get((URI)`/rest/spec`), AppRunContext ctx) = jsonResponse(ok(), (), listSpecifications(ctx.rebelBaseDir));

Response handle(get((URI)`/rest/spec/<Part spec>`), AppRunContext ctx) { 
  str path = replaceAll("<spec>", ".", "/");
  
  if (specExists(path, ctx), just(JsSpec model) := generateForDynamic(getSpecFile(path, ctx))) {
    edit(getSpecFile(path, ctx));

    return jsonResponse(ok(), (), model);
  } 

  return response(notFound(), "Unable to load specification");
} 

default Response handle(get(URI uri), AppRunContext ctx) = response(notFound(), "<uri> is not found on server");

private str getExtension(/^.*[.]<ext:.*>$/) = ext;

private list[str] listSpecifications(loc base) {
  list[str] specs = [];
  
  if (isFile(base) && base.extension == "ebl") {
    tuple[set[Message], Maybe[Built]] result = load(base);
    
    if (just(Built b) := result<1>, b.inlinedMod has spec) {
      return ["<b.inlinedMod.modDef.fqn>"];
    }
  } else if (isDirectory(base)) {
    for (loc f <- base.ls) {
      specs += listSpecifications(f);
    }
  }      

  return specs;  
}

private loc getStaticFile(str file, AppRunContext ctx) = ctx.config.staticFileBase + file;
private loc getSpecFile(str file, AppRunContext ctx) = (ctx.rebelBaseDir + file)[extension = "ebl"];

private bool staticFileExists(str file, AppRunContext ctx) = exists(getStaticFile(file, ctx));
private bool specExists(str file, AppRunContext ctx) = exists(getSpecFile(file, ctx));