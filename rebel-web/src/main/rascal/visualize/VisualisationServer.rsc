module visualize::VisualisationServer

import lang::Builder;

import util::Webserver;
import util::Maybe;
import IO;
import Message;
import String;
import Boolean; 

import visualize::ModelGenerator;
import visualize::ADT; 
import visualize::SimulationWrapper;
 
import web::Uri;

import analysis::Simulator;
import analysis::SimulationLoader;

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

Request rewrite(rq:get(str path)) = get([URI]"<path>", headers = rq.headers, parameters = rq.parameters); 
Request rewrite(rq:post(str path, Body b)) = post([URI]"<path>", b, headers = rq.headers, parameters = rq.parameters); 

ShutdownHandle serve(loc rebelBaseDir, AppConfig config = appConfig()) {
  AppRunContext ctx = appContext(rebelBaseDir, config);
  
  Response handleInternal(Request req) = handle(rewrite(req), ctx);
  serve(config.baseUrl, handleInternal);
   
  void sd() { shutdown(config.baseUrl); }
  return sd;  
}

Response handle(get((URI)`/vis`), AppRunContext ctx) = fileResponse(getStaticFile("visualize.html", ctx), mimeTypes["html"], ());
Response handle(get((URI)`/sim`), AppRunContext ctx) = fileResponse(getStaticFile("simulate.html", ctx), mimeTypes["html"], ());

Response handle(get((URI)`/static/<{Part "/"}* path>/<Part file>`), AppRunContext ctx) = fileResponse(getStaticFile("<path>/<file>", ctx), mimeTypes[getExtension("<file>")], ()) when staticFileExists("<path>/<file>", ctx);

Response handle(get((URI)`/rest/spec`), AppRunContext ctx) = jsonResponse(ok(), (), listSpecifications(ctx.rebelBaseDir));

Response handle(get((URI)`/rest/sim/start/<Part spec>`), AppRunContext ctx) 
  = jsonResponse(ok(), (), getInitialConfiguration(specLoc))
  when loc specLoc := resolveSpec("<spec>", ctx);

Response handle(req:post((URI)`/rest/sim/start/<Part spec>`, Body b), AppRunContext ctx) 
  = jsonResponse(ok(), (), toWeb(constructInitialState(cfg)))
  when SimConfig cfg := b(#SimConfig);
  
Response handle(get((URI)`/rest/sim/fire/<Part spec>/<Part event>`), AppRunContext ctx) 
  = jsonResponse(ok(), (), toWeb(getTransitionParams(specLoc, "<event>")))
  when loc specLoc := resolveSpec("<spec>", ctx); 

alias StateAndVars = tuple[State state, Variables vars];

Response handle(post((URI)`/rest/sim/fire/<Part spec>/<Part event>`, Body b), AppRunContext ctx) {
  if (StateAndVars sav := b(#StateAndVars)) {
    loc specLoc = resolveSpec("<spec>", ctx);
     
    TransitionResult result = transition(specLoc, "<spec>", "<event>", toSim(sav.vars), toSim(sav.state));
    
    switch(result) {
      case successful(State next): return jsonResponse(ok(), (), toWeb(next));
      case failed(list[str] failingStatements): return jsonResponse(badRequest(), (), failingStatements);
    } 
  }
}

Response handle(req:get((URI)`/rest/spec/<Part spec>`), AppRunContext ctx) { 
  str path = replaceAll("<spec>", ".", "/");
  
  if (specExists(path, ctx), just(JsSpec model) := generateForDynamic(getSpecFile(path, ctx))) {
    if ("openInEditor" in req.parameters && fromString(req.parameters["openInEditor"])) {
      edit(getSpecFile(path, ctx));
    }

    return jsonResponse(ok(), (), model);
  } 

  return response(notFound(), "Unable to load specification");
} 

private loc resolveSpec(str spec, AppRunContext ctx) = getSpecFile(path, ctx)
  when str path := replaceAll("<spec>", ".", "/"),
       specExists(path, ctx);  

default Response handle(get(URI uri), AppRunContext ctx) = response(notFound(), "Get of <uri> is not found on server");
default Response handle(post(URI uri, Body b), AppRunContext ctx) = response(notFound(), "Post to <uri> with this body content not found");

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