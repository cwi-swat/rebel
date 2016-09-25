"use strict"

var SpecificationService = function() {
  var loadSpec = function(specId, openInEditor, callback) {
    $.ajax({
      url: "/rest/spec/" + specId + "?openInEditor=" + openInEditor
    }).then(function(data) {
        callback(data);
//        poll(data.spec, callback);
    });
  }

  var poll = function(spec, callback) {
    $.ajax({
      url: "/rest/spec/lastupdate/" + spec.fqn
    }).then(function(data) {
      if ("spec" in data && data.spec != spec) {
        spec = data.spec;
        callback(data);
      }

      setTimeout(function() {poll(spec,callback);}, 1000);
    })
  }

  return {
    load: loadSpec,
  }
}();
