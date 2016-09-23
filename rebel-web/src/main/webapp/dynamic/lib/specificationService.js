"use strict"

var SpecificationService = function() {
  var loadSpec = function(specId, callback) {
    $.ajax({
      url: "/rest/spec/" + specId
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
