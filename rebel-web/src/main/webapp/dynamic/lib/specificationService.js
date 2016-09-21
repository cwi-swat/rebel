"use strict"

var SpecificationService = function() {
  var loadSpec = function(specId, callback) {
    $.ajax({
      url: "/rest/spec/" + specId
    }).then(function(data) {
        callback(data);
    });
  }

  return {
    load: loadSpec
  }
}();
