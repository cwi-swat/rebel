"use strict"

var SpecificationService = function() {
  var loadSpec = function(specId) {
    $.ajax({
      url: "/rest/spec/" + specId
    }).then(function(data) {
        return data
    });
  }
}();
