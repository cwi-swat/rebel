"use strict"

var SpecificationFinder = function(specs) {
  var findSpec = function(fqn) {
    var foundElement;
    specs.find(function (element, index, array) {
      if ("fqn" in element && element.fqn === fqn) {
        foundElement = element;
      };
    });

    return foundElement;
  }

  var createFlattenedSpecTree = function() {
    var items = [];

    specs.forEach(function (s) {
      items.push({label: s.fqn, url: s.fqn});
    });

    items.sort(function(a,b) {
      return (a.label < b.label) ? -1 : (a.label > b.label) ? 1 : 0;
    });

    return items;
  }

  return {
    findSpec: findSpec,
    getFlattenedSpecTree: createFlattenedSpecTree
  }
}
