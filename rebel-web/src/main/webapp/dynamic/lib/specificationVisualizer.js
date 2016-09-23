"use strict"

var SpecRenderer = function() {
  var Specification = function(fqn, name, documentation, modifier, inheritsFrom, extendedBy, fields, events, states, transitions, externalMachines, transitionsToExternalMachines, transitionsFromExternalMachines) {
    this.fqn = fqn,
    this.name = name,
    this.doc = documentation,
    this.modifier = modifier;
    this.inheritsFrom = inheritsFrom;
    this.extendedBy = extendedBy;
    this.fields = fields;
    this.events = events;
    this.states = states;
    this.transitions = transitions;
    this.externalMachines = externalMachines;
    this.transitionsToExternalMachines = transitionsToExternalMachines;
    this.transitionsFromExternalMachines = transitionsFromExternalMachines;
  }

  function buildGraph(specification) {
    function hasState(state) {
      return specification.states.find(function (elem) {
        if ("finalState" in elem) return elem.finalState.name == state;
        else if ("initialState" in elem) return elem.initialState.name == state;
        else return elem.state.name == state;
      }) !== undefined;
    }

    function hasEvent(event) {
      return specification.events.find(function (elem) { return elem.event.id == event;}) !== undefined;
    }

    function hasExternalMachine(em) {
      return specification.externalMachines.find(function (elem) { return elem.externalMachine.fqn == em;}) !== undefined;
    }

    function guid() {
      function s4() {
        return Math.floor((1 + Math.random()) * 0x10000)
          .toString(16)
          .substring(1);
      }
      return s4() + s4() + '-' + s4() + '-' + s4() + '-' +
        s4() + '-' + s4() + s4() + s4();
    }

    // Create a new directed graph
    var g = new dagreD3.graphlib.Graph({compound: true}).setGraph({rankDir: "LR"});

    // Create group for specification
    var groupId = guid();
    var groupLabel = "<em>" + specification.name + "</em>";
    if ("extends" in specification.inheritsFrom) {
        groupLabel += "<span class='inheritsFrom'>inherits from <a href='#" + specification.inheritsFrom.extends.fqn + "'>" + specification.inheritsFrom.extends.name + "</a></span>";
    }

    if (specification.extendedBy.length > 0) {
      groupLabel += "<span class='extendedBy'>extended by ";
      specification.extendedBy.forEach(function(e, index) {
          groupLabel += "<a href='#" + e.extends.fqn + "'>" + e.extends.name + "</a>";
          groupLabel += index < specification.extendedBy.length - 1 ? ", " : "";
      });
    }

    console.log("Modifier = " + specification.modifier);

    groupLabel =  ("abstract" in specification.modifier ? "<p>&lt;&lt;abstract&gt;&gt;</p>" :
                  "external" in specification.modifier ? "<p>&lt;&lt;external&gt;&gt;</p>" :
                  "") + groupLabel;

    g.setNode(groupId, {
      labelType: "html",
      clusterLabelPos: "top",
      label: groupLabel
    });

    // add the fields of the specification
    if (specification.fields.length > 0) {
      var fieldsId = guid();
      var fieldsLabel = "<table><thead><tr><th>Fields</th></tr></thead><tbody>";
      specification.fields.forEach(function(f) {
        fieldsLabel += "<tr><td>" + f.field.name + ":</td><td>" + f.field.tipe + "</td></tr>";
      });
      fieldsLabel += "</tbody></table>";

      g.setNode(fieldsId, {
        labelType: "html",
        label: fieldsLabel,
        shape: "rect",
        class: "fields"});
      g.setParent(fieldsId, groupId);
    }

    // Add states
    specification.states.forEach(function(s) {
      var name, shape, labelStyle;
      if ("initialState" in s) {
        name = s.initialState.name;
        shape = "initial";
        labelStyle = "transform: translate(0,25px)";
      } else if ("finalState" in s) {
        name = s.finalState.name;
        shape = "final";
        labelStyle = "transform: translate(0,25px)";
      } else {
        name = s.state.name;
        shape = "rect";
        labelStyle - "";
      }

      var result = g.setNode(name, {label: name, shape: shape, labelStyle: labelStyle});
      g.setParent(name, groupId);
    });

    // add events
    specification.events.forEach(function(e) {
      g.setNode(e.event.id, {
        label: e.event.name,
        shape: "rect",
        class: "edgeNode",
        doc: "doc" in e.event ? e.event.doc : "",
        config: "config" in e.event ? e.event.config : [],
        params: "params" in e.event ? e.event.params : [],
        preconditions: "preconditions" in e.event ? e.event.preconditions : [],
        postconditions: "postconditions" in e.event ? e.event.postconditions : [],
        sync: "sync" in e.event ? e.event.sync : []});
      g.setParent(e.event.id, groupId);
    });

    function getLabelOfExternalMachine(e) {
      var label = "<a href='#" + e.fqn+ "'>" + e.name + "</a>";
      if("incoming" in e.referenceType) {
        label = "<p>&lt;&lt;is referenced by&gt;&gt;</p>" + label;
      } else if ("outgoing" in e.referenceType) {
        label = "<p>&lt;&lt;references&gt;&gt;</p>" + label;
      } else {
        label = "<p>&lt;both references and is referenced by&gt;&gt;</p>" + label;
      }

      return label;
    }

    // add external machines
    specification.externalMachines.forEach(function(e) {
      var rt;
      if ("incoming" in e.externalMachine.referenceType) {
        rt = "incoming";
      } else if ("outgoing" in e.externalMachine.referenceType) {
        rt = "outgoing";
      } else {
        rt = "both";
      }

      g.setNode(e.externalMachine.fqn, {
        labelType: "html",
        label: getLabelOfExternalMachine(e.externalMachine),
        class: "externalMachine " + rt,
        shape: "rect"
      });
    });

    // Set up internal edges
    specification.transitions.forEach(function(t) {
      if (hasState(t.trans.from) && hasState(t.trans.to) && hasEvent(t.trans.via)) {
        g.setEdge(t.trans.from, t.trans.via, {label: "", arrowhead: "undirected", lineInterpolate:"basis"});
        g.setEdge(t.trans.via, t.trans.to, {label: "", lineInterpolate:"basis"});
      }
    });

    // set up external edges
    specification.transitionsToExternalMachines.forEach(function(t) {
      if (hasEvent(t.transToExternal.from) && hasExternalMachine(t.transToExternal.toMachine)) {
        g.setEdge(t.transToExternal.from, t.transToExternal.toMachine, {class: "syncTo", lineInterpolate:"basis"});
      }
    });

    specification.transitionsFromExternalMachines.forEach(function(t) {
      if (hasEvent(t.transFromExternal.to) && hasExternalMachine(t.transFromExternal.fromMachine)) {
        g.setEdge(t.transFromExternal.fromMachine, t.transFromExternal.to, {class: "syncFrom", lineInterpolate:"basis"});
      }
    });


    return g;
  };

  var renderSpecification = function(specification, svgDomElement) {
    var g = buildGraph(specification);

    //d3.selectAll("svg > g > *").remove();
    svgDomElement.select("g").remove();
    svgDomElement.insert("g");

    var inner = svgDomElement.select("g");

    // Set up zoom support
    var zoom = d3.behavior.zoom().on("zoom", function() {
          inner.attr("transform", "translate(" + d3.event.translate + ")" +
                                      "scale(" + d3.event.scale + ")");
        });
    svgDomElement.call(zoom);

    // Create the renderer
    var render = new dagreD3.render();

    render.shapes().initial = function(parent, bbox, node) {
      var shapeSvg = parent.insert("circle")
            .attr("cx", 0)
            .attr("cy", -0)
            .attr("r", 10)
            .attr("class", "initial");

      node.intersect = function(point) {
        return dagreD3.intersect.circle(node, 10, point);
      };

      return shapeSvg;
    };

    render.shapes().final = function(parent, bbox, node) {
      var shapeSvg = parent.insert("g");

      shapeSvg.insert("circle")
        .attr("cx", 0)
        .attr("cy", 0)
        .attr("r", 10)
        .attr("stroke", "#000")
        .attr("fill-opacity", "0")
        .attr("class", "final");

      shapeSvg.insert("circle")
          .attr("cx", 0)
          .attr("cy", 0)
          .attr("r",  8)
          .attr("fill", "#000");

      node.intersect = function(point) {
        return dagreD3.intersect.circle(node, 10, point);
      };

      return shapeSvg;
    };

    var styleTooltip = function(edgeNode) {
      function createPart(title, items) {
        var result = "<h1>" + title + "</h1>";
        for (var i = 0; i < items.length; i++) {
          result += items[i];
        }
        return result;
      }

      function preprocessStatements(origItems) {
        var items = [];
        origItems.forEach(function(o) {
            var code = ("codeOnly" in o) ? o.codeOnly.code : o.docAndCode.code;
            var doc = ("docAndCode" in o) ? o.docAndCode.doc : "";

            var item = (doc !== "" ? "<p>" +  micromarkdown.parse(doc) + "</p>" : "") + micromarkdown.parse("```" + code + "```");

            items.push(item);
        });

        return items;
      }

      var content = edgeNode.doc !== "" ? edgeNode.doc + " \n" : "";

      if (edgeNode.params.length > 0) {
        var items = [];
        edgeNode.params.forEach(function(p) {
          items.push(micromarkdown.parse("```" + p.typeOnly.name + ": " + p.typeOnly.tipe + "```"));
        });
        content += createPart("Transition parameters", items);
      }
      content += edgeNode.preconditions.length > 0 ? createPart("Preconditions", preprocessStatements(edgeNode.preconditions)) : "";
      content += edgeNode.postconditions.length > 0 ? createPart("Postconditions", preprocessStatements(edgeNode.postconditions)) : "";
      content += edgeNode.sync.length > 0 ? createPart("Synchronized events", preprocessStatements(edgeNode.sync)) : "";

      return content;
    };

    // Run the renderer. This is what draws the final graph.
    render(inner, g);

    // Attach the tipsy pop-up to all edge nodes
    inner.selectAll("g.node.edgeNode")
      .attr("title", function(v) {
        return styleTooltip(g.node(v));
      })
      .each(function(v) {
          $(this).tipsy({ gravity: "w", opacity: 1, html: true});
      });

    var initialPlacement = function(svgViewport) {
      var viewportWidth = svgViewport.width();
      var viewportHeight = svgViewport.height();

      g.initialScale = 1;
      if (viewportWidth > g.graph().width) {
        if (viewportHeight < g.graph().height) {
          g.initialScale = (1 / (g.graph().height + 20)) * viewportHeight;
        }
      } else {
        g.initialScale = (1 / (g.graph().width + 20)) * viewportWidth;
      }

      zoom
        .translate([(viewportWidth - g.graph().width * g.initialScale) / 2,
            (viewportHeight - g.graph().height * g.initialScale) / 2])
        .scale(g.initialScale)
        .event(svgDomElement);
    }

    return {
      graph: g,
      initialPlacement: initialPlacement
    }
  }

  return {
    Specification: Specification,
    render: renderSpecification
  }
}();
