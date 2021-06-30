exports.getEnv = function() {
  return process.env;
};

exports.responseHeaders = function(resp) {
  var obj = {};
  Array.from(resp.headers.entries()).forEach(function(item) {
    obj[item[0]] = item[1];
  });
  return obj;
};

exports.unsafeDecode = function(just) {
  return function(nothing) {
    return function(s) {
      try {
        var r = new TextDecoder("utf-8", { fatal: true }).decode(s);
        return just(r);
      } catch(e) {
        return nothing;
      }
    };
  };
};

exports.windowFetch = function() {
  return window.fetch;
};

exports.nodeFetch = function() {
  return require("node-fetch").default;
};
