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

exports.windowFetch = function() {
  return window.fetch;
};

exports.nodeFetch = function() {
  return require("node-fetch").default;
};
