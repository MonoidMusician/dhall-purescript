export function getEnv() {
  return process.env;
}

export function responseHeaders(resp) {
  var obj = {};
  Array.from(resp.headers.entries()).forEach(function(item) {
    obj[item[0]] = item[1];
  });
  return obj;
}

export function unsafeDecode(just) {
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
}

export function windowFetch() {
  return window.fetch;
}

export function nodeFetch() {
  return import("node-fetch");
}
