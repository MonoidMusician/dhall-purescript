exports.encode = function(r) {
  return require("cbor-js").encode(r);
};
exports.decode = function(r) {
  return require("cbor-js").decode(r);
};
