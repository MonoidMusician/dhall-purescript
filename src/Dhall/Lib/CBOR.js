exports.encode = function(r) {
  return require("../../lib/cbor-js/cbor.js").encode(r);
};
exports.decode = function(r) {
  return require("../../lib/cbor-js/cbor.js").decode(r);
};
