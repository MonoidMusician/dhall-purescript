exports.encode = function(r) {
  return require("../../lib/cbor-js/cbor.js").encode(r);
};
exports.decode = function(r) {
  return require("../../lib/cbor-js/cbor.js").decode(r);
};
exports.mkDecimal = function(r) {
  return new (require("../../lib/cbor-js/cbor.js").Decimal)(r);
};
exports.unDecimal = function(r) {
  return { exponent: r.exponent, mantissa: r.mantissa };
};
