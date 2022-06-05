export function encode(r) {
  return require("../../lib/cbor-js/cbor.js").encode(r);
}
export function decode(r) {
  return require("../../lib/cbor-js/cbor.js").decode(r);
}
export function mkDecimal(r) {
  return new (require("../../lib/cbor-js/cbor.js").Decimal)(r);
}
export function unDecimal(r) {
  return { exponent: r.exponent, mantissa: r.mantissa };
}
