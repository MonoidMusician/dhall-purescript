import cbor from "../../lib/cbor-js/cbor.js"
export function encode(r) {
  return cbor.encode(r);
}
export function decode(r) {
  return cbor.decode(r);
}
export function mkDecimal(r) {
  return new cbor.Decimal(r);
}
export function unDecimal(r) {
  return { exponent: r.exponent, mantissa: r.mantissa };
}
