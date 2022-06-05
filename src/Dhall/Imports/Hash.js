export function sha256(data) {
  var sjcl = require("sjcl");
  return sjcl.codec.hex.fromBits(sjcl.hash.sha256.hash(sjcl.codec.arrayBuffer.toBits(data)));
}
