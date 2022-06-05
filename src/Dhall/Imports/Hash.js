import sjcl from "sjcl"
export function sha256(data) {
  return sjcl.codec.hex.fromBits(sjcl.hash.sha256.hash(sjcl.codec.arrayBuffer.toBits(data)));
}
