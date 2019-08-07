exports.eqArrayBuffer = function(a) {
  return function(b) {
    return arrayBuffersAreEqual(a, b);
  }
}

// compare ArrayBuffers
function arrayBuffersAreEqual(a, b) {
  return dataViewsAreEqual(new DataView(a), new DataView(b));
}

// compare DataViews
function dataViewsAreEqual(a, b) {
  if (a.byteLength !== b.byteLength) return false;
  for (var i=0; i < a.byteLength; i++) {
    if (a.getUint8(i) !== b.getUint8(i)) return false;
  }
  return true;
}
