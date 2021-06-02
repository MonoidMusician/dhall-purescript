exports.unsafeNumber = function(n) {
  return new Number(n);
}
exports.unsafeFromNumber = function(just) {
  return function(nothing) {
    return function(n) {
      if (n instanceof Number) {
        return just(n.valueOf());
      } else {
        return nothing(n);
      }
    }
  }
}
exports.unsafeFromBigInt = function(just) {
  return function(nothing) {
    return function(n) {
      if (require("big-integer").isInstance(n)) {
        return just(n);
      } else {
        return nothing(n);
      }
    }
  }
}
