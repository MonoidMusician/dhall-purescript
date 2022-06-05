import bigInteger from 'big-integer';
export function unsafeNumber(n) {
  return new Number(n);
}
export function unsafeFromNumber(just) {
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
export function unsafeFromBigInt(just) {
  return function(nothing) {
    return function(n) {
      if (bigInteger.isInstance(n)) {
        return just(n);
      } else {
        return nothing(n);
      }
    }
  }
}
