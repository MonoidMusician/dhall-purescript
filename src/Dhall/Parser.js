const nearley = require("nearley");
const grammar = require("../../grammar.js");

exports.parseImpl = function(s) {
  const parser = new nearley.Parser(nearley.Grammar.fromCompiled(grammar));
  try {
    parser.feed(s);
    return parser.results;
  } catch (err) {
    return null;
  }
}
