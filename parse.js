const nearley = require("nearley");
const grammar = require("./grammar.js");

module.exports.parse = function(s) {
  // Create a Parser object from our grammar.
  const parser = new nearley.Parser(nearley.Grammar.fromCompiled(grammar));
  try {
    parser.feed(s);
    return parser.results;
  } catch (err) {
    return null;
  }
}
