import nearley from "nearley";
import grammar from "../../grammar.js";

export function parseImpl(s) {
  const parser = new nearley.Parser(nearley.Grammar.fromCompiled(grammar));
  try {
    parser.feed(s);
    return parser.results;
  } catch (err) {
    return null;
  }
}
