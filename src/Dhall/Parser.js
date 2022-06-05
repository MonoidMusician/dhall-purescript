import { Parser, Grammar } from "nearley";
import grammar from "../../grammar.js";

export function parseImpl(s) {
  const parser = new Parser(Grammar.fromCompiled(grammar));
  try {
    parser.feed(s);
    return parser.results;
  } catch (err) {
    return null;
  }
}
