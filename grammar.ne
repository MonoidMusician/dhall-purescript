# Converted from https://github.com/dhall-lang/dhall-lang/blob/master/standard/dhall.abnf

@{%
function binop(type, i=1) {
  return data => data[1].reduce((r, v) => ({ type, value: [r, v[i]] }), data[0]);
};

function nuller() { return null; }

const pass = n => d => d ? d[n] : null;
const pass0 = pass(0);
const pass1 = pass(1);

const tag = type => value => ({ type, value });

function flatten(items) {
  const flat = [];

  items.forEach(item => {
    if (Array.isArray(item)) {
      flat.push(...flatten(item));
    } else {
      flat.push(item);
    }
  });

  return flat;
}

function collapse(items) {
  var flat = "";

  items.forEach(item => {
    if (Array.isArray(item)) {
      flat += collapse(item);
    } else if (item != null) {
      flat += item;
    }
  });

  return flat;
}

function remove_common_prefix(items) {
  // Function to iterate through each character (or interpolation) in a string
  function iterate(iterator) {
    items.forEach(function(str) {
      if (typeof str === "string") {
        // Array.from respects CodePoints
        Array.from(str).forEach(iterator);
      } else {
        iterator(str);
      }
    });
  }
  // First we gather a list of all of the prefixes
  var prefixes = [];
  // current_prefix:
  //   - null means we have stopped scanning for this line
  //   - string means we are actively scanning this line, indicates what
  //     spaces and tabs have been found thus far
  var current_prefix = "";
  function gather_prefixes(char) {
    // Reset the current_prefix indicator, but do not add to prefixes
    // (if line was non-empty, that would have happened already)
    if (char === "\n") {
      current_prefix = "";
    // If still scanning...
    } else if (current_prefix !== null) {
      // A tab or space gets added to the current prefix
      if (char === "\t" || char === " ") {
        current_prefix += char;
      // Anything else (including interpolation) stops scanning this line,
      // flushing the current prefix to the list.
      } else {
        prefixes.push(current_prefix);
        current_prefix = null;
      }
    }
  }
  iterate(gather_prefixes);
  // Flush out any remaining prefix (right before the close quotes)
  gather_prefixes(null);
  // Now we calculate the common prefix
  var common_prefix = prefixes.reduce(function(a, b) {
    var common = "";
    while (a.length && b.length) {
      if (a[0] === b[0]) {
        common += a[0];
        a = a.substring(1);
        b = b.substring(1);
      } else break;
    }
    return common;
  });
  // Now we remove the common prefixes, building the new result
  var result = [];
  // prefix_removal indicates the next chars to remove, if possible
  var prefix_removal = common_prefix;
  function remove_prefixes(char) {
    var keep = true;
    // Reset the prefix on the new line
    if (char === "\n") {
      prefix_removal = common_prefix;
    // If we can still remove a prefix character
    } else if (prefix_removal !== "") {
      // Drop this element if it matches, and advance to the next char in the
      // common prefix
      if (char === prefix_removal[0]) {
        keep = false;
        prefix_removal = prefix_removal.substring(1);
      // Otherwise keep it but cancel removing any more (probably unreachable)
      } else {
        prefix_removal = "";
      }
    }
    if (keep) result.push(char);
  }
  iterate(remove_prefixes);
  return result;
}

const keyword =
  [ "if"
  , "then"
  , "else"
  , "let"
  , "in"
  , "using"
  , "missing"
  , "as"
  , "Infinity"
  , "NaN"
  , "merge"
  , "Some"
  , "toMap"
  , "assert"
  , "forall"
  , "with"
  ];

const builtin =
  [ "Type"
  , "Kind"
  , "Sort"
  , "Bool"
  , "True"
  , "False"
  , "missing"
  , "Natural"
  , "Natural/fold"
  , "Natural/build"
  , "Natural/isZero"
  , "Natural/even"
  , "Natural/odd"
  , "Natural/toInteger"
  , "Natural/show"
  , "Natural/subtract"
  , "Integer"
  , "Integer/show"
  , "Integer/toDouble"
  , "Integer/negate"
  , "Integer/clamp"
  , "Double"
  , "Double/show"
  , "Text"
  , "Text/show"
  , "Text/replace"
  , "List"
  , "List/build"
  , "List/fold"
  , "List/length"
  , "List/head"
  , "List/last"
  , "List/indexed"
  , "List/reverse"
  , "Optional"
  , "None"
  ];
%}

# This just adds surrounding whitespace for the top-level of the program
complete_expression -> shebang:* whsp expression whsp {% pass(2) %}

end_of_line -> [\n] {% pass0 %} | [\r] [\n] {% () => "\n" %}
tab -> [\t] {% pass0 %}

ascii -> [\x20-\x7F] {% pass0 %}

# This rule matches all characters that are not:
#
# * not ASCII
# * not part of a surrogate pair
# * not a "non-character"
valid_non_ascii ->
    [\x80-\uD7FF\uE000-\uFFFD] {% collapse %}
  | [\uD800-\uD83E\uD840-\uD87E\uD880-\uD8BE\uD8C0-\uD8FE\uD900-\uD93E\uD940-\uD97E\uD980-\uD9BE\uD9C0-\uD9FE\uDA00-\uDA3E\uDA40-\uDA7E\uDA80-\uDABE\uDAC0-\uDAFE\uDB00-\uDB3E\uDB40-\uDB7E\uDB80-\uDBBE\uDBC0-\uDBFE] [\uDC00-\uDFFF] {% collapse %}
  | [\uD83F\uD87F\uD8BF\uD8FF\uD93F\uD97F\uD9BF\uD9FF\uDA3F\uDA7F\uDABF\uDAFF\uDB3F\uDB7F\uDBBF\uDBFF] [\uDC00-\uDFFD] {% collapse %}

# Note: block comments can be nested
block_comment -> "{-" block_comment_continue

block_comment_char -> [\x20-\x7A\x7C-\x7F] | ( [\x7B] ( [\x20-\x2c\x2e-\x7F] | valid_non_ascii | tab | end_of_line ) ) | valid_non_ascii | tab | end_of_line

# FIXME
block_comment_continue ->
    "-}"
  | block_comment block_comment_continue
  | block_comment_char block_comment_continue

not_end_of_line -> ascii | valid_non_ascii | tab

# NOTE: Slightly different from Haskell-style single-line comments because this
# does not require a space after the dashes
line_comment -> "--" not_end_of_line:* end_of_line

whitespace_chunk ->
      " " {% nuller %}
    | tab {% nuller %}
    | end_of_line {% nuller %}
    | line_comment {% nuller %}
    | block_comment {% nuller %}

whsp -> whitespace_chunk:* {% nuller %}

# nonempty whitespace
whsp1 -> whitespace_chunk:+ {% nuller %}

# Uppercase or lowercase ASCII letter
ALPHA -> [A-Za-z] {% pass0 %}

# ASCII digit
DIGIT -> [0-9] {% pass0 %}

ALPHANUM -> ALPHA {% pass0 %} | DIGIT {% pass0 %}

HEXDIG -> DIGIT {% pass0 %} | [Aa] {% pass0 %} | [Bb] {% pass0 %} | [Cc] {% pass0 %} | [Dd] {% pass0 %} | [Ee] {% pass0 %} | [Ff] {% pass0 %}

# A simple label cannot be one of the reserved keywords
# listed in the `keyword` rule.
# A PEG parser could use negative lookahead to
# enforce this, e.g. as follows:
# simple-label =
#       keyword 1*simple-label-next-char
#     / !keyword (simple-label-first-char *simple-label-next-char)
simple_label_first_char -> ALPHA {% pass0 %} | "_" {% pass0 %}
simple_label_next_char ->
    ALPHANUM {% pass0 %}
  | "-" {% pass0 %}
  | "/" {% pass0 %}
  | "_" {% pass0 %}
simple_label ->
  simple_label_first_char simple_label_next_char:*
  {% (d, _, reject) => {
    let r = d[0] + d[1].join("");
    return keyword.includes(r) ? reject : r;
  } %}

quoted_label_char -> [\x20-\x5F\x61-\x7E]
quoted_label -> quoted_label_char:* {% collapse %}

# NOTE: Dhall does not support Unicode labels, mainly to minimize the potential
# for code obfuscation
label -> ("`" quoted_label "`" {% pass1 %} | simple_label {% pass0 %}) {% pass0 %}

# A nonreserved-label cannot not be any of the reserved identifiers for builtins
# (unless quoted).
# Their list can be found in the `builtin` rule.
# The only place where this restriction applies is bound variables.
# A nonreserved-label also cannot start with sha256-prefix.  This would be true
# anyway since that contains a `:` but a PEG parser may want to explicitly
# look for this case to avoid greedily matching the start of the prefix.
# A PEG parser could use negative lookahead to avoid parsing those identifiers,
# e.g. as follows:
# nonreserved-label =
#      builtin 1*simple-label-next-char
#    / !(builtin / sha256-prefix) label
nonreserved_label -> ("`" quoted_label "`" {% pass1 %} | simple_label {% (d, _, reject) => builtin.includes(d[0]) ? reject : d[0] %}) {% pass0 %}

# An any_label is allowed to be one of the reserved identifiers (but not a keyword).
any_label -> label {% pass0 %}

# Allow specifically `Some` in record and union labels.
any_label_or_some -> any_label {% pass0 %} | Some {% pass0 %}

# Dhall's double-quoted strings are similar to JSON strings (RFC7159) except:
#
# * Dhall strings support string interpolation
#
# * Dhall strings also support escaping string interpolation by adding a new
#   `\$` escape sequence
#
# * Dhall strings also allow Unicode escape sequences of the form `\u{XXX}`
double_quote_chunk ->
      double_quote_literal_chunk (interpolation double_quote_literal_chunk):*
        {% d => [d[0]].concat(...d[1]) %}

double_quote_literal_chunk ->
    ( "\\" double_quote_escaped {% pass1 %}
    | double_quote_char {% pass0 %}
    ):* {% d => d[0].join("") %}

double_quote_escaped ->
  ( [\x22\x24\x5C\x2F] {% pass0 %}
  | [\x62] {% () => "\x08" %}
  | [\x66] {% () => "\x0C" %}
  | [\x6E] {% () => "\x0A" %}
  | [\x72] {% () => "\x0D" %}
  | [\x74] {% () => "\x09" %}
  | "u" unicode_escape {% pass1 %}
  ) {% pass0 %}

# Valid Unicode escape sequences are as follows:
#
# * Exactly 4 hexadecimal digits without braces:
#       `\uXXXX`
# * 1-6 hexadecimal digits within braces (with optional zero padding):
#       `\u{XXXX}`, `\u{000X}`, `\u{XXXXX}`, `\u{00000XXXXX}`, etc.
#   Any number of leading zeros are allowed within the braces preceding the 1-6
#   digits specifying the codepoint.
#
# From these sequences, the parser must also reject any codepoints that are in
# the following ranges:
#
# * Surrogate pairs: `%xD800-DFFF`
# * Non-characters: `%xNFFFE-NFFFF` / `%x10FFFE-10FFFF` for `N` in `{ 0 .. F }`
#
# See the `valid-non-ascii` rule for the exact ranges that are not allowed
unicode_escape ->
    unbraced_escape
    {% d => String.fromCharCode(parseInt(d[0], 16)) %}
  | "{" braced_escape "}"
    {% d => String.fromCodePoint(parseInt(d[1], 16)) %}

# All valid last 4 digits for unicode codepoints (outside Plane 0): `0000-FFFD`
unicode_suffix ->
    (DIGIT | [A-E]) HEXDIG HEXDIG HEXDIG {% collapse %}
  | "F" HEXDIG HEXDIG (DIGIT | [A-D]) {% collapse %}

# All 4-hex digit unicode escape sequences that are not:
#
# * Surrogate pairs (i.e. `%xD800-DFFF`)
# * Non-characters (i.e. `%xFFFE-FFFF`)
#
unbraced_escape ->
      (DIGIT | [A-C]) HEXDIG HEXDIG HEXDIG {% collapse %}
    | "D" [0-7] HEXDIG HEXDIG {% collapse %}
    # %xD800-DFFF Surrogate pairs
    | "E" HEXDIG HEXDIG HEXDIG {% collapse %}
    | "F" HEXDIG HEXDIG (DIGIT | [A-D]) {% collapse %}
    # %xFFFE-FFFF Non-characters

# All 1-6 digit unicode codepoints that are not:
#
# * Surrogate pairs: `%xD800-DFFF`
# * Non-characters: `%xNFFFE-NFFFF` / `%x10FFFE-10FFFF` for `N` in `{ 0 .. F }`
#
# See the `valid-non-ascii` rule for the exact ranges that are not allowed
braced_codepoint ->
      "0":* ([1-9A-F] | "10") unicode_suffix {% collapse %} # (Planes 1-16)
    | unbraced_escape {% collapse %} # (Plane 0)
    | "0" {% collapse%}
    | ("0":+ "0"):? [1-9A-F] (HEXDIG HEXDIG:?):? {% collapse %} # %x000-FFF

# Allow zero padding for braced codepoints
braced_escape -> braced_codepoint {% collapse %}

# Printable characters except double quote and backslash
# FIXME
double_quote_char -> [\x20-\x21\x23\x25-\x5B\x5D-\x7F] {% pass0 %} | valid_non_ascii {% pass0 %}

double_quote_literal -> [\x22] double_quote_chunk [\x22] {% pass1 %}

# NOTE: The only way to end a single-quote string literal with a single quote is
# to either interpolate the single quote, like this:
#
#     ''ABC${"'"}''
#
# ... or concatenate another string, like this:
#
#     ''ABC'' ++ "'"
#
# If you try to end the string literal with a single quote then you get "'''",
# which is interpreted as an escaped pair of single quotes
single_quote_continue ->
      interpolation single_quote_continue {% d => [d[0]].concat(d[1]) %}
    | escaped_quote_pair single_quote_continue {% d => [d[0]].concat(d[1]) %}
    | escaped_interpolation single_quote_continue {% d => [d[0]].concat(d[1]) %}
    | "''" {% () => [] %}
    | single_quote_char single_quote_continue {% d => [d[0]].concat(d[1]) %}

# Escape two single quotes (i.e. replace this sequence with "''")
escaped_quote_pair -> "'''" {% () => "''" %}

# Escape interpolation (i.e. replace this sequence with "${")
escaped_interpolation -> "''${" {% () => "${" %}

# FIXME
single_quote_char -> [\x20-\x23\x25-\x26\x28-\x7F] {% pass0 %} | valid_non_ascii {% pass0 %} | tab {% pass0 %} | end_of_line {% pass0 %}
  # single quote cannot be followed by single quote
  | [\x27] ( [\x20-\x26\x28-\x7F] {% pass0 %} | valid_non_ascii {% pass0 %} | tab {% pass0 %} | end_of_line {% pass0 %} ) {% collapse %}
  # $ cannot be followed by {
  | [\x24] ( [\x20-\x7A\x7C-\x7F] {% pass0 %} | valid_non_ascii {% pass0 %} | tab {% pass0 %} | end_of_line {% pass0 %} ) {% collapse %}

single_quote_literal -> "''" end_of_line single_quote_continue {% d => remove_common_prefix(d[2]) %}

interpolation -> "${" complete_expression "}" {% pass1 %}

text_literal -> (double_quote_literal | single_quote_literal) {% d => d[0][0] %}

if                -> "if" {% pass0 %}
then              -> "then" {% pass0 %}
else              -> "else" {% pass0 %}
let               -> "let" {% pass0 %}
in                -> "in" {% pass0 %}
as                -> "as" {% pass0 %}
using             -> "using" {% pass0 %}
merge             -> "merge" {% pass0 %}
missing           -> "missing" {% pass0 %}
Infinity          -> "Infinity" {% pass0 %}
NaN               -> "NaN" {% pass0 %}
Some              -> "Some" {% pass0 %}
toMap             -> "toMap" {% pass0 %}
assert            -> "assert" {% pass0 %}
forall_keyword    -> "forall" {% pass0 %}
forall_symbol     -> [\u2200] {% pass0 %}
forall            -> forall_symbol | forall_keyword
with              -> "with"

# Unused rule that could be used as negative lookahead in the
# `simple-label` rule for parsers that support this.
keyword ->
      if {% pass0 %} | then {% pass0 %} | else {% pass0 %}
    | let {% pass0 %} | in {% pass0 %}
    | using {% pass0 %} | missing {% pass0 %}
    | assert {% pass0 %} | as {% pass0 %}
    | Infinity {% pass0 %} | NaN {% pass0 %}
    | merge {% pass0 %} | Some {% pass0 %} | toMap {% pass0 %}
    | forall_keyword {% pass0 %}
    | with {% pass0 %}

# Note that there is a corresponding parser test in
# `tests/parser/success/builtinsA.dhall`. Please update it when
# you modify this `builtin` rule.
builtin ->
    Natural_fold {% pass0 %}
  | Natural_build {% pass0 %}
  | Natural_isZero {% pass0 %}
  | Natural_even {% pass0 %}
  | Natural_odd {% pass0 %}
  | Natural_toInteger {% pass0 %}
  | Natural_show {% pass0 %}
  | Natural_subtract {% pass0 %}
  | Integer_toDouble {% pass0 %}
  | Integer_show {% pass0 %}
  | Integer_negate {% pass0 %}
  | Integer_clamp {% pass0 %}
  | Double_show {% pass0 %}
  | List_build {% pass0 %}
  | List_fold {% pass0 %}
  | List_length {% pass0 %}
  | List_head {% pass0 %}
  | List_last {% pass0 %}
  | List_indexed {% pass0 %}
  | List_reverse {% pass0 %}
  | Text_show {% pass0 %}
  | Text_replace {% pass0 %}
  | Bool {% pass0 %}
  | True {% pass0 %}
  | False {% pass0 %}
  | Optional {% pass0 %}
  | None {% pass0 %}
  | Natural {% pass0 %}
  | Integer {% pass0 %}
  | Double {% pass0 %}
  | Text {% pass0 %}
  | List {% pass0 %}
  | Type {% pass0 %}
  | Kind {% pass0 %}
  | Sort {% pass0 %}

# Reserved identifiers, needed for some special cases of parsing
Optional -> "Optional" {% pass0 %}
Text     -> "Text" {% pass0 %}
List     -> "List" {% pass0 %}
Location -> "Location" {% pass0 %}

# Reminder of the reserved identifiers, needed for the `builtin` rule
Bool              -> "Bool" {% pass0 %}
True              -> "True" {% pass0 %}
False             -> "False" {% pass0 %}
None              -> "None" {% pass0 %}
Natural           -> "Natural" {% pass0 %}
Integer           -> "Integer" {% pass0 %}
Double            -> "Double" {% pass0 %}
Type              -> "Type" {% pass0 %}
Kind              -> "Kind" {% pass0 %}
Sort              -> "Sort" {% pass0 %}
Natural_fold      -> "Natural/fold" {% pass0 %}
Natural_build     -> "Natural/build" {% pass0 %}
Natural_isZero    -> "Natural/isZero" {% pass0 %}
Natural_even      -> "Natural/even" {% pass0 %}
Natural_odd       -> "Natural/odd" {% pass0 %}
Natural_toInteger -> "Natural/toInteger" {% pass0 %}
Natural_show      -> "Natural/show" {% pass0 %}
Natural_subtract  -> "Natural/subtract" {% pass0 %}
Integer_toDouble  -> "Integer/toDouble" {% pass0 %}
Integer_show      -> "Integer/show" {% pass0 %}
Integer_negate    -> "Integer/negate" {% pass0 %}
Integer_clamp     -> "Integer/clamp" {% pass0 %}
Double_show       -> "Double/show" {% pass0 %}
List_build        -> "List/build" {% pass0 %}
List_fold         -> "List/fold" {% pass0 %}
List_length       -> "List/length" {% pass0 %}
List_head         -> "List/head" {% pass0 %}
List_last         -> "List/last" {% pass0 %}
List_indexed      -> "List/indexed" {% pass0 %}
List_reverse      -> "List/reverse" {% pass0 %}
Optional_fold     -> "Optional/fold" {% pass0 %}
Optional_build    -> "Optional/build" {% pass0 %}
Text_show         -> "Text/show" {% pass0 %}
Text_replace      -> "Text/replace" {% pass0 %}

combine       -> ( [\u2227] | "/\\"                ) {% pass0 %}
combine_types -> ( [\u2A53] | "//\\\\"              ) {% pass0 %}
equivalent    -> ( [\u2261] | "==="              ) {% pass0 %}
prefer        -> ( [\u2AFD] | "//"                ) {% pass0 %}
lambda        -> ( [\u03BB]  | "\\"                 ) {% pass0 %}
arrow         -> ( [\u2192] | "->"                ) {% pass0 %}
complete      -> "::" {% pass0 %}

exponent -> "e" ( "+" | "-" ):? DIGIT:+

numeric_double_literal -> ( "+" | "-" ):? DIGIT:+ ( "." DIGIT:+ ( exponent ):? | exponent) {% d => +flatten(d).join("") %}

minus_infinity_literal -> "-" Infinity {% () => -Infinity %}
plus_infinity_literal -> Infinity {% () => Infinity %}

double_literal ->
  # "2.0"
    numeric_double_literal {% (d,_,reject) => isFinite(d[0]) ? d[0] : reject %}
  # "-Infinity"
  | minus_infinity_literal {% pass0 %}
  # "Infinity"
  | plus_infinity_literal {% pass0 %}
  # "NaN"
  | NaN {% () => NaN %}

natural_literal ->
    # Hexadecimal with "0x" prefix
      "0x" HEXDIG:+ {% d => collapse(d)|0 %}
    # Decimal; leading 0 digits are not allowed
    | [1-9] DIGIT:* {% d => collapse(d)|0 %}
    # ... except for 0 itself
    | "0" {% () => 0 %}

integer_literal -> ( "+" | "-" ) natural_literal {% d => d[0] == "+" ? +d[1] : -d[1] %}

# If the identifier matches one of the names in the `builtin` rule, then it is a
# builtin, and should be treated as the curresponding item in the list of
# "Reserved identifiers for builtins" specified in the `standard/README.md` document.
# It is a syntax error to specify a de Bruijn index in this case.
# Otherwise, this is a variable with name and index matching the label and index.
identifier -> variable {% pass0 %} | builtin {% d => ({ type: d[0], value: [] }) %}

variable -> nonreserved_label ( whsp "@" natural_literal ):? {% d => ({ type: "Var", value: [d[0], pass(2)(d[1]) || 0] }) %}

# Printable characters other than " ()[]{}<>/\,"
#
# Excluding those characters ensures that paths don't have to end with trailing
# whitespace most of the time
path_character -> [\x21-\x22\x24-\x27\x2A-\x2B\x2D-\x2E\x30-\x3B\x3D\x40-\x5A\x5E-\x7A\x7C\x7E] {% pass0 %}

quoted_path_character -> [\x20-\x21\x23-\x2E\x30-\x7F] {% pass0 %} | valid_non_ascii {% pass0 %}

unquoted_path_component -> path_character:+ {% collapse %}
quoted_path_component -> quoted_path_character:+ {% collapse %}

path_component -> "/" ( unquoted_path_component {% pass0 %} | [\x22] quoted_path_component [\x22] {% pass1 %} ) {% pass1 %}

# The last path-component matched by this rule is referred to as "file" in the semantics,
# and the other path-components as "directory".
path -> path_component:+ {% pass0 %}

local ->
      ".." path {% d => ({ type: "Local", value: ["Parent", d[1].slice(0, -1), d[1][d[1].length-1]] }) %}
    | "."  path {% d => ({ type: "Local", value: ["Here", d[1].slice(0, -1), d[1][d[1].length-1]] }) %}
    | "~"  path {% d => ({ type: "Local", value: ["Home", d[1].slice(0, -1), d[1][d[1].length-1]] }) %}
    | path {% d => ({ type: "Local", value: ["Absolute", d[0].slice(0, -1), d[0][d[0].length-1]] }) %}

# `http[s]` URI grammar based on RFC7230 and RFC 3986 with some differences
# noted below

scheme -> "http" {% pass0 %} | "https" {% pass0 %}

# NOTE: This does not match the official grammar for a URI.  Specifically:
#
# * path segments may be quoted instead of using percent-encoding
# * this does not support fragment identifiers, which have no meaning within
#   Dhall expressions and do not affect import resolution
# * the characters "(" ")" and "," are not included in the `sub-delims` rule:
#   in particular, these characters can't be used in authority, path or query
#   strings.  This is because those characters have other meaning in Dhall
#   and it would be confusing for the comma in
#       [http://example.com/foo, bar]
#   to be part of the URL instead of part of the list.  If you need a URL
#   which contains parens or a comma, you must percent-encode them.
#
# Reserved characters in quoted path components should be percent-encoded
# according to https://tools.ietf.org/html/rfc3986#section-2
http_raw -> scheme "://" authority path_abempty ( "?" query ):?
{% d => ({ type: "Remote", value: [d[0], d[2], d[3].slice(0,-1), d[3][d[3].length-1], pass1(d[4])] }) %}

path_abempty -> ("/" segment):* {% pass0 %}

authority -> ( userinfo "@" ):? host ( ":" port ):? {% collapse %}

userinfo -> ( unreserved | pct_encoded | sub_delims | ":" ):* {% pass0 %}

host -> IP_literal {% collapse %} | IPv4address {% collapse %} | domain {% collapse %}

port -> DIGIT:* {% pass0 %}

IP_literal -> "[" ( IPv6address {% collapse %} | IPvFuture {% collapse %} ) "]"

IPvFuture -> "v" HEXDIG:+ "." ( unreserved | sub_delims | ":" ):+

IPv6address ->                            ( h16 ":" h16 ":" h16 ":" h16 ":" h16 ":" h16 ":" ) ls32
            |                       "::" ( h16 ":" h16 ":" h16 ":" h16 ":" h16 ":" h16 ":" ) ls32
            | (               h16 ):? "::" ( h16 ":" h16 ":" h16 ":" h16 ":" h16 ":" ) ls32
            | ( ( h16 ":" ):? h16 ):? "::" ( h16 ":" h16 ":" h16 ":" h16 ":" ) ls32
            | ( ( h16 ":" ( h16 ":" ):? ):? h16 ):? "::" ( h16 ":" h16 ":" h16 ":" ) ls32
            | ( ( h16 ":" ( h16 ":" ( h16 ":" ):? ):? ):? h16 ):? "::"    h16 ":"   ls32
            | ( ( h16 ":" ( h16 ":" ( h16 ":" ( h16 ":" ):? ):? ):? ):? h16 ):? "::"              ls32
            | ( ( h16 ":" ( h16 ":" ( h16 ":" ( h16 ":" ( h16 ":" ):? ):? ):? ):? ):? h16 ):? "::"              h16
            | ( ( h16 ":" ( h16 ":" ( h16 ":" ( h16 ":" ( h16 ":" ( h16 ":" ):? ):? ):? ):? ):? ) h16 ):? "::"

h16 -> HEXDIG | HEXDIG HEXDIG | HEXDIG HEXDIG HEXDIG | HEXDIG HEXDIG HEXDIG HEXDIG

ls32 -> ( h16 ":" h16 ) | IPv4address

IPv4address -> dec_octet "." dec_octet "." dec_octet "." dec_octet

dec_octet -> DIGIT {% collapse %}          | [\x31-\x39] DIGIT {% collapse %}          | "1" DIGIT DIGIT {% collapse %}          | "2" [\x30-\x34] DIGIT {% collapse %}          | "25" [\x30-\x35] {% collapse %}

# Look in RFC3986 3.2.2 for
# "A registered name intended for lookup in the DNS"
domain -> ( domainlabel "." ):* domainlabel ".":? {% collapse %}

domainlabel -> ALPHANUM:+ ( "-":+ ALPHANUM:+ ):* {% collapse %}

segment -> pchar:* {% collapse %}

pchar -> ( unreserved | pct_encoded | sub_delims | ":" | "@") {% collapse %}

query -> ( pchar | "/" | "?" ):* {% collapse %}

pct_encoded -> "%" HEXDIG HEXDIG {% collapse %}

unreserved  -> ( ALPHA | DIGIT | "-" | "." | "_" | "~" ) {% collapse %}

# this is the RFC3986 sub-delims rule, without "(", ")" or ","
# see comments above the `http-raw` rule above
sub_delims -> ( "!" | "$" | "&" | "'" | "*" | "+" | ";" | "=" )  {% collapse %}

http ->
    http_raw
    ( whsp using whsp1 import_expression ):?
  {% d => (d[0].value[5] = pass(3)(d[1]), d[0]) %}

# Dhall supports unquoted environment variables that are Bash-compliant or
# quoted environment variables that are POSIX-compliant
env -> "env:"
    ( bash_environment_variable
    | [\x22] posix_environment_variable [\x22]
    )
    {% d => ({ type: "Env", value: [d[1].length === 1 ? d[1][0] : d[1][1]] }) %}

# Bash supports a restricted subset of POSIX environment variables.  From the
# Bash `man` page, an environment variable name is:
#
# > A word consisting only of  alphanumeric  characters  and  under-scores,  and
# > beginning with an alphabetic character or an under-score
bash_environment_variable -> (ALPHA | "_") (ALPHA | DIGIT | "_"):* {% collapse %}

# The POSIX standard is significantly more flexible about legal environment
# variable names, which can contain alerts (i.e. '\a'), whitespace, or
# punctuation, for example.  The POSIX standard says about environment variable
# names:
#
# > The value of an environment variable is a string of characters. For a
# > C-language program, an array of strings called the environment shall be made
# > available when a process begins. The array is pointed to by the external
# > variable environ, which is defined as:
# >
# >     extern char **environ;
# >
# > These strings have the form name=value; names shall not contain the
# > character '='. For values to be portable across systems conforming to IEEE
# > Std 1003.1-2001, the value shall be composed of characters from the portable
# > character set (except NUL and as indicated below).
#
# Note that the standard does not explicitly state that the name must have at
# least one character, but `env` does not appear to support this and `env`
# claims to be POSIX-compliant.  To be safe, Dhall requires at least one
# character like `env`
posix_environment_variable -> posix_environment_variable_character:+ {% collapse %}

# These are all the characters from the POSIX Portable Character Set except for
# '\0' (NUL) and '='.  Note that the POSIX standard does not explicitly state
# that environment variable names cannot have NUL.  However, this is implicit
# in the fact that environment variables are passed to the program as
# NUL-terminated `name=value` strings, which implies that the `name` portion of
# the string cannot have NUL characters
posix_environment_variable_character ->
      [\x5C]      ( [\x22\x5C\x61\x62\x66\x6E\x72\x74\x76]      )
    | [\x20-\x21\x23-\x3C\x3E-\x5B\x5D-\x7E]

import_type -> missing {% () => ({ type: "Missing", value: [] }) %} | local {% pass0 %} | http {% pass0 %} | env {% pass0 %}

sha256_prefix -> "sha256:"

hash -> sha256_prefix HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG {% d => collapse(d.slice(1)) %}

import -> import_type ( whsp as whsp1 ( Text {% pass0 %} | Location {% pass0 %} ) {% pass(3) %} ):? {% tag("Import") %}

expression ->
    # "\(x : a) -> b"
      lambda whsp "(" whsp nonreserved_label whsp ":" whsp1 expression whsp ")" whsp arrow whsp expression {% d => ({ type: "Lam", value: [d[4], d[8], d[14]] }) %}

    # "if a then b else c"
    | if whsp1 expression whsp then whsp1 expression whsp else whsp1 expression {% d => ({ type: "BoolIf", value: [d[2], d[6], d[10]] }) %}

    # "let x : t = e1 in e2"
    # "let x     = e1 in e2"
    | let_binding:+ in whsp1 expression {% d => d[0].reduceRight((b,a) => ({ type: "Let", value: a.concat(b) }), d[3]) %}

    # "forall (x : a) -> b"
    | forall whsp "(" whsp nonreserved_label whsp ":" whsp1 expression whsp ")" whsp arrow whsp expression {% d => ({ type: "Pi", value: [d[4], d[8], d[14]] }) %}

    # "a -> b"
    #
    # NOTE: Backtrack if parsing this alternative fails
    | operator_expression whsp arrow whsp expression {% d => ({ type: "Pi", value: ["_", d[0], d[4]] }) %}

    # "a with x = b"
    #
    # NOTE: Backtrack if parsing this alternative fails
    | with_expression {% pass0 %}

    # "merge e1 e2 : t"
    #
    # NOTE: Backtrack if parsing this alternative fails since we can't tell
    # from the keyword whether there will be a type annotation or not
    | merge whsp1 import_expression whsp1 import_expression whsp ":" whsp1 application_expression {% d => ({ type: "Merge", value: [d[2], d[4], d[8]] }) %}

    # "[] : t"
    #
    # NOTE: Backtrack if parsing this alternative fails since we can't tell
    # from the opening bracket whether or not this will be an empty list or
    # a non-empty list
    | empty_list_literal {% pass0 %}

    # "toMap e : t"
    #
    # NOTE: Backtrack if parsing this alternative fails since we can't tell
    # from the keyword whether there will be a type annotation or not
    | toMap whsp1 import_expression whsp ":" whsp1 application_expression {% d => ({ type: "ToMap", value: [d[2],d[6]] }) %}

    # "assert : Natural/even 1 ≡ False"
    | assert whsp ":" whsp1 expression {% d => ({ type: "Assert", value: [d[4]] }) %} # FIXME?

    | annotated_expression {% pass0 %}

# Nonempty-whitespace to disambiguate `env:VARIABLE` from type annotations
annotated_expression ->
    # "x : t"
    operator_expression (whsp ":" whsp1 expression):? {% d => d[1] == null ? d[0] : { type: "Annot", value: [d[0], d[1][3]] } %}

let_binding ->
  let whsp1 nonreserved_label whsp ( ":" whsp1 expression whsp ):? "=" whsp expression whsp {% d => [d[2],pass(2)(d[4]),d[7]] %}

empty_list_literal ->
  "[" whsp ( "," whsp ):? "]" whsp ":" whsp1 application_expression {% d => ({ type: "ListLit", value: [[],d[7]] }) %}

with_expression ->
    import_expression (whsp1 with whsp1 with_clause):+ {% d => binop("With", 3) %}

with_clause ->
    any_label_or_some (whsp "." whsp any_label_or_some):* whsp "=" whsp operator_expression {% d => {throw "WITH"} %}

operator_expression -> equivalent_expression {% pass0 %}

# Nonempty-whitespace to disambiguate `http://a/a?a`
equivalent_expression    -> import_alt_expression    (whsp equivalent whsp application_expression):* {% binop("Equivalent", 3) %}
import_alt_expression    -> or_expression            (whsp "?" whsp1 or_expression):* {% binop("ImportAlt", 3) %}
or_expression            -> plus_expression          (whsp "||" whsp plus_expression):* {% binop("BoolOr", 3) %}
# Nonempty-whitespace to disambiguate `f +2`
plus_expression          -> text_append_expression   (whsp "+" whsp1 text_append_expression):* {% binop("NaturalPlus", 3) %}
text_append_expression   -> list_append_expression   (whsp "++" whsp list_append_expression):* {% binop("TextAppend", 3) %}
list_append_expression   -> and_expression           (whsp "#" whsp and_expression):* {% binop("ListAppend", 3) %}
and_expression           -> combine_expression       (whsp "&&" whsp combine_expression):* {% binop("BoolAnd", 3) %}
combine_expression       -> prefer_expression        (whsp combine whsp prefer_expression):* {% binop("Combine", 3) %}
prefer_expression        -> combine_types_expression (whsp prefer whsp combine_types_expression):* {% binop("Prefer", 3) %}
combine_types_expression -> times_expression         (whsp combine_types whsp times_expression):* {% binop("CombineTypes", 3) %}
times_expression         -> equal_expression         (whsp "*" whsp equal_expression):* {% binop("NaturalTimes", 3) %}
equal_expression         -> not_equal_expression     (whsp "==" whsp not_equal_expression):* {% binop("BoolEQ", 3) %}
not_equal_expression     -> application_expression   (whsp "!=" whsp application_expression):* {% binop("BoolNE", 3) %}

# Import expressions need to be separated by some whitespace, otherwise there
# would be ambiguity: `./ab` could be interpreted as "import the file `./ab`",
# or "apply the import `./a` to label `b`"
application_expression ->
    first_application_expression (whsp1 import_expression):* {% binop("App") %}

first_application_expression ->
  # "merge e1 e2"
    merge whsp1 import_expression whsp1 import_expression
    {% d => ({ type: "Merge", value: [d[2],d[4],null]}) %}
  # "Some e"
  | Some whsp1 import_expression
    {% d => ({ type: "Some", value: [d[2]] }) %}
  # "toMap e"
  | toMap whsp1 import_expression
    {% d => ({ type: "ToMap", value: [d[2], null] }) %}
  | import_expression {% pass0 %}

import_expression ->
  ( import {% pass0 %}
  | completion_expression {% pass0 %}
  ) (whsp1 hash):?
  {% d => d[1] == null ? d[0] : ({ type: "Hashed", value: [d[0], d[1][1]] }) %}

completion_expression ->
  selector_expression ( whsp complete whsp selector_expression ):? {% d => d[1] != null ? { type: "RecordCompletion", value: [d[0], d[1][3]] } : d[0] %}

# `record.field` extracts one field of a record
#
# `record.{ field0, field1, field2 }` projects out several fields of a record
#
# NOTE: Backtrack when parsing the `*("." ...)`.  The reason why is that you
# can't tell from parsing just the period whether "foo." will become "foo.bar"
# (i.e. accessing field `bar` of the record `foo`) or `foo./bar` (i.e. applying
# the function `foo` to the relative path `./bar`)
selector_expression -> primitive_expression (whsp "." whsp selector):*
{% d =>
  d[1].reduce((r, v) => ({ type: v[3].type, value: [r, v[3].value[0]] }), d[0])
%}


selector ->
    any_label {% tag("Field") %}
  | labels {% tag("Project") %}
  | type_selector {% tag("ProjectType") %}

labels -> "{" whsp ( any_label_or_some whsp ("," whsp any_label_or_some whsp):* ):? "}"
{% d => d[2] != null ? [d[2][0]].concat(d[2][2].map(v => v[2])) : [] %}

type_selector -> "(" whsp expression whsp ")" {% pass(2) %}

primitive_expression ->
    # "2.0"
      double_literal {% tag("DoubleLit") %}
    # 2
    | natural_literal {% tag("NaturalLit") %}
    # +2
    # -2
    | integer_literal {% tag("IntegerLit") %}
    # '"ABC"'
    | text_literal {% d => ({ type: "TextLit", value: d[0] }) %}
    # "{ foo = 1      , bar = True }"
    # "{ foo : Integer, bar : Bool }"
    | "{" whsp ( "," whsp ):? record_type_or_literal whsp "}" {% pass(3) %}
    # "< Foo : Integer | Bar : Bool >"
    # "< Foo : Integer | Bar = True >"
    | "<" whsp ( "," whsp ):? union_type ">" {% pass(3) %}
    # "[1, 2, 3]"
    | non_empty_list_literal {% pass0 %}
    # "x"
    # "x@2"
    | identifier {% pass0 %}
    # "(e)"
    | "(" complete_expression ")" {% pass1 %}

record_type_or_literal ->
    empty_record_literal {% pass0 %}
  | non_empty_record_type_or_literal {% pass0 %}
  | empty_record_type {% pass0 %}

empty_record_literal -> "=" ( whsp "," ):? {% () => ({ type: "RecordLit", value: [] }) %}
empty_record_type -> null {% () => ({ type: "Record", value: [] }) %}
non_empty_record_type_or_literal ->
    any_label_or_some whsp ( non_empty_record_literal | non_empty_record_type )
  {% d => {d[2][0].value[0][0] = d[0]; return d[2][0]} %}
non_empty_record_type    -> ":" whsp1 expression (whsp "," whsp record_type_entry):*
  {%
  d => ({ type: "Record", value: [["",d[2]]].concat(d[3].map(v => v[3])) })
  %}
record_type_entry -> any_label whsp ":" whsp1 expression {% d => [d[0], d[4]] %}
non_empty_record_literal -> "=" whsp expression (whsp "," whsp record_literal_entry):*
  {%
  d => ({ type: "RecordLit", value: [["",d[2]]].concat(d[3].map(v => v[3])) })
  %}
record_literal_entry -> any_label whsp "=" whsp expression {% d => [d[0],d[4]] %}

union_type ->
      non_empty_union_type whsp {% pass0 %}
    | empty_union_type {% pass0 %}

empty_union_type -> null {% () => ({ type: "Union", value: [] }) %}

non_empty_union_type ->
    union_type_entry ( whsp "|" whsp union_type_entry {% pass(3) %} ):*
    {% d => ({ type: "Union", value: [d[0]].concat(d[1]) }) %}

# x : Natural
# x
union_type_entry -> any_label ( whsp ":" whsp1 expression ):?
    {% d => [d[0],pass(3)(d[1])] %}

non_empty_list_literal -> "[" whsp ( "," whsp ):? expression whsp ("," whsp expression whsp):* ( "," whsp ):? "]"
  {% d => ({ type: "ListLit", value: [[d[3]].concat(d[5].map(v => v[2])),null] }) %}

# We provide special support for the Unix shebang convention, by permitting
# `#!` as a line comment only on the first lines
shebang -> "#!" not_end_of_line:* end_of_line
