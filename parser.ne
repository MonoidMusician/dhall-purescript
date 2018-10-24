@{%
function binop(type, i=1) {
	return data => data[1].reduce((r, v) => ({ type, value: [r, v[i]] }), data[0]);
};

function nuller() { return null; }

const pass = n => d => d ? d[n] : null;
const pass0 = pass(0);
const pass1 = pass(1);

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
%}

complete_expression -> whitespace expression {% pass1 %}


end_of_line ->
      [\u0A]    | [\u0D] [\u0A]
tab -> [\u09]
block_comment -> "{-" block_comment_continue

block_comment_chunk ->
      block_comment
    | .
    | tab
    | end_of_line

block_comment_continue -> "-}" | block_comment_chunk block_comment_continue

not_end_of_line -> [^\u20] | tab

line_comment -> "--" not_end_of_line:* end_of_line

whitespace_chunk ->
      " " {% nuller %}
    | tab {% nuller %}
    | end_of_line {% nuller %}
    | line_comment {% nuller %}
    | block_comment {% nuller %}

whitespace -> whitespace_chunk:* {% nuller %}

nonempty_whitespace -> whitespace_chunk:+ {% nuller %}

ALPHA -> [A-Za-z]

DIGIT -> [0-9]
HEXDIG -> DIGIT {% pass0 %} | "A" {% pass0 %} | "B" {% pass0 %} | "C" {% pass0 %} | "D" {% pass0 %} | "E" {% pass0 %} | "F" {% pass0 %}

simple_label -> (ALPHA | "_") (ALPHA | DIGIT | "-" | "/" | "_"):* {% d => d[0].join("") + d[1].join("") %}

quoted_label -> (ALPHA | DIGIT | "-" | "/" | "_" | ":" | "." | "$"):+ {% d => d[0].join("") %}

label -> ("`" quoted_label "`" | simple_label) whitespace {% d => d[0].length === 3 ? d[0][1] : d[0][0] %}

double_quote_chunk ->
      "${" expression "}" {% pass1 %}    | "\\"      ( [\u22]      | [\u24]      | [\u5C]      | [\u2F]      | [\u62]      | [\u66]      | [\u6E]      | [\u72]      | [\u74]      | [\u75] HEXDIG HEXDIG HEXDIG HEXDIG {% d => String.fromCharCode(parseInt(d[1]+d[2]+d[3]+d[4], 16)) %}      ) {% pass1 %}
    | [^"\\] {% pass0 %}

double_quote_literal -> [\u22] double_quote_chunk:* [\u22] {% pass1 %}

single_quote_continue ->
      "'''"               single_quote_continue {% d => ["''"].concat(d[1]) %}
    | "${" complete_expression "}" single_quote_continue {% d => [d[1]].concat(d[3]) %}
    | "''${"              single_quote_continue {% d => ["${"].concat(d[1]) %}
    | "''" {% () => [] %}
	| .         single_quote_continue {% d => [d[0]].concat(d[1]) %}

single_quote_literal -> "''" single_quote_continue {% pass1 %}

text_literal -> (double_quote_literal | single_quote_literal) whitespace {% pass0 %}

if_raw                -> "if" {% pass0 %}
then_raw              -> "then" {% pass0 %}
else_raw              -> "else" {% pass0 %}
let_raw               -> "let" {% pass0 %}
in_raw                -> "in" {% pass0 %}
as_raw                -> "as" {% pass0 %}
using_raw             -> "using" {% pass0 %}
merge_raw             -> "merge" {% pass0 %}
missing_raw           -> "missing" {% pass0 %}
Some_raw              -> "Some" {% pass0 %}
constructors_raw      -> "constructors" {% pass0 %}
Natural_fold_raw      -> "Natural/fold" {% pass0 %}
Natural_build_raw     -> "Natural/build" {% pass0 %}
Natural_isZero_raw    -> "Natural/isZero" {% pass0 %}
Natural_even_raw      -> "Natural/even" {% pass0 %}
Natural_odd_raw       -> "Natural/odd" {% pass0 %}
Natural_toInteger_raw -> "Natural/toInteger" {% pass0 %}
Natural_show_raw      -> "Natural/show" {% pass0 %}
Integer_toDouble_raw  -> "Integer/toDouble" {% pass0 %}
Integer_show_raw      -> "Integer/show" {% pass0 %}
Double_show_raw       -> "Double/show" {% pass0 %}
List_build_raw        -> "List/build" {% pass0 %}
List_fold_raw         -> "List/fold" {% pass0 %}
List_length_raw       -> "List/length" {% pass0 %}
List_head_raw         -> "List/head" {% pass0 %}
List_last_raw         -> "List/last" {% pass0 %}
List_indexed_raw      -> "List/indexed" {% pass0 %}
List_reverse_raw      -> "List/reverse" {% pass0 %}
Optional_fold_raw     -> "Optional/fold" {% pass0 %}
Optional_build_raw    -> "Optional/build" {% pass0 %}
Bool_raw              -> "Bool" {% pass0 %}
Optional_raw        -> "Optional" {% pass0 %}
None_raw              -> "None" {% pass0 %}
Natural_raw           -> "Natural" {% pass0 %}
Integer_raw           -> "Integer" {% pass0 %}
Double_raw            -> "Double" {% pass0 %}
Text_raw              -> "Text" {% pass0 %}
List_raw              -> "List" {% pass0 %}
True_raw              -> "True" {% pass0 %}
False_raw             -> "False" {% pass0 %}
Type_raw              -> "Type" {% pass0 %}
Kind_raw              -> "Kind" {% pass0 %}
Sort_raw              -> "Sort" {% pass0 %}

reserved_raw ->
    Bool_raw {% pass0 %}
  | Optional_raw {% pass0 %}
  | None_raw {% pass0 %}
  | Natural_raw {% pass0 %}
  | Integer_raw {% pass0 %}
  | Double_raw {% pass0 %}
  | Text_raw {% pass0 %}
  | List_raw {% pass0 %}
  | True_raw {% pass0 %}
  | False_raw {% pass0 %}
  | Type_raw {% pass0 %}
  | Kind_raw {% pass0 %}
  | Sort_raw {% pass0 %}

reserved_namespaced_raw ->
    Natural_fold_raw {% pass0 %}
  | Natural_build_raw {% pass0 %}
  | Natural_isZero_raw {% pass0 %}
  | Natural_even_raw {% pass0 %}
  | Natural_odd_raw {% pass0 %}
  | Natural_toInteger_raw {% pass0 %}
  | Natural_show_raw {% pass0 %}
  | Integer_toDouble_raw {% pass0 %}
  | Integer_show_raw {% pass0 %}
  | Double_show_raw {% pass0 %}
  | List_build_raw {% pass0 %}
  | List_fold_raw {% pass0 %}
  | List_length_raw {% pass0 %}
  | List_head_raw {% pass0 %}
  | List_last_raw {% pass0 %}
  | List_indexed_raw {% pass0 %}
  | List_reverse_raw {% pass0 %}
  | Optional_fold_raw {% pass0 %}
  | Optional_build_raw {% pass0 %}

reserved            -> reserved_raw            whitespace {% pass0 %}
reserved_namespaced -> reserved_namespaced_raw whitespace {% pass0 %}

if           -> if_raw           nonempty_whitespace {% pass0 %}
then         -> then_raw         nonempty_whitespace {% pass0 %}
else         -> else_raw         nonempty_whitespace {% pass0 %}
let          -> let_raw          nonempty_whitespace {% pass0 %}
in           -> in_raw           nonempty_whitespace {% pass0 %}
as           -> as_raw           nonempty_whitespace {% pass0 %}
using        -> using_raw        nonempty_whitespace {% pass0 %}
merge        -> merge_raw        nonempty_whitespace {% pass0 %}
constructors -> constructors_raw nonempty_whitespace {% pass0 %}
Some         -> Some_raw         nonempty_whitespace {% pass0 %}

Optional     -> Optional_raw     whitespace {% pass0 %}
Text         -> Text_raw         whitespace {% pass0 %}
List         -> List_raw         whitespace {% pass0 %}

equal         -> "="  whitespace {% pass0 %}
or            -> "||" whitespace {% pass0 %}
plus          -> "+"  whitespace {% pass0 %}
text_append   -> "++" whitespace {% pass0 %}
list_append   -> "#"  whitespace {% pass0 %}
and           -> "&&" whitespace {% pass0 %}
times         -> "*"  whitespace {% pass0 %}
double_equal  -> "==" whitespace {% pass0 %}
not_equal     -> "!=" whitespace {% pass0 %}
dot           -> "."  whitespace {% pass0 %}
open_brace    -> "{"  whitespace {% pass0 %}
close_brace   -> "}"  whitespace {% pass0 %}
open_bracket  -> "["  whitespace {% pass0 %}
close_bracket -> "]"  whitespace {% pass0 %}
open_angle    -> "<"  whitespace {% pass0 %}
close_angle   -> ">"  whitespace {% pass0 %}
bar           -> "|"  whitespace {% pass0 %}
comma         -> ","  whitespace {% pass0 %}
open_parens   -> "("  whitespace {% pass0 %}
close_parens  -> ")"  whitespace {% pass0 %}
colon         -> ":"  whitespace {% pass0 %}
at            -> "@"  whitespace {% pass0 %}
import_alt    -> "?"  whitespace {% pass0 %}

combine       -> ( [\u2227] | "/\\"                ) whitespace {% pass0 %}
combine_types -> ( [\u2A53] | "//\\\\"              ) whitespace {% pass0 %}
prefer        -> ( [\u2AFD] | "//"                ) whitespace {% pass0 %}
lambda        -> ( [\u3BB]  | "\\"                 ) whitespace {% pass0 %}
forall        -> ( [\u2200] | "forall" ) whitespace {% pass0 %}
arrow         -> ( [\u2192] | "->"                ) whitespace {% pass0 %}

exponent -> "e" ( "+" | "-" ):? DIGIT:+

double_literal -> ( "+" | "-" ):? DIGIT:+ ( "." DIGIT:+ ( exponent ):? | exponent) whitespace {% d => +flatten(d).join("") %}

natural_lit_raw -> DIGIT:+ {% d => d[0].join("")|0 %}

integer_literal -> ( "+" | "-" ) natural_lit_raw whitespace {% d => d[0] == "+" ? d[1] : -d[1] %}

natural_literal -> natural_lit_raw whitespace {% pass0 %}

identifier -> label ( at natural_lit_raw ):? whitespace {% d => ({ type: "Var", value: [d[0], d[1] || 0] }) %}

identifier_reserved_prefix ->
    reserved_raw (ALPHA | DIGIT | "-" | "/" | "_"):+ whitespace ( at natural_lit_raw ):? whitespace {% d => ({ type: "Var", value: [d[0]+d[1].join(""), d[3] || 0] }) %}

identifier_reserved_namespaced_prefix ->
    reserved_namespaced_raw (ALPHA | DIGIT | "-" | "/" | "_"):+ whitespace ( at natural_lit_raw ):? {% d => ({ type: "Var", value: [d[0]+d[1].join(""), d[3] || 0] }) %}

missing -> missing_raw whitespace {% pass0 %}

path_character ->
      [\u21-\u22]
    | [\u24-\u27]
    | [\u2A-\u2B]
    | [\u2D-\u2E]
    | [\u30-\u3B]
    | [\u3D]
    | [\u40-\u5A]
    | [\u5E-\u7A]
    | [\u7C]
    | [\u7E]

path_component -> "/" path_character:+ {% d => d[1].join() %}

directory -> path_component:*

file -> path_component

local_raw ->
      ".." directory file    | "."  directory file    | "~"  directory file    | directory file {% d => [null, d[0], d[1]] %}
local -> local_raw whitespace {% pass0 %}


scheme -> "http" {% pass0 %} | "https" {% pass0 %}
http_raw -> scheme "://" authority directory file ( "?" query ):? ( "#" fragment ):?
{% d => [d[0], d[2], d[3], d[4], pass1(d[5]), pass1(d[6])] %}

authority -> ( userinfo "@" ):? host ( ":" port ):? {% d => [pass1(d[0]), d[1], pass1(d[2])] %}

userinfo -> ( unreserved | pct_encoded | sub_delims | ":" ):*

host -> IP_literal | IPv4address | reg_name

port -> DIGIT:*

IP_literal -> "[" ( IPv6address | IPvFuture  ) "]"

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

h16 -> HEXDIG | HEXDIG | HEXDIG | HEXDIG

ls32 -> ( h16 ":" h16 ) | IPv4address

IPv4address -> dec_octet "." dec_octet "." dec_octet "." dec_octet

dec_octet -> DIGIT          | [\u31-\u39] DIGIT          | "1" DIGIT DIGIT          | "2" [\u30-\u34] DIGIT          | "25" [\u30-\u35]
reg_name -> ( unreserved | pct_encoded | sub_delims ):*

pchar -> unreserved | pct_encoded | sub_delims | ":" | "@"

query -> ( pchar | "/" | "?" ):*

fragment -> ( pchar | "/" | "?" ):*

pct_encoded -> "%" HEXDIG HEXDIG

unreserved  -> ALPHA | DIGIT | "-" | "." | "_" | "~"

sub_delims -> "!" | "$" | "&" | "'" | "(" | ")" | "*" | "+" | "," | ";" | "="

http ->
    http_raw whitespace
    ( using (import_hashed | open_parens import_hashed close_parens) ):?

env -> "env:"
    ( bash_environment_variable
    | [\u22] posix_environment_variable [\u22]
    )
    whitespace

bash_environment_variable -> (ALPHA | "_") (ALPHA | DIGIT | "_"):*

posix_environment_variable -> posix_environment_variable_character:+

posix_environment_variable_character ->
      [\u5C]      ( [\u22]      | [\u5C]      | [\u61]      | [\u62]      | [\u66]      | [\u6E]      | [\u72]      | [\u74]      | [\u76]      )
    | [\u20-\u21]
    | [\u23-\u3C]
    | [\u3E-\u5B]
    | [\u5D-\u7E]

import_type -> missing | local | http | env

hash -> [\u73] [\u68] [\u61] [\u32] [\u35] [\u36] [\u3a] HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG HEXDIG whitespace
import_hashed -> import_type ( hash ):?

import -> import_hashed ( as Text ):?


expression ->
      lambda open_parens label colon expression close_parens arrow expression {% d => ({ type: "Lam", value: [d[2], d[4], d[7]] }) %}
    | if expression then expression else expression {% d => ({ type: "BoolIf", value: [d[1], d[3], d[5]] }) %}
    | let label ( colon expression ):? equal expression in expression {% d => ({ type: "Let", value: [d[1], pass1(d[2]), d[4], d[6]] }) %}
    | forall open_parens label colon expression close_parens arrow expression {% d => ({ type: "Pi", value: [d[2], d[4], d[7]] }) %}
    | operator_expression arrow expression {% d => ({ type: "Pi", value: ["_", d[0], d[2]] }) %}
    | annotated_expression {% pass0 %}

annotated_expression ->
      merge import_expression import_expression ( colon application_expression ):? {% d => ({ type: "Merge", value: [d[1], d[2], pass1(d[3])] }) %}
    | open_bracket (empty_collection | non_empty_optional) {% pass1 %}
    | operator_expression (colon expression):? {% d => d[1] == null ? d[0] : { type: "Annot", value: [d[0], d[1][1]] } %}

empty_collection -> close_bracket colon (List | Optional) import_expression {% d => ({ type: d[2]+"Lit", value: [[], d[3]] }) %}

non_empty_optional -> expression close_bracket colon Optional import_expression {% d => ({ type: "OptionalLit", value: [[d[0]], d[4]] }) %}

operator_expression -> import_alt_expression {% pass0 %}

import_alt_expression    -> or_expression            (import_alt            or_expression):* {% binop("ImportAlt") %}
or_expression            -> plus_expression          (or                    plus_expression         ):* {% binop("BinOr") %}
plus_expression          -> text_append_expression   (plus whitespace_chunk text_append_expression  ):* {% binop("NaturalPlus", 2) %}
text_append_expression   -> list_append_expression   (text_append           list_append_expression  ):* {% binop("TextAppend") %}
list_append_expression   -> and_expression           (list_append           and_expression          ):* {% binop("ListAppend") %}
and_expression           -> combine_expression       (and                   combine_expression      ):* {% binop("BinAnd") %}
combine_expression       -> prefer_expression        (combine               prefer_expression       ):* {% binop("Combine") %}
prefer_expression        -> combine_types_expression (prefer                combine_types_expression):* {% binop("Prefer") %}
combine_types_expression -> times_expression         (combine_types         times_expression        ):* {% binop("CombineTypes") %}
times_expression         -> equal_expression         (times                 equal_expression        ):* {% binop("NaturalTimes") %}
equal_expression         -> not_equal_expression     (double_equal          not_equal_expression    ):* {% binop("BinEQ") %}
not_equal_expression     -> application_expression   (not_equal             application_expression  ):* {% binop("BinNE") %}

application_expression ->
    ( constructors | Some ):? import_expression (whitespace_chunk import_expression):*
{%
d => {
	if (d[0] != null) {
		return binop("App")([{ type: "App", value: [d[0], d[1]] }, d[2]]);
	} else {
		return binop("App")([d[1],d[2]]);
	}
}
%}

import_expression -> import {% pass0 %} | selector_expression {% pass0 %}

selector_expression -> primitive_expression (dot ( label | labels )):*
{% function(d) {
	return d[1].reduce((r, v) => {
		if (typeof v[1][0] === "string")
			return { type: "Field", value: [r, v[1][0]] }
		else return { type: "Project", value: [r, v[1][0]] }
	}, d[0]);
} %}


primitive_expression ->
      double_literal {% d => ({ type: "DoubleLit", value: d[0] }) %}
    | natural_literal {% d => ({ type: "NaturalLit", value: d[0] }) %}
    | integer_literal {% d => ({ type: "IntegerLit", value: d[0] }) %}
    | text_literal {% d => ({ type: "TextLit", value: d[0] }) %}
    | open_brace record_type_or_literal close_brace {% pass1 %}
    | open_angle union_type_or_literal  close_angle {% pass1 %}
    | non_empty_list_literal {% pass0 %}
	| identifier_reserved_namespaced_prefix {% pass0 %}
    | reserved_namespaced {% d => ({ type: d[0], value: [] }) %}
    | identifier_reserved_prefix {% pass0 %}
    | reserved {% d => ({ type: d[0], value: [] }) %}
    | identifier {% pass0 %}
    | open_parens expression close_parens {% pass1 %}

labels -> open_brace (  label (comma label):* | null ) close_brace
{% d => d[1].length ? [d[1][0]].concat(d[1][1].map(v => v[1])) : [] %}

record_type_or_literal ->
      equal {% () => ({ type: "RecordLit", value: [] }) %}
	  | non_empty_record_type_or_literal {% pass0 %}
      | null {% () => ({ type: "Record", value: [] }) %}
non_empty_record_type_or_literal ->
    label (non_empty_record_literal | non_empty_record_type)
	{% d => {d[1][0].value[0][0] = d[0]; return d[1][0]} %}

non_empty_record_type    -> colon expression (comma label colon expression):*
{%
d => ({ type: "Record", value: [["",d[1]]].concat(d[2].map(v => [v[1],v[3]])) })
%}
non_empty_record_literal -> equal expression (comma label equal expression):*
{%
d => ({ type: "RecordLit", value: [["",d[1]]].concat(d[2].map(v => [v[1],v[3]])) })
%}

union_type_or_literal ->
      non_empty_union_type_or_literal
    | null {% () => ({ type: "Union", value: [] }) %}
non_empty_union_type_or_literal ->
    label
    ( equal expression (bar label colon expression):*
{%
d => [({ type: "UnionLit", value: [["",d[1]]].concat(d[2].map(v => [v[1],v[3]])) })]
%}
    | colon expression (bar non_empty_union_type_or_literal | null)
{%
d => [({ type: "Union", value: [["",d[1]]].concat(d[2].map(v => [v[1],v[3]])) })]
%}
    )
	{% function(d) {d[1][0].value[0][0] = d[0]; return d[1][0]} %}

non_empty_list_literal -> open_bracket expression (comma expression):* close_bracket
	{% d => ({type: "ListLit", value: [[d[1]].concat(d[2].map(v => v[1])), null]}) %}
