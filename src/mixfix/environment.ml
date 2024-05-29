
module IdentifierSet = Set.Make(struct type t = Syntax.name let compare = Stdlib.compare end)

type parser_context = {
  operators: Precedence.graph;
  known_identifiers: IdentifierSet.t;
}

type t = {
  parser_context: parser_context;
  context: (Syntax.name * Presyntax.htype) list;
  env: Interpret.environment;
}
;;

let empty = {
  parser_context = {
    operators = Precedence.empty_graph;
    known_identifiers = IdentifierSet.empty;
  };
  context = [];
  env = [];
}
;;

let debug = true

let register_operator (ctx:parser_context) (prec, op) =
  let operators = Precedence.add_operator ctx.operators prec op in
  {ctx with operators = operators}

let add_identifier_token (ctx:parser_context) identifier =
  let new_identifiers = IdentifierSet.add identifier ctx.known_identifiers in
  {ctx with known_identifiers = new_identifiers}

let identifier_present (ctx:parser_context) token =
  IdentifierSet.mem token ctx.known_identifiers

let dprintln a =
  if debug then print_endline a else ()