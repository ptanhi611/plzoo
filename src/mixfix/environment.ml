
module TokenSet = Set.Make(struct type t = Syntax.name let compare = compare end)

type parser_context = {
  operators: Precedence.graph;
  known_tokens: TokenSet.t;
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
    known_tokens = TokenSet.empty;
  };
  context = [];
  env = [];
}
;;

let debug = true

let register_operator (ctx:parser_context) (prec, op) =
  let operators = Precedence.add_operator ctx.operators prec op in
  {ctx with operators = operators}

let add_known_token (ctx:parser_context) token =
  let known_tokens = TokenSet.add token ctx.known_tokens in
  {ctx with known_tokens = known_tokens}

let token_present (ctx:parser_context) token =
  TokenSet.mem token ctx.known_tokens

let dprintln a =
  if debug then print_endline a else ()