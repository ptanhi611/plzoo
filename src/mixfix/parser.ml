(* Parser combinatorji *)

module ListMonad = struct

  let return = Seq.return

  let ( >>= ) x f = Seq.concat_map f x

  let ( let* ) = ( >>= )

  let fail = Seq.empty

end

module ParserMonad : sig
  type ('token, 'a) t = ('token Seq.t -> ('a * 'token Seq.t) Seq.t)

  val return : 'a -> ('token, 'a) t
  val fail : ('token, 'a) t
  val eof : ('token, unit) t
  val get : ('token, 'token) t
  val ( +++ ) : ('token, 'a) t -> ('token, 'a) t -> ('token, 'a) t
  val ( let* ) : ('token, 'a) t -> ('a -> ('token, 'b) t) -> ('token, 'b) t
  val ( >>= ) : ('token, 'a) t -> ('a -> ('token, 'b) t) -> ('token, 'b) t
end = struct
  type ('token, 'a) t = 'token Seq.t -> ('a * 'token Seq.t) Seq.t

  let return x = fun inp -> Seq.return (x, inp)

  let ( >>= ) (p : ('token, 'a) t) (f : 'a -> ('token, 'b) t) : ('token, 'b) t =
    fun inp ->
    (let g (x, rest) = (f x) rest in
      Seq.concat_map g (p inp))

  let ( let* ) = ( >>= )

  (** Fail parser directly fails. (Returns [[]]) *)
  let fail : ('token, 'a) t = fun _ -> Seq.empty

  (** Gets next token from the stream *)
  let get : ('token, 'token) t = fun inp -> 
    match Seq.uncons inp with 
    | None -> Seq.empty
    | Some (t,ts) -> Seq.return (t, ts)

  let ( +++ ) c1 c2 inp = Seq.append (c1 inp) (c2 inp)

  let eof : ('token, unit) t =
    fun inp -> match Seq.uncons inp with
    | None -> (Seq.return ((), Seq.empty))
    | Some _ -> Seq.empty
end

open ParserMonad

let check_success lst =
  match List.of_seq lst with
  | [] -> Zoo.error "could not parse"
  | [ r ] -> r
  | _ :: _ :: _ as e ->
    print_endline @@ "\n - " ^ (String.concat "\n - " (List.map Syntax.string_of_expr e));
    Zoo.error "ambiguous parse"

type (_, _) parser =
  | Fail : ('a, 'b) parser
  | Return : 'b -> ('a, 'b) parser
  | Sequ : ('a, 'b) parser * ('a, 'c) parser -> ('a, 'b * 'c) parser
  | Or : ('a, 'b) parser * ('a, 'b) parser -> ('a, 'b) parser
  | Map : ('b -> 'c Seq.t) * ('a, 'b) parser -> ('a, 'c) parser
  | Lazy : ('a, 'b) parser lazy_t -> ('a, 'b) parser
  | Get : ('a, 'a) parser
  | Eof : ('a, unit) parser

let rec string_of_parser : type a b. (a, b) parser -> string = function
  | Fail -> "Fail"
  | Return _ -> "Return"
  | Sequ (p1, p2) -> "(" ^ string_of_parser p1 ^ " -> " ^ string_of_parser p2 ^ ")"
  | Or (p1, p2) -> "Or(" ^ string_of_parser p1 ^ ", " ^ string_of_parser p2 ^ ")"
  | Map (_, p) -> "Map(" ^ string_of_parser p ^ ")"
  | Lazy (lazy p) -> "Lazy()"
  | Get -> "Get"
  | Eof -> "Eof"

let return_many xs = fun inp -> Seq.map (fun x -> (x, inp)) xs

let rec runParser : type a b. (a, b) parser -> (a, b) t = function
  | Fail -> fail
  | Return t -> return t
  | Get -> get
  | Eof -> eof
  | Lazy (lazy p) -> runParser p

  | Sequ (p, q) ->
    let* x = runParser p in
    let* y = runParser q in
    return (x, y)

  | Or (p, q) -> runParser p +++ runParser q

  | Map (f, p) ->
    let* x = runParser p in
    return_many @@ f x

(** Flat Map. [f p] Creates a parser that maps f over result of p and returns all the individual results. *)
let flat_map f p = Map(f, p)

(** Map. [map f p] Creates a parser that maps f over result of p *)
let map f p = Map ((fun x -> Seq.return (f x)), p)

(** Map_opt. [map_opt f p] Creates a parser that maps f over result of p, but only if f is not None *)
let map_opt f p = Map (
  (fun x -> match f x with
  | Some t -> Seq.return t
  | None -> Seq.empty), p)

let kw k = map_opt (fun x -> if x = k then Some x else None) Get

(** Recursive parser building *)
let recursively build =
  let rec self = lazy (build (Lazy self)) in
  Lazy.force self

(** Option to choose from either parse result of [p1] pr [p2] *)
let ( ||| ) p1 p2 = Or (p1, p2)

(** Concatenation of parsers, returning a pair *)
let ( @@@ ) p1 p2 = Sequ (p1, p2)

(** Concatenation of parsers, discarding left *)
let ( <@@ ) p1 p2 = map snd (p1 @@@ p2)

(** Concatenation of parsers, discarding right *)
let ( @@< ) p1 p2 = map fst (p1 @@@ p2)

let list_of_pair (a, b) = (Seq.cons a b)

(** Cons results from [x_p] and [xs_p] into Seq.t *)
let ( >:: ) p_head p_tail = map list_of_pair (Sequ (p_head, p_tail))

(** Kleene star *)
let iter p = recursively (fun self -> Return Seq.empty ||| (p >:: self))

(** Kleene plus *)
let iter1 p = p >:: (iter p)

let between (p:('a,'b) parser) =
  let rec between p = function
  | [] -> assert false
  | [ k ] -> kw k <@@ (Return Seq.empty)
  | k :: ks -> kw k <@@ (p >:: (between p ks))
in (between p)

(* Auxiliary functions *)
let cons_back xs x = Seq.append xs (Seq.return x)

let seq_fold_right f s acc = 
  let rec aux acc s = 
    match Seq.uncons s with
    | None -> acc
    | Some (x, xs) -> f x (aux acc xs)
  in aux acc s

(* Core of parsing *)

let rec expr (env : Environment.parser_context) e =
  let open ListMonad in
  match e with
  | Presyntax.Var x ->
    if Environment.identifier_present env x then 
      Seq.return @@ Syntax.Var x
    else
      Seq.empty
  | Presyntax.Seq es ->
    let context_parser = get_parser env in
    let* tt = runParser context_parser es in
    return @@ fst tt
  | Presyntax.Int k -> return @@ Syntax.Int k
  | Presyntax.Bool b -> return @@ Syntax.Bool b
  | Presyntax.Nil ht -> return @@ Syntax.Nil ht
  | Presyntax.Times (e1, e2) ->
    let* e1 = expr env e1 in
    let* e2 = expr env e2 in
    return @@ Syntax.Times (e1, e2)
  | Presyntax.Divide (e1, e2) ->
    let* e1 = expr env e1 in
    let* e2 = expr env e2 in
    return @@ Syntax.Divide (e1, e2)
  | Presyntax.Mod (e1, e2) ->
    let* e1 = expr env e1 in
    let* e2 = expr env e2 in
    return @@ Syntax.Mod (e1, e2)
  | Presyntax.Plus (e1, e2) ->
    let* e1 = expr env e1 in
    let* e2 = expr env e2 in
    return @@ Syntax.Plus (e1, e2)
  | Presyntax.Minus (e1, e2) ->
    let* e1 = expr env e1 in
    let* e2 = expr env e2 in
    return @@ Syntax.Minus (e1, e2)
  | Presyntax.Equal (e1, e2) ->
    let* e1 = expr env e1 in
    let* e2 = expr env e2 in
    return @@ Syntax.Equal (e1, e2)
  | Presyntax.Less (e1, e2) ->
    let* e1 = expr env e1 in
    let* e2 = expr env e2 in
    return @@ Syntax.Less (e1, e2)
  | Presyntax.If (e1, e2, e3) ->
    let* e1 = expr env e1 in
    let* e2 = expr env e2 in
    let* e3 = expr env e3 in
    return @@ Syntax.If (e1, e2, e3)
  | Presyntax.Fun (name, ht, e) ->
    let env = Environment.add_identifier_token env name in
    let* e = expr env e in
    return @@ Syntax.Fun (name, ht, e)
  | Presyntax.Pair (e1, e2) ->
    let* e1 = expr env e1 in
    let* e2 = expr env e2 in
    return @@ Syntax.Pair (e1, e2)
  | Presyntax.Fst e ->
    let* e = expr env e in
    return @@ Syntax.Fst e
  | Presyntax.Snd e ->
    let* e = expr env e in
    return @@ Syntax.Snd e
  | Presyntax.Rec (x, ht, e) ->
    let* e = expr env e in
    return @@ Syntax.Rec (x, ht, e)
  | Presyntax.Cons (e1, e2) ->
    let* e1 = expr env e1 in
    let* e2 = expr env e2 in
    return @@ Syntax.Cons (e1, e2)
  | Presyntax.Match (e, ht, e1, x, y, e2) ->
    let* e = expr env e in
    let* e1 = expr env e1 in
    let env2 =
      Environment.add_identifier_token
        (Environment.add_identifier_token env y)
        x
    in
    let* e2 = expr env2 e2 in
    return @@ Syntax.Match (e, ht, e1, x, y, e2)

and app_parser env : (Presyntax.expr, Syntax.expr) parser =
  let open ListMonad in
  let rec parse_arguments args = 
    match Seq.uncons args with
    | None -> return Seq.empty (* equivalent to fail *)
    | Some (arg0 ,args) ->
      let* arg0 = expr env arg0 in
      let* args = parse_arguments args in
      return @@ Seq.cons arg0 args
  in

  let parse_application (presyntaxl : Presyntax.expr Seq.t) =
    match Seq.uncons presyntaxl with
    | None -> fail
    | Some (h, tail) ->
      let* h = expr env h in
      let* args = parse_arguments tail in
      return @@ Syntax.make_app h args
  in

  flat_map parse_application (iter1 Get)

and get_parser env :
  (Presyntax.expr, Syntax.expr) parser =
  let g = env.operators in
  let rec graph_parser (g : Precedence.graph) :
    (Presyntax.expr, Syntax.expr) parser =
    recursively (fun self ->
      let rec precedence_parser stronger operators =
        let operator_parser stronger_parser op =
          let op_name = Syntax.Var (Syntax.name_of_operator op) in
          let make_operator_app = Syntax.make_app op_name in
          let between_parser = between self @@ 
            List.map (fun x -> Presyntax.Var x) op.tokens in
          match op with

          | { fx = Closed; _ } ->
            map make_operator_app between_parser

          | { fx = Postfix; _ } ->
            map
              (fun (head, tails) ->
                Seq.fold_left
                  (fun arg0 args -> make_operator_app @@ Seq.cons arg0 args)
                  head tails)
              (Sequ (stronger_parser, iter1 between_parser))

          | { fx = Prefix; _ } ->
            map
              (fun (heads, tail) ->
                seq_fold_right
                  (fun args argZ -> make_operator_app @@ cons_back args argZ)
                  heads tail)
              (Sequ (iter1 between_parser, stronger_parser))

          | { fx = Infix NonAssoc; _ } ->
            map
              (fun (a, (mid, b)) ->
                let args = cons_back (Seq.cons a mid) b in (* [a] ++ mid ++ [b] *)
                make_operator_app args)
              (Sequ ( stronger_parser,
                Sequ (between_parser, stronger_parser) ))

          | { fx = Infix LeftAssoc; _ } ->
            (* (_A_)A_ -> First token has to be of upper parsing level.  *)
            map 
              (fun (a, bs) ->
                match Seq.uncons bs with
                | None -> failwith "Iter1 missimplementation"
                | Some (head, tails) ->
                  let left = make_operator_app @@ Seq.cons a head in
                  Seq.fold_left
                    (fun a b -> make_operator_app @@ Seq.cons a b)
                    left tails)

              (Sequ (stronger_parser,
                map
                  (Seq.map (fun (a, b) -> cons_back a b))
                  (iter1 @@ Sequ (between_parser, stronger_parser))
              ))

          | { fx = Infix RightAssoc; _ } ->
            (* _A(_A_) -> Last token has to be of upper parsing level.  *)
            map
              (fun (s, b) ->
                match Seq.uncons s with
                | None -> failwith "Iter1 missimplementation"
                | Some (head, tails) ->
                  let right = make_operator_app @@ cons_back head b in
                  seq_fold_right
                    (fun b a -> make_operator_app @@ cons_back b a)
                    tails right)
              (Sequ(
                map
                  (Seq.map (fun (a, b) -> Seq.cons a b))
                  (iter1 @@ Sequ (stronger_parser, between_parser)),
                stronger_parser
              ))
        in
        match operators with
        | [] -> Fail
        | o :: os ->
          operator_parser stronger o ||| precedence_parser stronger os
      in
      match g with
      | [] -> app_parser env
      | p :: ps ->
        let sucs = graph_parser ps in
        precedence_parser sucs (snd p) ||| sucs)
  in
  graph_parser g @@< Eof

  (* let t = graph_parser g @@< Eof
in string_of_parser t |> print_endline; t *)