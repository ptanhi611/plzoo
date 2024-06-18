(* Parser combinatorji *)

module ListMonad = struct

  let return = Seq.return

  let ( >>= ) x f = Seq.concat_map f x

  let ( let* ) = ( >>= )

  let fail = Seq.empty

end

module ParserMonad : sig
  type ('token, 'a) t = 'token Seq.t -> ('a * 'token Seq.t) Seq.t

  val return : 'a -> ('token, 'a) t
  val fail : ('token, 'a) t
  val eof : ('token, unit) t
  val get : ('token, 'token) t
  val ( ++ ) : ('token, 'a) t -> ('token, 'a) t -> ('token, 'a) t
  val ( let* ) : ('token, 'a) t -> ('a -> ('token, 'b) t) -> ('token, 'b) t
  val ( >>= ) : ('token, 'a) t -> ('a -> ('token, 'b) t) -> ('token, 'b) t
end = struct
  type ('token, 'a) t = 'token Seq.t -> ('a * 'token Seq.t) Seq.t

  let return x inp = Seq.return (x, inp)

  let ( >>= ) (p : ('token, 'a) t) (f : 'a -> ('token, 'b) t) : ('token, 'b) t =
    fun inp ->
      Seq.flat_map (fun (x, inp) -> f x inp) (p inp)

  let ( let* ) = ( >>= )

  (** Fail parser directly fails. (Returns [[]]) *)
  let fail = fun _ -> Seq.empty

  (** Gets next token from the stream *)
  let get inp =
    match Seq.uncons inp with
    | None -> Seq.empty
    | Some (t,ts) -> Seq.return (t, ts)

   let eof inp =
     match Seq.uncons inp with
     | None -> (Seq.return ((), Seq.empty))
     | Some _ -> Seq.empty

  let ( ++ ) c1 c2 inp = Seq.append (c1 inp) (c2 inp)
end

open ParserMonad

let check_success lst =
  match Seq.uncons lst with
  | None -> failwith "could not parse"
  | Some (a,tail) -> a

let first (p:('a,'b) t) =
  fun inp -> match Seq.uncons (p inp) with
    | None -> Seq.empty
    | Some(a, _) -> Seq.return a

let return_many xs inp = Seq.map (fun x -> (x, inp)) xs

(** Flat Map. [f p] Creates a parser that maps f over result of p and returns all the individual results. *)
let flat_map f p =
  let* x = p in
  return_many @@ f x

(** Recursively. [recursively f] Creates a parser that can refer to itself. *)
let recursively build =
  let rec self x = build self x in
  self

(** Map. [map f p] Creates a parser that maps f over result of p *)
let map f p = flat_map (fun x -> Seq.return (f x)) p

(** Map_opt. [map_opt f p] Creates a parser that maps f over result of p, but only if f is not None *)
let map_opt f p = flat_map
  (fun x -> match f x with
  | Some t -> Seq.return t
  | None -> Seq.empty) p

let kw k =
  let* v = get in
  if v == k then return v
  else fail

(** Option to choose from either parse result of [p1] pr [p2] *)
let ( || ) p1 p2 = p1 ++ p2 ;;

(** Concatenation of parsers, returning a pair *)
let ( @@@ ) p1 p2 =
  let* x = p1 in
  let* y = p2 in
  return (x,y)

let sequ a b = a @@@ b  (* TODO! To gre VEN*)

(** Concatenation of parsers, discarding left *)
let ( <@@ ) p1 p2 =
  let* _ = p1 in
  let* x = p2 in
  return x

(** Concatenation of parsers, discarding right *)
let ( @@< ) p1 p2 =
  let* x = p1 in
  let* _ = p2 in
  return x

let mapf f p =
  let* x = p in
  return_many (f x)

(** Kleene star *)
let rec iter p = (
  let* x = p in
  let* xs = iter p in
  return @@ Seq.cons x xs
) ++ (return @@ Seq.empty)

(** Kleene plus *)
let iter1 p =
  let* x = p in
  let* xs = iter p in
  return @@ Seq.cons x xs

let between p =
  let rec between p = function
  | [] -> assert false
  | [ k ] -> kw k <@@ (return Seq.empty)
  | k :: ks -> kw k <@@ (
    let* arg0 = p in
    let* args = between p ks in
    return @@ Seq.cons arg0 args)
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
    Seq.iter (fun e -> print_string (Presyntax.string_of_expr e ^ " ")) es;
    print_newline ();
    let context_parser = get_env_parser env in
    let* tt = context_parser es in
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

and app_parser env : (Presyntax.expr, Syntax.expr) t =
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

  (flat_map parse_application (iter1 get))

and get_env_parser env :
  (Presyntax.expr, Syntax.expr) t =
  let rec graph_parser (g : Precedence.graph) inp =
      let rec precedence_parser stronger operators =
        let operator_parser stronger_parser op =
          let op_name = Syntax.Var (Syntax.name_of_operator op) in
          let make_operator_app = Syntax.make_app op_name in
          let between_parser = between (graph_parser g) @@
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
              (sequ stronger_parser @@ iter1 between_parser)

          | { fx = Prefix; _ } ->
            map
              (fun (heads, tail) ->
                seq_fold_right
                  (fun args argZ -> make_operator_app @@ cons_back args argZ)
                  heads tail)
              (sequ (iter1 between_parser) stronger_parser)

          | { fx = Infix NonAssoc; _ } ->
            map
              (fun (a, (mid, b)) ->
                let args = cons_back (Seq.cons a mid) b in (* [a] ++ mid ++ [b] *)
                make_operator_app args)
              (sequ stronger_parser @@ sequ between_parser stronger_parser )

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

              (sequ stronger_parser @@
                map
                  (Seq.map (fun (a, b) -> cons_back a b))
                  (iter1 @@ sequ between_parser stronger_parser)
              )

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
              (sequ
                (map
                  (Seq.map (fun (a, b) -> Seq.cons a b))
                  (iter1 (sequ stronger_parser between_parser)))
                stronger_parser)
        in
        match operators with
        | [] -> fail
        | o :: os -> (operator_parser stronger o) ++ (precedence_parser stronger os)
      in
      match g with
      | [] -> app_parser env inp
      | p :: ps ->
        let sucs = graph_parser ps in
        (precedence_parser sucs (snd p)) ++ sucs @@ inp
  in
  (graph_parser env.operators) @@< eof

  (* let t = graph_parser g @@< Eof
in string_of_parser t |> print_endline; t *)
