(* Parser combinatorji *)

module LList = struct

  let return = Seq.return

  let ( >>= ) x f = Seq.concat_map f x

  let ( let* ) = ( >>= )

  let fail = Seq.empty

end

let take_unambigous = 
  Seq.filter_map (
    fun (p, s) -> 
      match Seq.uncons s with
      | None -> Some p
      | Some _ -> None
  )

let cons_back xs x = Seq.append xs (Seq.return x)

let seq_fold_right f s acc = 
  let rec aux acc s = 
    match Seq.uncons s with
    | None -> acc
    | Some (x, xs) -> f x (aux acc xs)
  in aux acc s

type ('token, 'a) t = 'token Seq.t -> ('a * 'token Seq.t) Seq.t

module ParserMonad : sig
  val return : 'a -> ('token, 'a) t
  val fail : ('token, 'a) t
  val eof : ('token, unit) t
  val get : ('token, 'token) t
  val ( +++ ) : ('token, 'a) t -> ('token, 'a) t -> ('token, 'a) t
  val ( let* ) : ('token, 'a) t -> ('a -> ('token, 'b) t) -> ('token, 'b) t
  val ( >>= ) : ('token, 'a) t -> ('a -> ('token, 'b) t) -> ('token, 'b) t
end = struct
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
    print_endline (String.concat "\n" (List.map Syntax.string_of_expr e));
    Zoo.error "ambiguous parse"

type (_, _) parser =
  | Fail : ('a, 'b) parser
  | Return : 'b -> ('a, 'b) parser
  | Sequ : ('a, 'b) parser * ('a, 'c) parser -> ('a, 'b * 'c) parser
  | Or : ('a, 'b) parser * ('a, 'b) parser -> ('a, 'b) parser
  | Map : ('b -> 'c) * ('a, 'b) parser -> ('a, 'c) parser
  | Kw : 'a -> ('a, 'a) parser
  | Between : ('a, 'b) parser * 'a list -> ('a, 'b Seq.t) parser
  | Lazy : ('a, 'b) parser lazy_t -> ('a, 'b) parser
  | Get : ('a, 'a) parser
  | Eof : ('a, unit) parser (* TODO Ven? *)
  | Split : ('a, 'b Seq.t) parser -> ('a, 'b) parser

(** Smart parser constructors *)

let recursively build =
  let rec self = lazy (build (Lazy self)) in
  Lazy.force self

let kw k = Kw k

(** Concatenation of parsers, returning a pair *)
let ( @@@ ) p1 p2 = Sequ (p1, p2)

(** Concatenation of parsers, discarding left *)
let ( >@@ ) p1 p2 = Map (snd, p1 @@@ p2)

(** Concatenation of parsers, discarding right *)
let ( @@< ) p1 p2 = Map (fst, p1 @@@ p2)
  
(** Map. [f <$> p] Creates a parser that maps f over result of p *)
let ( <$> ) f x_parser = Map (f, x_parser)

(** Parse once with parser [p] and yield v*)
let ( >> ) p v = p >@@ Return v

let list_of_pair (a, b) = Seq.cons a b

let concat_parser x_p xs_p = list_of_pair <$> Sequ (x_p, xs_p)

let iter p = recursively (fun self -> Or (Return Seq.empty, concat_parser p self))

let iter1 p = concat_parser p (iter p)

(** Between that maps to presyntax *)
let betweenp p k =
  let k = List.map (fun x -> Presyntax.Var x) k in
  Between (p, k)

let rec runParser : type a b. (a, b) parser -> (a, b) t = function
  | Fail -> fail
  | Return t -> return t
  | Get -> get
  | Eof -> eof
  | Lazy (lazy p) -> runParser p

  | Kw k -> 
    let* x = get in
    if x = k then
      return k
    else
      fail

  | Or (p, q) -> runParser p +++ runParser q
  | Sequ (p, q) ->
    let* x = runParser p in
    let* y = runParser q in
    return (x, y)

  | Map (f, p) ->
    let* x = runParser p in
    return @@ f x

  | Between (p, []) -> assert false
  | Between (p, [ k ]) -> runParser (kw k >> Seq.empty)
  | Between (p, k :: ks) -> runParser (kw k >@@ concat_parser p (Between (p, ks)))


  | Split p ->
    let* xs = (runParser p) in
    fun inp -> Seq.map (fun x -> (x, inp)) xs

let rec expr (env : Environment.parser_context) e =
  let open LList in
  match e with
  | Presyntax.Var x ->
    if Environment.identifier_present env x then return @@ Syntax.Var x
    else fail
  | Presyntax.Seq es ->
    let context_parser = get_parser env in
    take_unambigous
      (
        let* tt = runParser context_parser es in
        return tt
      )
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
  (*
    app_parser env -> Moramo narediti parser, ki sprejme Presyntax.expr in vrača Syntax.expr   
   *)
  let open LList in
  let rec parse_arguments presyntaxl = 
    match Seq.uncons presyntaxl with
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
  Split (Map (parse_application, iter1 Get))
(* TODO! Maybe Iter *)

and get_parser env : (Presyntax.expr, Syntax.expr) parser =
  let g = env.operators in

  let rec graph_parser (g : Precedence.graph) :
    (Presyntax.expr, Syntax.expr) parser =
    recursively (fun self ->
      let rec precedence_parser stronger operators =
        let operator_parser stronger_parser op =
          let op_name = Syntax.Var (Syntax.name_of_operator op) in
          match op with


          | { fx = Closed; tokens } ->
            Map (Syntax.make_app op_name, betweenp self tokens)


          | { fx = Postfix; tokens } ->
            Map (
                (fun (head, tails) ->
                  Seq.fold_left
                    (fun arg0 args -> Syntax.make_app op_name (Seq.cons arg0 args))
                    head tails
                ),
                Sequ (stronger_parser, iter1 @@ betweenp self tokens)
              )


          | { fx = Prefix; tokens } ->
            Map (
              (fun (heads, tail) ->
                seq_fold_right
                  (fun args argZ -> Syntax.make_app op_name (cons_back args argZ))
                  heads tail),
                Sequ (iter1 @@ betweenp self tokens, stronger_parser)
              )


          | { fx = Infix NonAssoc; tokens } ->
            Map
              ( (fun (a, (mid, b)) ->
                let args = cons_back (Seq.cons a mid) b in (* [a] ++ mid ++ [b] *)
                Syntax.make_app op_name args),
                Sequ ( stronger_parser,
                  Sequ (betweenp self tokens, stronger_parser) )
              )


          | { fx = Infix LeftAssoc; tokens } ->
            (* (_A_)A_ -> First token has to be of upper parsing level.  *)
            Map
              (
                (
                  fun (a, bs) ->
                  match Seq.uncons bs with
                  | None -> failwith "Iter1 missimplementation"
                  | Some (head, tails) ->
                    let left = Syntax.make_app op_name (Seq.cons a head) in
                    Seq.fold_left
                      (fun a b -> Syntax.make_app op_name (Seq.cons a b))
                      left tails
                ),

                Sequ ( stronger_parser,
                  Map ( Seq.map (fun (a, b) -> cons_back a b),
                    iter1 @@ Sequ (betweenp self tokens, stronger_parser)
                  )
                )
              )


          | { fx = Infix RightAssoc; tokens } ->
            Map
              (
                (fun (s, b) ->
                  match Seq.uncons s with
                  | None -> failwith "Iter1 missimplementation"
                  | Some (head, tails) ->
                    let right = Syntax.make_app op_name (cons_back head b) in
                    seq_fold_right
                      (fun b a -> Syntax.make_app op_name (cons_back b a))
                      tails right),

                Sequ (
                  Map (
                    Seq.map (fun (a, b) -> Seq.cons a b),
                    iter1 @@ Sequ (stronger_parser, betweenp self tokens)
                  ),
                  stronger_parser
                )
              )


        in
        match operators with
        | [] -> Fail
        | o :: os ->
          Or (operator_parser stronger o, precedence_parser stronger os)
      in
      match g with
      | [] -> app_parser env
      | p :: ps ->
        let sucs = graph_parser ps in
        Or (precedence_parser sucs (snd p), sucs))
  in
  graph_parser g

(*
   let string_of_parser p:(('a, 'b) t) =
     let rec string_of_parser' = function
       | Fail -> "Fail"
       | Return -> "Return"
       | Kw k -> "Kw " ^ Presyntax.string_of_expr k
       | Pair (p1, p2) -> "Pair (" ^ string_of_parser' p1 ^ ", " ^ string_of_parser' p2 ^ ")"
       | Or (p1, p2) -> "Or (" ^ string_of_parser' p1 ^ ", " ^ string_of_parser' p2 ^ ")"
       | Map (_, p) -> "Map (_, " ^ string_of_parser' p ^ ")"
       | Between (p, ks) -> "Between (" ^ string_of_parser' p ^ ", " ^ String.concat ", " ks ^ ")"
       | Lazy _ -> "Lazy"
       | Get -> "Get"
       | Split p -> "Split (" ^ string_of_parser' p ^ ")"
     in string_of_parser' p *)
