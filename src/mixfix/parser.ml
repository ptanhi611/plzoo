(* Parser combinatorji *)

module ListMonad = struct
  let return x = [ x ]
  let ( let* ) xs f = List.concat_map f xs
  let fail = []
end

let wrap rs ts = List.map (fun x -> (x, ts)) rs

let rec unwrap = function
  | [] -> []
  | (r, []) :: rs -> r :: unwrap rs
  | (_, _ :: _) :: rs -> unwrap rs

type ('token, 'a) t = 'token list -> ('a * 'token list) list

module ParserMonad : sig
  val return : 'a -> ('token, 'a) t
  val fail : ('token, 'a) t
  val eof : ('token, unit) t
  val get : ('token, 'token) t
  val ( ||| ) : ('token, 'a) t -> ('token, 'a) t -> ('token, 'a) t
  val ( let* ) : ('token, 'a) t -> ('a -> ('token, 'b) t) -> ('token, 'b) t
  val ( >>= ) : ('token, 'a) t -> ('a -> ('token, 'b) t) -> ('token, 'b) t
end = struct
  let return x inp = [ (x, inp) ]

  let ( >>= ) (p : ('token, 'a) t) (f : 'a -> ('token, 'b) t) : ('token, 'b) t =
   fun inp ->
    let g (x, rest) = (f x) rest in
    List.concat_map g (p inp)

  let ( let* ) = ( >>= )

  (** Fail parser directly fails. (Returns [[]]) *)
  let fail : ('token, 'a) t = fun _ -> []

  (** Gets next token from the stream *)
  let get : ('token, 'token) t = function [] -> [] | t :: ts -> [ (t, ts) ]

  let ( ||| ) c1 c2 s = c1 s @ c2 s
  let eof = function [] -> [ ((), []) ] | _ -> []
end

open ParserMonad

let check_success lst =
  match lst with
  | [] -> Zoo.error "could not parse"
  | [ r ] -> r
  | _ :: _ :: _ as e ->
      print_endline (String.concat "\n" (List.map Syntax.string_of_expr e));
      Zoo.error "ambiguous parse"

type (_, _) parser =
  | Fail : ('a, 'b) parser
  | Return : 'b -> ('a, 'b) parser
  | Cons : ('a, 'b) parser * ('a, 'c) parser -> ('a, 'b * 'c) parser
  | Or : ('a, 'b) parser * ('a, 'b) parser -> ('a, 'b) parser
  | Map : ('b -> 'c) * ('a, 'b) parser -> ('a, 'c) parser
  | Sat : ('a -> bool) * ('a, 'a) parser -> ('a, 'a) parser
  | Between : ('a, 'b) parser * 'a list -> ('a, 'b list) parser
  | Lazy : ('a, 'b) parser lazy_t -> ('a, 'b) parser
  | Get : ('a, 'a) parser
  | Split : ('a, 'b list) parser -> ('a, 'b) parser

(** Smart parser constructors *)

let recursively build =
  let rec self = lazy (build self) in
  Lazy.force self

let kw k = Sat (( = ) k, Get)

(** Concatenation of parsers, returning a pair *)
let ( @@@ ) p1 p2 = Cons (p1, p2)

(** Concatenation of parsers, discarding left *)
let ( >@@ ) p1 p2 = Map (snd, p1 @@@ p2)

(** Concatenation of parsers, discarding right *)
let ( @@< ) p1 p2 = Map (fst, p1 @@@ p2)

(** Map. [f <$> p] Creates a parser that maps f over result of p *)
let ( <$> ) f x_parser = Map (f, x_parser)

(** Parse once with unit parser [p] and yield v*)
let ( >> ) p v = p >@@ Return v

let list_of_pair (a, b) = a :: b
let concat x_p xs_p = list_of_pair <$> Cons (x_p, xs_p)
let iter p = recursively (fun self -> Or (Return [], concat p (Lazy self)))
let iter1 p = concat p (iter p)

(** Between that maps to presyntax *)
let betweenp p k =
  let k = List.map (fun x -> Presyntax.Var x) k in
  Between (p, k)

let rec runParser : type a b. (a, b) parser -> (a, b) t = function
  | Fail -> fail
  | Return t -> return t
  | Get -> get
  | Lazy (lazy p) -> runParser p
  | Sat (pred, p) ->
      let* x = runParser p in
      if pred x then return x else fail
  | Or (p, q) -> runParser p ||| runParser q
  | Cons (p, q) ->
      let* x = runParser p in
      let* y = runParser q in
      return (x, y)
  | Map (f, x) ->
      let* x = runParser x in
      return (f x)
  | Between (p, []) -> assert false
  | Between (p, [ k ]) -> runParser (kw k >> [])
  | Between (p, k :: ks) -> runParser @@ (kw k >@@ concat p (Between (p, ks)))
  | Split p ->
      let* xs = runParser p in
      fun inp -> List.map (fun x -> (x, inp)) xs

let foldl f p =
  Map
    ( (function
      | [] -> [] | [ x ] -> [ x ] | x :: xs -> [ List.fold_left f x xs ]),
      p )

let foldr f p = Map ((function [] -> [] | [ x ] -> x | x :: xs -> f xs x), p)

let rec parse_one_presyntax (env : Environment.parser_context) e :
    Syntax.expr list =
  let open ListMonad in
  match e with
  | Presyntax.Var x ->
      if Environment.identifier_present env x then return @@ Syntax.Var x
      else fail
  | Presyntax.Seq es ->
      let context_parser = get_parser env in
      unwrap @@ runParser context_parser es
  | Presyntax.Int k -> return @@ Syntax.Int k
  | Presyntax.Bool b -> return @@ Syntax.Bool b
  | Presyntax.Nil ht -> return @@ Syntax.Nil ht
  | Presyntax.Times (e1, e2) ->
      let* e1 = parse_one_presyntax env e1 in
      let* e2 = parse_one_presyntax env e2 in
      return @@ Syntax.Times (e1, e2)
  | Presyntax.Divide (e1, e2) ->
      let* e1 = parse_one_presyntax env e1 in
      let* e2 = parse_one_presyntax env e2 in
      return @@ Syntax.Divide (e1, e2)
  | Presyntax.Mod (e1, e2) ->
      let* e1 = parse_one_presyntax env e1 in
      let* e2 = parse_one_presyntax env e2 in
      return @@ Syntax.Mod (e1, e2)
  | Presyntax.Plus (e1, e2) ->
      let* e1 = parse_one_presyntax env e1 in
      let* e2 = parse_one_presyntax env e2 in
      return @@ Syntax.Plus (e1, e2)
  | Presyntax.Minus (e1, e2) ->
      let* e1 = parse_one_presyntax env e1 in
      let* e2 = parse_one_presyntax env e2 in
      return @@ Syntax.Minus (e1, e2)
  | Presyntax.Equal (e1, e2) ->
      let* e1 = parse_one_presyntax env e1 in
      let* e2 = parse_one_presyntax env e2 in
      return @@ Syntax.Equal (e1, e2)
  | Presyntax.Less (e1, e2) ->
      let* e1 = parse_one_presyntax env e1 in
      let* e2 = parse_one_presyntax env e2 in
      return @@ Syntax.Less (e1, e2)
  | Presyntax.If (e1, e2, e3) ->
      let* e1 = parse_one_presyntax env e1 in
      let* e2 = parse_one_presyntax env e2 in
      let* e3 = parse_one_presyntax env e3 in
      return @@ Syntax.If (e1, e2, e3)
  | Presyntax.Fun (name, ht, e) ->
      let env = Environment.add_identifier_token env name in
      let* e = parse_one_presyntax env e in
      return @@ Syntax.Fun (name, ht, e)
  | Presyntax.Pair (e1, e2) ->
      let* e1 = parse_one_presyntax env e1 in
      let* e2 = parse_one_presyntax env e2 in
      return @@ Syntax.Pair (e1, e2)
  | Presyntax.Fst e ->
      let* e = parse_one_presyntax env e in
      return @@ Syntax.Fst e
  | Presyntax.Snd e ->
      let* e = parse_one_presyntax env e in
      return @@ Syntax.Snd e
  | Presyntax.Rec (x, ht, e) ->
      let* e = parse_one_presyntax env e in
      return @@ Syntax.Rec (x, ht, e)
  | Presyntax.Cons (e1, e2) ->
      let* e1 = parse_one_presyntax env e1 in
      let* e2 = parse_one_presyntax env e2 in
      return @@ Syntax.Cons (e1, e2)
  | Presyntax.Match (e, ht, e1, x, y, e2) ->
      let* e = parse_one_presyntax env e in
      let* e1 = parse_one_presyntax env e1 in
      let env2 =
        Environment.add_identifier_token
          (Environment.add_identifier_token env y)
          x
      in
      let* e2 = parse_one_presyntax env2 e2 in
      return @@ Syntax.Match (e, ht, e1, x, y, e2)

and app_parser env : (Presyntax.expr, Syntax.expr) parser =
  (*
    app_parser env -> Moramo narediti parser, ki sprejme Presyntax.expr in vrača Syntax.expr   
   *)
  let open ListMonad in
  let f (presyntaxl : Presyntax.expr list) =
    match presyntaxl with
    | [] -> fail
    | h :: args ->
        let rec map_expr = function
          | [] -> return []
          | arg :: args ->
              let* arg = parse_one_presyntax env arg in
              let* args = map_expr args in
              return (arg :: args)
        in
        let* h = parse_one_presyntax env h in
        let* args = map_expr args in
        return @@ Syntax.make_app h args
  in
  Split (Map (f, iter1 Get))
(* TODO! Maybe Iter *)

and get_parser env : (Presyntax.expr, Syntax.expr) parser =
  let g = env.operators in

  let rec graph_parser (g : Precedence.graph) :
      (Presyntax.expr, Syntax.expr) parser =
    recursively (fun self ->
        let rec precedence_parser stronger operators =
          let operator_parser stronger_parser op =
            let ophead = Syntax.Var (Syntax.op_name op) in
            match op with
            | Syntax.{ fx = Closed; tokens } ->
                Map (Syntax.make_app ophead, betweenp (Lazy self) tokens)
            | { fx = Postfix; tokens } ->
                Map
                  ( (fun (head, tails) ->
                      List.fold_left
                        (fun a b -> Syntax.make_app ophead (a :: b))
                        head tails),
                    Cons (stronger_parser, iter1 (betweenp (Lazy self) tokens))
                  )
            | { fx = Prefix; tokens } ->
                Map
                  ( (fun (tails, head) ->
                      List.fold_right
                        (fun b a -> Syntax.make_app ophead (b @ [ a ]))
                        tails head),
                    Cons (iter1 @@ betweenp (Lazy self) tokens, stronger_parser)
                  )
            | { fx = Infix NonAssoc; tokens } ->
                Map
                  ( (fun (a, (mid, b)) ->
                      Syntax.make_app ophead ((a :: mid) @ [ b ])),
                    Cons
                      ( stronger_parser,
                        Cons (betweenp (Lazy self) tokens, stronger_parser) ) )
            | { fx = Infix LeftAssoc; tokens } ->
                Map
                  ( (function
                    | a, [] -> failwith "Iter1 isn't working"
                    | a, head :: tails ->
                        let left = Syntax.make_app ophead (a :: head) in
                        List.fold_left
                          (fun a b -> Syntax.make_app ophead (a :: b))
                          left tails),
                    Cons
                      ( stronger_parser,
                        Map
                          ( List.map (fun (a, b) -> a @ [ b ]),
                            iter1
                              (Cons
                                 (betweenp (Lazy self) tokens, stronger_parser))
                          ) ) )
            | { fx = Infix RightAssoc; tokens } ->
                Map
                  ( (function
                    | [], b -> failwith "Iter1 isn't working"
                    | head :: tails, b ->
                        let right = Syntax.make_app ophead (head @ [ b ]) in
                        List.fold_right
                          (fun b a -> Syntax.make_app ophead (b @ [ a ]))
                          tails right),
                    Cons
                      ( Map
                          ( List.map (fun (a, b) -> a :: b),
                            iter1
                              (Cons
                                 (stronger_parser, betweenp (Lazy self) tokens))
                          ),
                        stronger_parser ) )
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
       | Cons (p1, p2) -> "Cons (" ^ string_of_parser' p1 ^ ", " ^ string_of_parser' p2 ^ ")"
       | Or (p1, p2) -> "Or (" ^ string_of_parser' p1 ^ ", " ^ string_of_parser' p2 ^ ")"
       | Map (_, p) -> "Map (_, " ^ string_of_parser' p ^ ")"
       | Between (p, ks) -> "Between (" ^ string_of_parser' p ^ ", " ^ String.concat ", " ks ^ ")"
       | Lazy _ -> "Lazy"
       | Get -> "Get"
       | Split p -> "Split (" ^ string_of_parser' p ^ ")"
     in string_of_parser' p *)
