(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators

(* Simple expressions: syntax and semantics *)
module Expr =
  struct

    (* The type for expressions. Note, in regular OCaml there is no "@type..."
       notation, it came from GT.
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* State: a partial map from variables to integer values. *)
    type state = string -> int

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

    (* Expression evaluator

          val eval : state -> t -> int

       Takes a state and an expression, and returns the value of the expression in
       the given state.
    *)
    let bool_to_int e = if e then 1 else 0
    let int_to_bool e = e != 0

    let rec eval st ex = match ex with
      | Const c -> c
      | Var   v -> st v
      | Binop (op, left, right) ->
        let left_val = eval st left in
        let right_val = eval st right in
        match op with
          | "+"  -> left_val +  right_val
          | "-"  -> left_val -  right_val
          | "*"  -> left_val *  right_val
          | "/"  -> left_val /  right_val
          | "%"  -> left_val mod  right_val

          | "<"  -> bool_to_int ( left_val <  right_val )
          | "<=" -> bool_to_int ( left_val <= right_val )
          | ">"  -> bool_to_int ( left_val >  right_val )
          | ">=" -> bool_to_int ( left_val >= right_val )
          | "==" -> bool_to_int ( left_val == right_val )
          | "!=" -> bool_to_int ( left_val != right_val )

          | "&&" -> bool_to_int (int_to_bool ( left_val ) && int_to_bool ( right_val ))
          | "!!" -> bool_to_int (int_to_bool ( left_val ) || int_to_bool ( right_val ))

          | _    -> failwith "wtf?"

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string

    *)
    ostap (
      expr:
        !(Ostap.Util.expr
           (fun x -> x)
           [|
             `Lefta , [ostap ("!!"), (fun x y -> Binop ("!!", x, y))];
             `Lefta , [ostap ("&&"), (fun x y -> Binop ("&&", x, y))];

             `Nona  , [ostap ("<="), (fun x y -> Binop ("<=", x, y));
                       ostap ("<" ), (fun x y -> Binop ("<" , x, y));
                       ostap (">="), (fun x y -> Binop (">=", x, y));
                       ostap (">" ), (fun x y -> Binop (">" , x, y));
                       ostap ("=="), (fun x y -> Binop ("==", x, y));
                       ostap ("!="), (fun x y -> Binop ("!=", x, y))];

             `Lefta , [ostap ("+" ), (fun x y -> Binop ("+" , x, y));
                       ostap ("-" ), (fun x y -> Binop ("-" , x, y))];

             `Lefta , [ostap ("*" ), (fun x y -> Binop ("*" , x, y));
                       ostap ("/" ), (fun x y -> Binop ("/" , x, y));
                       ostap ("%" ), (fun x y -> Binop ("%" , x, y))];

           |]
           atom
         );
      atom : x:IDENT {Var x} | x:DECIMAL {Const x} | -"(" expr -")"
    )

  end

(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list

    (* Statement evaluator

         val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval (mp, i, o) st = match st with
       | Read var            -> begin match i with
                                  | x :: tl -> (Expr.update var x mp, tl, o)
                                  | []      -> failwith "not enough input"
                                end
       | Write ex            -> (mp, i, o @ [Expr.eval mp ex])
       | Assign (var, ex)    -> (Expr.update var (Expr.eval mp ex) mp, i, o)
       | Seq (st1, st2)      -> let new_conf = eval (mp, i, o) st1
                                in
                                  eval new_conf st2
       | Skip                -> (mp, i, o)
       | If (cond, th, el)   -> let cond_val = Expr.eval mp cond
                                in eval (mp, i, o) (if cond_val != 0 then th else el)
       | While (cond, todo)  -> let cond_val = Expr.eval mp cond
                                in
                                  if cond_val != 0
                                  then
                                    let new_conf = eval (mp, i, o) todo
                                    in eval new_conf (While (cond, todo))
                                  else (mp, i, o)
       | Repeat (todo, cond) -> let new_conf = eval (mp, i, o) todo in
                                let (new_mp, _, _) = new_conf
                                in eval new_conf (if (Expr.eval new_mp cond) == 0 then (Repeat (todo, cond)) else Skip)

    (* Statement parser *)
    ostap (
      atom : "read" "(" var:IDENT ")" {Read var}
        | "write" "(" x:!(Expr.expr) ")" {Write x}
        | ass:IDENT ":=" ex:!(Expr.expr) {Assign (ass, ex)}
        | "skip" {Skip}
        | "if" cond:!(Expr.expr)
          "then" th:parse
          elifs:("elif" elcond:!(Expr.expr) "then" elth:parse {(elcond, elth)})*
          el:(tl:(-"else" parse)? {match tl with None -> Skip | Some st -> st})
          "fi" {If (cond, th, List.fold_left (fun tl (elcond, elth) -> If (elcond, elth, tl)) el elifs)}
        | "while" cond:!(Expr.expr)
          "do" body:parse
          "od" {While (cond, body)}
        | "for" before:atom "," cond:!(Expr.expr) "," afterbody:atom "do" body:parse "od" {Seq(before, While(cond, Seq(body, afterbody)))}
        | "repeat" body:parse "until" cond:!(Expr.expr) {Repeat(body, cond)};
      parse: <s::ss> : !(Ostap.Util.listBy)[ostap (";")][atom] {List.fold_left (fun s ss -> Seq(s, ss)) s ss}
    )

  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o

(* Top-level parser *)
let parse = Stmt.parse
