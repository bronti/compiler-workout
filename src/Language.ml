(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators

(* States *)
module State =
  struct

    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (* Empty state *)
    let empty =
      let e x = failwith (Printf.sprintf "Undefined variable: %s" x) in
      {g = e; l = e; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let u x v s = fun y -> if x = y then v else s y in
      if List.mem x s.scope then {s with l = u x v s.l} else {s with g = u x v s.g}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let push_scope st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let drop_scope st st' = {st' with g = st.g}

  end

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

    (* Expression evaluator

          val eval : state -> t -> int

       Takes a state and an expression, and returns the value of the expression in
       the given state.
    *)
    let to_func op =
      let bti   = function true -> 1 | _ -> 0 in
      let itb b = b <> 0 in
      let (|>) f g   = fun x y -> f (g x y) in
      match op with
      | "+"  -> (+)
      | "-"  -> (-)
      | "*"  -> ( * )
      | "/"  -> (/)
      | "%"  -> (mod)
      | "<"  -> bti |> (< )
      | "<=" -> bti |> (<=)
      | ">"  -> bti |> (> )
      | ">=" -> bti |> (>=)
      | "==" -> bti |> (= )
      | "!=" -> bti |> (<>)
      | "&&" -> fun x y -> bti (itb x && itb y)
      | "!!" -> fun x y -> bti (itb x || itb y)
      | _    -> failwith (Printf.sprintf "Unknown binary operator %s" op)

    let rec eval st expr =
      match expr with
      | Const n -> n
      | Var   x -> State.eval st x
      | Binop (op, x, y) -> to_func op (eval st x) (eval st y)

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string

    *)
    ostap (
      parse:
  	  !(Ostap.Util.expr
               (fun x -> x)
  	     (Array.map (fun (a, s) -> a,
                             List.map  (fun s -> ostap(- $(s)), (fun x y -> Binop (s, x, y))) s
                          )
                [|
  		`Lefta, ["!!"];
  		`Lefta, ["&&"];
  		`Nona , ["=="; "!="; "<="; "<"; ">="; ">"];
  		`Lefta, ["+" ; "-"];
  		`Lefta, ["*" ; "/"; "%"];
                |]
  	     )
  	     primary);

      primary:
        n:DECIMAL {Const n}
      | x:IDENT   {Var x}
      | -"(" parse -")"
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
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* call a procedure                 *) | Call   of string * Expr.t list with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters and a body for given definition
    *)
    let rec eval env (mp, i, o) st = match st with
       | Read var            -> begin match i with
                                  | x :: tl -> (State.update var x mp, tl, o)
                                  | []      -> failwith "not enough input"
                                end
       | Write ex            -> (mp, i, o @ [Expr.eval mp ex])
       | Assign (var, ex)    -> (State.update var (Expr.eval mp ex) mp, i, o)
       | Seq (st1, st2)      -> let new_conf = eval env (mp, i, o) st1
                                in eval env new_conf st2
       | Skip                -> (mp, i, o)
       | If (cond, th, el)   -> let cond_val = Expr.eval mp cond
                                in eval env (mp, i, o) (if cond_val != 0 then th else el)
       | While (cond, todo)  -> let cond_val = Expr.eval mp cond
                                in
                                  if cond_val != 0
                                  then
                                    let new_conf = eval env (mp, i, o) todo
                                    in eval env new_conf (While (cond, todo))
                                  else (mp, i, o)
       | Repeat (todo, cond) -> let new_conf = eval env (mp, i, o) todo in
                                let (new_mp, _, _) = new_conf
                                in eval env new_conf (if (Expr.eval new_mp cond) == 0 then (Repeat (todo, cond)) else Skip)
       | Call (name, es)   -> let xs, ls, body = env#definition name in
                                let args = List.combine xs (List.map (Expr.eval mp) es) in
                                let loc_mp = State.push_scope mp (xs @ ls) in
                                let begin_mp = List.fold_left (fun mp (n, v) -> State.update n v mp) loc_mp args in
                                let end_mp, new_i, new_o = eval env (begin_mp, i, o) body
                                in (State.drop_scope end_mp mp, new_i, new_o)


    (* Statement parser *)
    ostap (
      atom : %"read" "(" var:IDENT ")" {Read var}
        | %"write" "(" x:!(Expr.parse) ")" {Write x}
        | %"skip" {Skip}
        | %"if" cond:!(Expr.parse)
          %"then" th:parse
          elifs:(%"elif" elcond:!(Expr.parse) %"then" elth:parse {(elcond, elth)})*
          el:(tl:(-(%"else") parse)? {match tl with None -> Skip | Some st -> st})
          %"fi" {
            If (cond, th, List.fold_left (fun tl (elcond, elth) -> If (elcond, elth, tl)) el elifs)
          }
        | %"while" cond:!(Expr.parse)
          %"do" body:parse
          %"od" {While (cond, body)}
        | %"for" before:atom "," cond:!(Expr.parse) "," afterbody:atom %"do" body:parse %"od" {
            Seq(before, While(cond, Seq(body, afterbody)))
          }
        | %"repeat" body:parse %"until" cond:!(Expr.parse) {Repeat(body, cond)}
        | x:IDENT b:(
              ":=" ex:!(Expr.parse) {Assign (x, ex)}
            | "("  args:!(Ostap.Util.list0 Expr.parse) ")" {Call (x, args)}
          ) {b};
      parse: <s::ss> : !(Ostap.Util.listBy)[ostap (";")][atom] {List.fold_left (fun s ss -> Seq(s, ss)) s ss}
    )

  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      arg: IDENT;
      parse: %"fun" name:IDENT "(" args:!(Ostap.Util.list0 arg) ")"
          locs:(%"local" !(Ostap.Util.list arg))?
          "{" body:!(Stmt.parse) "}" {
            (name, (args, (match locs with None -> [] | Some l -> l), body))
          }
    )

  end

(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m        = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in
  let _, _, o  = Stmt.eval (object method definition f = snd @@ M.find f m end) (State.empty, i, []) body in o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
