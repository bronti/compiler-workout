open GT
open Language

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
*)
let eval_instr (sk, (mp, i, o)) instr = match instr with
                | CONST x  -> (x :: sk, (mp, i, o))
                | BINOP op -> begin match sk with
                                | y :: x :: sk_tail ->
                                   let res = Language.Expr.eval Language.Expr.empty (Language.Expr.Binop op (Language.Expr.Const x) (Language.Expr.Const y)) in
                                      (res :: sk_tail, (mp, i, o))
                                | _                 -> failwith "not enough stack"
                              end
                | READ     -> begin match i with
                                | x :: i_tail -> (x :: sk, (mp, i_tail, o))
                                | []          -> failwith "not enough input"
                              end
                | WRITE    -> begin match sk with
                                | x :: sk_tail -> (sk_tail, (mp, i, o @ [x]))
                                | []           -> failwith "not enough stack"
                              end
                | LD var   -> (mp var :: sk, (mp, i, o))
                | ST var   -> begin match sk with
                               | x :: sk_tail -> (sk_tail, (Language.Expr.update var x mp, i, o))
                               | []           -> failwith "not enough stack"
                              end

let rec eval conf prog = match prog with
  | []                 -> conf
  | instr :: tail_prog -> eval (eval_instr conf instr) tail_prog

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i = let (_, (_, _, o)) = eval ([], (Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compile =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  in
  function
  | Stmt.Seq (s1, s2)  -> compile s1 @ compile s2
  | Stmt.Read x        -> [READ; ST x]
  | Stmt.Write e       -> expr e @ [WRITE]
  | Stmt.Assign (x, e) -> expr e @ [ST x]
