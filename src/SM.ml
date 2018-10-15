open GT
open Language

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string
(* conditional jump                *) | CJMP  of string * string with show

(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let eval_instr (sk, (mp, i, o)) instr = match instr with
                | CONST x  -> (x :: sk, (mp, i, o))
                | BINOP op -> begin match sk with
                                | y :: x :: sk_tail ->
                                   let res = Language.Expr.eval Language.Expr.empty (Language.Expr.Binop op (Language.Expr.Const x) (Language.Expr.Const y))
                                   in (res :: sk_tail, (mp, i, o))
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
                | LABEL l  -> (sk, (mp, i, o))

let rec eval env conf prog = match prog with
  | []                 -> conf
  | instr :: tail_prog ->
      match instr with
        | JMP l -> eval env conf (env#labeled l)
        | CJMP (t, l) ->
          let (sk, (mp, i, o)) = conf in
          let is_nz = match t with
            | "nz"  -> true
            | "z" -> false
            | _ -> failwith "incorrect CJMP type"
          in begin match sk with
                        | cond :: sk_tail ->
                          if (cond != 0) == is_nz
                          then eval env conf (env#labeled l)
                          else eval env conf tail_prog
                        | []           -> failwith "not enough stack"
                      end
        | _ -> eval env (eval_instr conf instr) tail_prog

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], (Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)

class label_gen =
  object (self)
    val mutable count = -1

    method get =
      count <- count + 1;
      Printf.sprintf "lab%d" count
  end

let rec compile st =
  let rec expr = function
    | Expr.Var   x          -> [LD x]
    | Expr.Const n          -> [CONST n]
    | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  in
  let rec do_compile lab_gen = function
    | Stmt.Seq (s1, s2)   -> do_compile lab_gen s1 @ do_compile lab_gen s2
    | Stmt.Read x         -> [READ; ST x]
    | Stmt.Write e        -> expr e @ [WRITE]
    | Stmt.Assign (x, e)  -> expr e @ [ST x]
    | Stmt.Skip           -> []
    | Stmt.If (e, s1, s2) ->
      let else_lab = lab_gen#get in
      let end_lab = lab_gen#get
      in
        expr e
        @ [CJMP ("z", else_lab)]
        @ do_compile lab_gen s1
        @ [JMP end_lab; LABEL else_lab]
        @ do_compile lab_gen s2
        @ [LABEL end_lab]
    | Stmt.While (e, s) ->
      let do_lab = lab_gen#get in
      let end_lab = lab_gen#get
      in
        [LABEL do_lab]
        @ expr e
        @ [CJMP ("z", end_lab)]
        @ do_compile lab_gen s
        @ [JMP do_lab; LABEL end_lab]
    | Stmt.Repeat (s, e) ->
      let do_lab = lab_gen#get
      in
        [LABEL do_lab]
        @ do_compile lab_gen s
        @ expr e
        @ [CJMP ("z", do_lab)]
  in do_compile (new label_gen) st
