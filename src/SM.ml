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
(* conditional jump                *) | CJMP  of string * string
(* begins procedure definition      *) | BEGIN of string list * string list
(* end procedure definition         *) | END
(* calls a procedure               *) | CALL  of string with show

(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let eval_instr (sk, (state, i, o)) instr = match instr with
                | CONST x  -> (x :: sk, (state, i, o))
                | BINOP op -> begin match sk with
                                | y :: x :: sk_tail ->
                                   let res = Expr.eval State.empty (Language.Expr.Binop op (Language.Expr.Const x) (Language.Expr.Const y))
                                   in (res :: sk_tail, (state, i, o))
                                | _                 -> failwith "not enough stack"
                              end
                | READ     -> begin match i with
                                | x :: i_tail -> (x :: sk, (state, i_tail, o))
                                | []          -> failwith "not enough input"
                              end
                | WRITE    -> begin match sk with
                                | x :: sk_tail -> (sk_tail, (state, i, o @ [x]))
                                | []           -> failwith "not enough stack"
                              end
                | LD var   -> ((State.eval state var) :: sk, (state, i, o))
                | ST var   -> begin match sk with
                                | x :: sk_tail -> (sk_tail, ((State.update var x state), i, o))
                                | []           -> failwith "not enough stack"
                              end
                | LABEL l  -> (sk, (state, i, o))


let rec eval env conf prog =
  let (cs, stack, st_conf) = conf in
  let (state, i, o) = st_conf
  in match prog with
    | []                 -> failwith "program should be ended with END instruction"
    | instr :: tail_prog ->
        match instr with
          | CALL name        -> eval env ((tail_prog, state) :: cs, stack, st_conf) (env#labeled name)
          | BEGIN (args, ls) ->
            let rec handle_begin state stack ls = function
              | []        -> eval env (cs, stack, (state, i, o)) tail_prog
              | a :: args ->
                let v :: stack_tail = stack
                in handle_begin (State.update a v state) stack_tail ls args
            in handle_begin (State.push_scope state (args @ ls)) stack ls args
          | END              -> begin match cs with
              | (ret, new_state) :: cs_tail -> eval env (cs_tail, stack, (State.drop_scope state new_state , i, o)) ret
              | []                          -> conf
            end
          | JMP l            -> eval env conf (env#labeled l)
          | CJMP (t, l)      ->
            let is_nz = match t with
              | "nz"  -> true
              | "z" -> false
              | _ -> failwith "incorrect CJMP type"
            in begin match stack with
                          | cond :: _ ->
                            if (cond != 0) == is_nz
                            then eval env conf (env#labeled l)
                            else eval env conf tail_prog
                          | []           -> failwith "not enough stack"
                        end
          | _               ->
            let (new_stack, new_st_conf) = eval_instr (stack, st_conf) instr
            in eval env (cs, new_stack, new_st_conf) tail_prog

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
  let (_, _, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.t -> prg

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

let compile (defs, st) =
  let rec compile_expr = function
    | Expr.Var   x          -> [LD x]
    | Expr.Const n          -> [CONST n]
    | Expr.Binop (op, x, y) -> compile_expr x @ compile_expr y @ [BINOP op]
  in
  let rec compile_st lab_gen = function
    | Stmt.Seq (s1, s2)   -> compile_st lab_gen s1 @ compile_st lab_gen s2
    | Stmt.Read x         -> [READ; ST x]
    | Stmt.Write e        -> compile_expr e @ [WRITE]
    | Stmt.Assign (x, e)  -> compile_expr e @ [ST x]
    | Stmt.Skip           -> []
    | Stmt.If (e, s1, s2) ->
      let else_lab = lab_gen#get in
      let end_lab = lab_gen#get
      in
        compile_expr e
        @ [CJMP ("z", else_lab)]
        @ compile_st lab_gen s1
        @ [JMP end_lab; LABEL else_lab]
        @ compile_st lab_gen s2
        @ [LABEL end_lab]
    | Stmt.While (e, s)   ->
      let do_lab = lab_gen#get in
      let end_lab = lab_gen#get
      in
        [LABEL do_lab]
        @ compile_expr e
        @ [CJMP ("z", end_lab)]
        @ compile_st lab_gen s
        @ [JMP do_lab; LABEL end_lab]
    | Stmt.Repeat (s, e)  ->
      let do_lab = lab_gen#get
      in
        [LABEL do_lab]
        @ compile_st lab_gen s
        @ compile_expr e
        @ [CJMP ("z", do_lab)]
    | Stmt.Call (nm, es)  ->
      (List.concat (List.map compile_expr (List.rev es)))
      @ [CALL nm]
  in
  let rec compile_defs lab_gen = function
    | []                            -> []
    | (name, (args, ls, s)) :: defs ->
      [LABEL name; BEGIN (args, ls)]
      @ (compile_st lab_gen s)
      @ [END]
      @ (compile_defs lab_gen defs)
  in
  let lab_gen = new label_gen in
  compile_st lab_gen st @ [END] @ compile_defs lab_gen defs
