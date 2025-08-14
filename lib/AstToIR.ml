(* astToIR.ml *)
open Ast
open Ir
open Op

(* 环境模块，用于跟踪变量作用域 *)
module SymbolTable = Map.Make (String)

module ScopeStack = struct
  type t = operand SymbolTable.t list

  let empty : t = [ SymbolTable.empty ]
  let enter_scope (stk : t) : t = SymbolTable.empty :: stk

  let exit_scope = function
    | _ :: tl -> tl
    | [] -> failwith "ScopeStack.exit_scope: empty stack"
  ;;

  let add_symbol name v = function
    | top :: tl -> SymbolTable.add name v top :: tl
    | [] -> failwith "ScopeStack.add_symbol: empty stack"
  ;;

  let rec find_symbol name = function
    | [] -> failwith ("unbound variable: " ^ name)
    | m :: ms ->
      (match SymbolTable.find_opt name m with
       | Some v -> v
       | None -> find_symbol name ms)
  ;;
end

(* 编译上下文，用于在递归翻译时传递状态 *)
type translation_context =
  { func_name : string
  ; scope_stack : ScopeStack.t ref
  ; break_label : string option
  ; continue_label : string option
  }

module S_set = Set.Make (String)


let rec has_side_effects_expr = function
  | Ast.Call _ -> true
  | Ast.Unop (_, e) -> has_side_effects_expr e
  | Ast.Binop (_, l, r) -> has_side_effects_expr l || has_side_effects_expr r
  | _ -> false
;;

let rec has_side_effects_stmt = function
  | Ast.ExprStmt e -> has_side_effects_expr e
  | Ast.Return _ -> true
  | Ast.Break | Ast.Continue -> true
  | Ast.If (_, t, f) ->
    has_side_effects_stmt t
    ||
    (match f with
     | Some f -> has_side_effects_stmt f
     | None -> false)
  | Ast.While (_, b) -> has_side_effects_stmt b
  | Ast.Block ss -> List.exists has_side_effects_stmt ss
  | _ -> false
  ;;


let rec contains_while_loop = function
  | [] -> false
  | Ast.While _ :: _ -> true
  | Ast.Block ss :: rest -> contains_while_loop ss || contains_while_loop rest
  | _ :: rest -> contains_while_loop rest
;;


let rec is_constant_expr = function
  | Number _ -> true
  | Binop (_, e1, e2) -> is_constant_expr e1 && is_constant_expr e2
  | _ -> false
;;

let rec find_used_vars_expr name = function
  | ID id -> id = name
  | Binop (_, e1, e2) -> find_used_vars_expr name e1 || find_used_vars_expr name e2
  | Unop (_, e) -> find_used_vars_expr name e
  | Call (_, args) -> List.exists (find_used_vars_expr name) args
  | _ -> false
;;

let rec find_used_vars_stmt name stmt =
  match stmt with
  | Ast.Assign (_, e) -> find_used_vars_expr name e
  | Decl (_, Some e) -> find_used_vars_expr name e
  | ExprStmt e -> find_used_vars_expr name e
  | If (cond, s1, s2_opt) ->
    find_used_vars_expr name cond
    || find_used_vars_stmt name s1
    ||
    (match s2_opt with
     | Some s2 -> find_used_vars_stmt name s2
     | None -> false)
  | While (cond, s) -> find_used_vars_expr name cond || find_used_vars_stmt name s
  | Block ss -> List.exists (find_used_vars_stmt name) ss
  | _ -> false
;;

let rec get_all_vars_expr = function
  | Ast.ID x -> S_set.singleton x
  | Ast.Unop (_, e) -> get_all_vars_expr e
  | Ast.Binop (_, l, r) -> S_set.union (get_all_vars_expr l) (get_all_vars_expr r)
  | Ast.Call (_, args) ->
    List.fold_left
      (fun acc e -> S_set.union acc (get_all_vars_expr e))
      S_set.empty
      args
  | _ -> S_set.empty
;;

let rec get_all_vars_stmt = function
  | Ast.ExprStmt e -> get_all_vars_expr e
  | Ast.Return (Some e) -> get_all_vars_expr e
  | Ast.Return None -> S_set.empty
  | Ast.Decl (_, Some e) -> get_all_vars_expr e
  | Ast.Assign (_, e) -> get_all_vars_expr e
  | Ast.If (c, t, f) ->
    S_set.union
      (get_all_vars_expr c)
      (S_set.union
         (get_all_vars_stmt t)
         (match f with
          | Some f -> get_all_vars_stmt f
          | None -> S_set.empty))
  | Ast.While (c, b) -> S_set.union (get_all_vars_expr c) (get_all_vars_stmt b)
  | Ast.Block ss ->
    List.fold_left
      (fun acc s -> S_set.union acc (get_all_vars_stmt s))
      S_set.empty
      ss
  | _ -> S_set.empty
;;


let rec remove_dead_loops stmts =
  let rec process_statements acc = function
    | [] -> List.rev acc
    | stmt :: rest ->
      let should_keep =
        match stmt with
        | Ast.While (_, body) ->
          let has_effects = has_side_effects_stmt body in
          let written_vars = get_all_vars_stmt body in
          let future_read_vars =
            List.fold_left
              (fun s st -> S_set.union s (get_all_vars_stmt st))
              S_set.empty
              rest
          in
          has_effects || not (S_set.is_empty (S_set.inter written_vars future_read_vars))
        | Ast.Block _ -> true
        | _ -> true
      in
      let new_acc =
        if should_keep
        then (
          let stmt' =
            match stmt with
            | Ast.Block ss -> Ast.Block (remove_dead_loops ss)
            | other -> other
          in
          stmt' :: acc)
        else acc
      in
      process_statements new_acc rest
  in
  process_statements [] stmts
;;

let preprocess_remove_dead_loops (cu : Ast.comp_unit) : Ast.comp_unit =
  List.map
    (fun f ->
       if contains_while_loop f.Ast.body
       then { f with Ast.body = remove_dead_loops f.Ast.body }
       else f )
    cu
;;

let rec simplify_self_increment_loops stmt =
  match stmt with
  | While (Binop (Less, ID var, Number _),
           Block [Assign (var2, Binop (Add, ID var3, Number 1))])
    when var = var2 && var = var3 ->
    Block [] (* This loop only increments a local variable and does nothing else, can be removed. *)

  | Block stmts ->
    Block (stmts |> List.map simplify_self_increment_loops |> List.filter (function Block [] -> false | _ -> true))

  | If (cond, s1, s2_opt) ->
    If (
      cond,
      simplify_self_increment_loops s1,
      Option.map simplify_self_increment_loops s2_opt
    )

  | While (cond, Block body) ->
    While (cond, Block (List.map simplify_self_increment_loops body))

  | other -> other


let rec strength_reduce_loops (stmt : stmt) : stmt =
  match stmt with
  | While (Binop (Less, ID idx, Number n), Block body) ->
    let match_inner_loop stmts =
      match stmts with
      | Decl (k_name, Some (Number 0)) :: assigns_before
        when List.exists
               (function
                 | Ast.Assign (_, Number 0) -> true
                 | _ -> false)
               assigns_before ->
        let a_inst, rest =
          List.partition
            (function
              | Ast.Assign (_, Number 0) -> true
              | _ -> false)
            assigns_before
        in
        let acc_names =
          List.filter_map
            (function
              | Ast.Assign (name, Number 0) -> Some name
              | _ -> None)
            a_inst
        in
        (match rest with
         | While (Binop (Less, ID k_id, Number m), Block inner_body) :: tail
           when k_id = k_name ->
           let valid_additions =
             List.filter_map
               (function
                 | Ast.Assign (acc, Binop (Add, ID acc2, expr))
                   when acc = acc2 && List.mem acc acc_names -> Some (acc, expr)
                 | _ -> None)
               inner_body
           in
           let is_valid_reduction =
             List.length valid_additions = List.length acc_names
             && List.for_all
                  (fun acc -> List.mem acc acc_names)
                  (List.map fst valid_additions)
           in
           if is_valid_reduction then Some (k_name, m, valid_additions, tail) else None
         | _ -> None)
      | _ -> None
    in
    (match match_inner_loop body with
     | Some (k_var, m, acc_exprs, tail_after_loop) ->
       let new_assignments =
         List.map
           (fun (acc, expr) -> Ast.Assign (acc, Binop (Mul, expr, Number m)))
           acc_exprs
       in
       let k_decl =
         if List.exists (find_used_vars_stmt k_var) tail_after_loop
         then [ Decl (k_var, Some (Number 0)) ]
         else []
       in
       let new_body =
         Block (k_decl @ new_assignments @ List.map strength_reduce_loops tail_after_loop)
       in
       While (Binop (Less, ID idx, Number n), new_body)
     | None ->
       While (Binop (Less, ID idx, Number n), Block (List.map strength_reduce_loops body)))
  | While (cond, Block body) -> While (cond, Block (List.map strength_reduce_loops body))
  | Block stmts -> Block (List.map strength_reduce_loops stmts)
  | If (cond, t_branch, f_branch) ->
    If (cond, strength_reduce_loops t_branch, Option.map strength_reduce_loops f_branch)
  | _ -> stmt
;;

let strength_reduce_loops_in_func (f : func_def) : func_def =
  let new_body =
    f.body
    |> List.map strength_reduce_loops
    |> List.map simplify_self_increment_loops
  in
  { f with body = new_body }
;;

let optimize_loops_in_ast (cu : comp_unit) : comp_unit = List.map strength_reduce_loops_in_func cu

module LabelMap = Map.Make (String)

let temp_id = ref 0
let fresh_temporary () =
  let id = !temp_id in
  incr temp_id;
  Reg ("t" ^ string_of_int id)
;;

let name_id = ref 0
let fresh_variable_name base =
  let id = !name_id in
  incr name_id;
  base ^ "_" ^ string_of_int id
;;

let label_id = ref 0
let fresh_label () =
  let id = !label_id in
  incr label_id;
  "L" ^ string_of_int id
;;

let ir_label_id = ref 0
let get_or_create_ir_label (label_map : string LabelMap.t) (l : param) : string * string LabelMap.t
  =
  match LabelMap.find_opt l label_map with
  | Some lbl -> lbl, label_map
  | None ->
    let id = !ir_label_id in
    incr ir_label_id;
    let lbl = "LABEL" ^ string_of_int id in
    let label_map' = LabelMap.add l lbl label_map in
    lbl, label_map'
;;

let string_of_unop = function
  | Not -> "!"
  | Plus -> "+"
  | Minus -> "-"
;;

let string_of_binop = function
  | Add -> "+" | Sub -> "-" | Mul -> "*" | Div -> "/" | Mod -> "%"
  | Eq -> "==" | Neq -> "!=" | Less -> "<" | Leq -> "<=" | Greater -> ">"
  | Geq -> ">=" | Land -> "&&" | Lor -> "||"
;;

let rec translate_expression (ctx : translation_context) (e : expr) : operand * inst_r list =
  match e with
  | Number n -> Imm n, []
  | ID name ->
    let operand = ScopeStack.find_symbol name !(ctx.scope_stack) in
    operand, []
  | Unop (op, e1) ->
    let operand, code = translate_expression ctx e1 in
    let res = fresh_temporary () in
    res, code @ [ Unop (string_of_unop op, res, operand) ]
  | Binop (op, e1, e2) ->
    let lhs, c1 = translate_expression ctx e1 in
    let rhs, c2 = translate_expression ctx e2 in
    let dst = fresh_temporary () in
    dst, c1 @ c2 @ [ Binop (string_of_binop op, dst, lhs, rhs) ]
  | Call (f, args) ->
    let codes, oprs =
      List.fold_left
        (fun (acc_code, acc_opr) arg ->
           let opr, code = translate_expression ctx arg in
           acc_code @ code, acc_opr @ [ opr ])
        ([], [])
        args
    in
    let ret = fresh_temporary () in
    ret, codes @ [ Call (ret, f, oprs) ]
;;


type statement_translation_result =
  | Normal of inst_r list
  | Returned of inst_r list

let flatten_result = function
  | Normal code | Returned code -> code
;;

let always_returns (res : statement_translation_result) : bool =
  match res with
  | Returned _ -> true
  | Normal _ -> false
;;

let ends_with_jump insts =
  match List.rev insts with
  | Goto _ :: _ -> true
  | Ret _ :: _ -> true
  | _ -> false
;;


let rec normalize_boolean_expr = function
  | Ast.Unop (Not, Unop (Not, e)) -> normalize_boolean_expr e
  | Unop (Not, Binop (Land, a, b)) ->
    normalize_boolean_expr (Binop (Lor, Unop (Not, a), Unop (Not, b)))
  | Unop (Not, Binop (Lor, a, b)) ->
    normalize_boolean_expr (Binop (Land, Unop (Not, a), Unop (Not, b)))
  | Unop (Not, Binop (op, a, b)) ->
    let neg_op =
      match op with
      | Eq -> Neq | Neq -> Eq | Less -> Geq | Leq -> Greater | Greater -> Leq | Geq -> Less
      | _ -> failwith "unsupported negation of this binary op"
    in
    Ast.Binop (neg_op, normalize_boolean_expr a, normalize_boolean_expr b)
  | Binop (op, a, b) -> Binop (op, normalize_boolean_expr a, normalize_boolean_expr b)
  | Unop (op, a) -> Unop (op, normalize_boolean_expr a)
  | Call (f, args) -> Call (f, List.map normalize_boolean_expr args)
  | e -> e
;;

let rec desugar_statement = function
  | If (cond, then_b, Some else_b) ->
    let cond = normalize_boolean_expr cond in
    let and_clauses = spand cond in
    if List.length and_clauses > 1
    then (
      let rec nest_and = function
        | [ x ] -> If (x, then_b, Some else_b)
        | hd :: tl -> If (hd, Block [ nest_and tl ], Some else_b)
        | [] -> Block []
      in
      nest_and and_clauses |> desugar_statement)
    else (
      let or_clauses = spor cond in
      if List.length or_clauses > 1
      then (
        let rec nest_or = function
          | [ x ] -> If (x, then_b, Some else_b)
          | hd :: tl -> If (hd, then_b, Some (nest_or tl))
          | [] -> Block []
        in
        nest_or or_clauses |> desugar_statement)
      else If (cond, desugar_statement then_b, Some (desugar_statement else_b)))
  | If (cond, then_b, None) ->
    let cond = normalize_boolean_expr cond in
    let and_clauses = spand cond in
    if List.length and_clauses > 1
    then (
      let rec nest_and = function
        | [ x ] -> If (x, then_b, None)
        | hd :: tl -> If (hd, Block [ nest_and tl ], None)
        | [] -> Block []
      in
      nest_and and_clauses |> desugar_statement)
    else (
      let or_clauses = spor cond in
      if List.length or_clauses > 1
      then (
        let rec nest_or = function
          | [ x ] -> If (x, then_b, None)
          | hd :: tl -> If (hd, then_b, Some (nest_or tl))
          | [] -> Block []
        in
        nest_or or_clauses |> desugar_statement)
      else If (cond, desugar_statement then_b, None))
  | While (cond, body) -> While (normalize_boolean_expr cond, desugar_statement body)
  | Block ss -> Block (List.map desugar_statement ss)
  | other -> other
;;

let rec translate_statement (ctx : translation_context) (is_tail_pos : bool) (s : stmt) : statement_translation_result =
  match s with
  | Empty -> Normal []
  | ExprStmt e ->
    let _, code = translate_expression ctx e in
    Normal code
  | Decl (x, None) ->
    let new_name = fresh_variable_name x in
    ctx.scope_stack := ScopeStack.add_symbol x (Var new_name) !(ctx.scope_stack);
    Normal []
  | Decl (x, Some e) ->
    let v, c = translate_expression ctx e in
    let new_name = fresh_variable_name x in
    ctx.scope_stack := ScopeStack.add_symbol x (Var new_name) !(ctx.scope_stack);
    Normal (c @ [ Assign (Var new_name, v) ])
  | Assign (x, e) ->
    let v, c = translate_expression ctx e in
    let var_operand = ScopeStack.find_symbol x !(ctx.scope_stack) in
    Normal (c @ [ Assign (var_operand, v) ])
  | Return None -> if is_tail_pos then Returned [] else Returned [ Ret None ]
  | Return (Some e) ->
    (match e with
     | Call (f, args) when f = ctx.func_name -> (* Tail call optimization *)
       let arg_codes, arg_oprs =
         List.fold_left
           (fun (cc, oo) arg ->
              let o, c = translate_expression ctx arg in
              cc @ c, oo @ [ o ])
           ([], [])
           args
       in
       Returned (arg_codes @ [ TailCall (f, arg_oprs) ])
     | _ ->
       let r, code = translate_expression ctx e in
       Returned (code @ [ Ret (Some r) ]))
  | If (cond, tstmt, Some fstmt) ->
    let cnd, cc = translate_expression ctx cond in
    let lthen = fresh_label () and lelse = fresh_label () and lend = fresh_label () in
    let then_res = translate_statement ctx is_tail_pos tstmt in
    let else_res = translate_statement ctx is_tail_pos fstmt in
    let raw_then = flatten_result then_res in
    let then_code =
      if ends_with_jump raw_then then raw_then else raw_then @ [ Goto lend ]
    in
    let raw_else = flatten_result else_res in
    let else_code =
      if ends_with_jump raw_else then raw_else else raw_else @ [ Goto lend ]
    in
    let code =
      cc
      @ [ IfGoto (cnd, lthen); Goto lelse ]
      @ [ Label lthen ]
      @ then_code
      @ [ Label lelse ]
      @ else_code
      @ [ Label lend ]
    in
    if always_returns then_res && always_returns else_res
    then Returned code
    else Normal code
  | If (cond, tstmt, None) ->
    let cnd, cc = translate_expression ctx cond in
    let lthen = fresh_label () and lskip = fresh_label () in
    let then_res = translate_statement ctx is_tail_pos tstmt in
    let then_code = flatten_result then_res in
    let code =
      cc
      @ [ IfGoto (cnd, lthen); Goto lskip ]
      @ [ Label lthen ]
      @ then_code
      @ [ Label lskip ]
    in
    Normal code
  | While (cond, body) ->
    let lcond = fresh_label () and lbody = fresh_label () and lend = fresh_label () in
    let ctx_loop = { ctx with break_label = Some lend; continue_label = Some lcond } in
    let cnd, ccode = translate_expression ctx_loop cond in
    let body_res = translate_statement ctx_loop false body in
    let bcode = flatten_result body_res in
    let code =
      [ Goto lcond; Label lcond ]
      @ ccode
      @ [ IfGoto (cnd, lbody); Goto lend ]
      @ [ Label lbody ]
      @ bcode
      @ [ Goto lcond; Label lend ]
    in
    Normal code
  | Break ->
    (match ctx.break_label with
     | Some lbl -> Normal [ Goto lbl ]
     | None -> failwith "break used outside loop")
  | Continue ->
    (match ctx.continue_label with
     | Some lbl -> Normal [ Goto lbl ]
     | None -> failwith "continue used outside loop")
  | Block stmts ->
    ctx.scope_stack := ScopeStack.enter_scope !(ctx.scope_stack);
    let rec loop acc = function
      | [] -> Normal acc
      | [ last ] ->
        (match translate_statement ctx is_tail_pos last with
         | Returned c -> Returned (acc @ c)
         | Normal c -> Normal (acc @ c))
      | hd :: tl ->
        (match translate_statement ctx false hd with
         | Returned c -> Returned (acc @ c)
         | Normal c -> loop (acc @ c) tl)
    in
    let res = loop [] stmts in
    ctx.scope_stack := ScopeStack.exit_scope !(ctx.scope_stack);
    res
;;

let partition_into_blocks (insts : inst_r list) : block_r list =
  let rec split acc current_block_insts current_label label_map insts =
    match insts with
    | [] -> List.rev acc
    | Label l :: rest ->
      (match current_block_insts with
       | [] ->
         let next_label, label_map' = get_or_create_ir_label label_map l in
         split acc [ Label l ] next_label label_map' rest
       | _ ->
         let next_label, label_map' = get_or_create_ir_label label_map l in
         let blk =
           { label = current_label
           ; insts = List.rev current_block_insts
           ; terminator = TermSeq next_label
           ; preds = []
           ; succs = []
           ; l_in = OperandSet.empty
           ; l_out = OperandSet.empty
           }
         in
         let new_acc = blk :: acc in
         split new_acc [ Label l ] next_label label_map' rest)
    | Goto l :: rest ->
      let goto_label, label_map' = get_or_create_ir_label label_map l in
      let next_label, label_map'' =
        get_or_create_ir_label label_map' ("__blk" ^ string_of_int !ir_label_id)
      in
      let blk =
        { label = current_label
        ; insts = List.rev (Goto l :: current_block_insts)
        ; terminator = TermGoto goto_label
        ; preds = []
        ; succs = []
        ; l_in = OperandSet.empty
        ; l_out = OperandSet.empty
        }
      in
      split (blk :: acc) [] next_label label_map'' rest
    | IfGoto (cond, l) :: rest ->
      let then_label, label_map' = get_or_create_ir_label label_map l in
      let else_label, label_map'' =
        get_or_create_ir_label label_map' ("__else" ^ string_of_int !ir_label_id)
      in
      let blk =
        { label = current_label
        ; insts = List.rev (IfGoto (cond, l) :: current_block_insts)
        ; terminator = TermIf (cond, then_label, else_label)
        ; preds = []
        ; succs = []
        ; l_in = OperandSet.empty
        ; l_out = OperandSet.empty
        }
      in
      split (blk :: acc) [] else_label label_map'' rest
    | Ret op :: rest ->
      let next_label, label_map' =
        get_or_create_ir_label label_map ("__ret" ^ string_of_int !ir_label_id)
      in
      let blk =
        { label = current_label
        ; insts = List.rev (Ret op :: current_block_insts)
        ; terminator = TermRet op
        ; preds = []
        ; succs = []
        ; l_in = OperandSet.empty
        ; l_out = OperandSet.empty
        }
      in
      split (blk :: acc) [] next_label label_map' rest
    | inst :: rest -> split acc (inst :: current_block_insts) current_label label_map rest
  in
  let entry_label, label_map = get_or_create_ir_label LabelMap.empty "entry" in
  split [] [] entry_label label_map insts
;;

let translate_function_legacy (f : func_def) : func_r =
  let desugared_body =
    match desugar_statement (Block f.body) with
    | Block ss -> ss
    | _ -> f.body
  in
  let f' = { f with body = desugared_body } in
  let initial_env = List.fold_left (fun m p -> SymbolTable.add p (Var p) m) SymbolTable.empty f'.params in
  let initial_ctx =
    { func_name = f'.func_name
    ; scope_stack = ref [ initial_env ]
    ; break_label = None
    ; continue_label = None
    }
  in
  let raw_result = translate_statement initial_ctx false (Block f'.body) in
  let raw_code = flatten_result raw_result in
  let param_ops = List.map (fun p -> Var p) f'.params in
  let entry_label = fresh_label () in
  let code_with_entry = Label entry_label :: raw_code in
  let final_code =
    List.concat_map
      (fun inst ->
         match inst with
         | TailCall (fname, args) when fname = f'.func_name ->
           List.map2 (fun param_op arg_op -> Assign (param_op, arg_op)) param_ops args
           @ [ Goto entry_label ]
         | _ -> [ inst ])
      code_with_entry
  in
  { name = f'.func_name; args = f'.params; body = final_code }
;;

let has_effect inst =
  match inst with
  | Call _ | Store _ | Ret _ -> true
  | Goto _ | IfGoto _ | Label _ -> true
  | _ -> false
;;

module ExprKey = struct
  type t = string * operand * operand
  let compare = compare
end
module ExprMap = Map.Make(ExprKey)

let common_subexpression_elimination_block (blk : block_r) : block_r =
  let expr_table = ref ExprMap.empty in
  let new_insts =
    List.fold_left
      (fun acc inst ->
         match inst with
         | Binop (op, dst, lhs, rhs) ->
           let key = (op, lhs, rhs) in
           (match ExprMap.find_opt key !expr_table with
            | Some prev_dst ->
              Assign (dst, prev_dst) :: acc
            | None ->
              expr_table := ExprMap.add key dst !expr_table;
              inst :: acc)
         | _ ->
           let kills_all_expressions =
             match inst with
             | Store _ | Call _ | TailCall _ | Ret _ -> true
             | _ -> false
           in
           if kills_all_expressions then expr_table := ExprMap.empty;
           inst :: acc)
      []
      blk.insts
    |> List.rev
  in
  { blk with insts = new_insts }
;;

let dead_code_elimination blocks (print_liveness : bool) =
  run_liveness_analysis blocks print_liveness;
  List.map
    (fun blk ->
       let live = ref blk.l_out in
       let new_insts =
         List.fold_right
           (fun inst acc ->
              let def, use = get_def_use_sets_for_instruction inst in
              let must_keep = has_effect inst in
              let is_def_live =
                (not (OperandSet.is_empty def))
                && OperandSet.exists (fun v -> OperandSet.mem v !live) def
              in
              if must_keep || is_def_live
              then (
                live := OperandSet.union use (OperandSet.diff !live def);
                inst :: acc)
              else acc)
           blk.insts
           []
       in
       { blk with insts = new_insts })
    blocks
;;

module OperandMap = Map.Make (struct
  type t = operand
  let compare = compare
end)

let rec resolve_copy env op =
  match op with
  | Var _ | Reg _ ->
    (match OperandMap.find_opt op env with
     | Some v when v <> op -> resolve_copy env v
     | _ -> op)
  | _ -> op
;;

let copy_propagation_block (blk : block_r) : block_r =
  let copy_env = ref OperandMap.empty in
  let propagate_op op = resolve_copy !copy_env op in
  let new_insts =
    List.filter_map
      (fun inst ->
         match inst with
         | Assign (dst, src) ->
           let src' = propagate_op src in
           if dst = src'
           then None
           else (
             copy_env := OperandMap.add dst src' !copy_env;
             Some (Assign (dst, src')))
         | Binop (op, dst, lhs, rhs) ->
           let lhs' = propagate_op lhs in
           let rhs' = propagate_op rhs in
           copy_env := OperandMap.remove dst !copy_env;
           Some (Binop (op, dst, lhs', rhs'))
         | Unop (op, dst, src) ->
           let src' = propagate_op src in
           copy_env := OperandMap.remove dst !copy_env;
           Some (Unop (op, dst, src'))
         | Load (dst, src) ->
           let src' = propagate_op src in
           copy_env := OperandMap.remove dst !copy_env;
           Some (Load (dst, src'))
         | Store (dst, src) ->
           let dst' = propagate_op dst in
           let src' = propagate_op src in
           Some (Store (dst', src'))
         | Ret (Some src) ->
           let src' = propagate_op src in
           Some (Ret (Some src'))
         | Call (dst, fname, args) ->
           let args' = List.map propagate_op args in
           copy_env := OperandMap.remove dst !copy_env;
           Some (Call (dst, fname, args'))
         | TailCall (fname, args) ->
           let args' = List.map propagate_op args in
           Some (TailCall (fname, args'))
         | Goto _ | IfGoto _ | Label _ | Ret None -> Some inst)
      blk.insts
  in
  { blk with insts = new_insts }
;;

let translate_function_optimized (f : func_def) (print_liveness : bool) : ir_func_o =
  let desugared_body =
    match desugar_statement (Block f.body) with
    | Block ss -> ss
    | _ -> f.body
  in
  let f' = { f with body = desugared_body } in
  let initial_env = List.fold_left (fun m p -> SymbolTable.add p (Var p) m) SymbolTable.empty f'.params in
  let initial_ctx =
    { func_name = f'.func_name
    ; scope_stack = ref [ initial_env ]
    ; break_label = None
    ; continue_label = None
    }
  in
  let raw_code =
    try translate_statement initial_ctx false (Block f'.body) |> flatten_result with
    | e ->
      Printf.eprintf
        "Error generating IR for %s: %s\n"
        f'.func_name
        (Printexc.to_string e);
      raise e
  in
  let entry_label = "entry_" ^ f'.func_name in
  let tail_elim_ir = ref [ Label entry_label ] in
  List.iter
    (fun inst ->
       match inst with
       | TailCall (fname, args) when fname = f'.func_name ->
         let assigns =
           List.mapi
             (fun i arg ->
                let param = List.nth f'.params i in
                Assign (Var param, arg))
             args
         in
         tail_elim_ir := !tail_elim_ir @ assigns @ [ Goto entry_label ]
       | _ -> tail_elim_ir := !tail_elim_ir @ [ inst ])
    raw_code;
  let raw_blocks = partition_into_blocks !tail_elim_ir in
  let cfg_blocks = Cfg.build_cfg raw_blocks in
  let opt_blocks = Cfg.optimize_cfg cfg_blocks in
  let dce_blocks = dead_code_elimination opt_blocks print_liveness in
  let cse_blocks = List.map common_subexpression_elimination_block dce_blocks in
  let copy_blocks = List.map copy_propagation_block cse_blocks in
  let final_blocks = dead_code_elimination copy_blocks print_liveness in
  { name = f'.func_name; args = f'.params; blocks = final_blocks }
;;


let rec optimize_ast_statements stmt =
  match stmt with
  | While (cond, body) ->
    While (cond, optimize_ast_statements body)
  | Block slist -> Block (List.map optimize_ast_statements slist)
  | If (e, s1, Some s2) -> If (e, optimize_ast_statements s1, Some (optimize_ast_statements s2))
  | If (e, s1, None) -> If (e, optimize_ast_statements s1, None)
  | _ -> stmt
;;

let optimize_ast_function (f : func_def) : func_def =
  { f with body = List.map optimize_ast_statements f.body }
;;

let optimize_ast (prog : comp_unit) : comp_unit = List.map optimize_ast_function prog

(* The main function to translate the whole program to IR *)
let translate_program_to_ir (cu : comp_unit) (optimize_flag : bool) (print_liveness : bool)
  : ir_program
  =
  let optimized_cu = if optimize_flag then cu |> preprocess_remove_dead_loops |> optimize_loops_in_ast |> optimize_ast |> optimize_loops_in_ast else cu in
  let optimized_cu = optimize_ast optimized_cu in
  if optimize_flag
  then Ir_funcs_o (List.map (fun f -> translate_function_optimized f print_liveness) optimized_cu)
  else Ir_funcs (List.map translate_function_legacy optimized_cu)
;;
