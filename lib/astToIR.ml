(* astToIR.ml *)
open Ast
open Ir
open Op

module Enwli = Map.Make (String)


module Estack = struct
  type t = operand Enwli.t list

  let empty : t = [ Enwli.empty ]
  let enter (stk : t) : t = Enwli.empty :: stk

  let exit = function
    | _ :: tl -> tl
    | [] -> failwith "Estack.exit: empty stack"
  ;;

  let add name v = function
    | top :: tl -> Enwli.add name v top :: tl
    | [] -> failwith "Estack.add: empty stack"
  ;;

  let rec l_up name = function
    | [] -> failwith ("unbound variable: " ^ name)
    | m :: ms ->
      (match Enwli.find_opt name m with
       | Some v -> v
       | None -> l_up name ms)
  ;;
end

type text =
  { func_name : string
  ; e_stack : Estack.t ref
  ; breakb : string option
  ; continueb : string option
  }

module S_set = Set.Make (String)


let rec side_effecte = function
  | Ast.Call _ -> true
  | Ast.Unop (_, e) -> side_effecte e
  | Ast.Binop (_, l, r) -> side_effecte l || side_effecte r
  | _ -> false
;;

let rec side_effects = function
  | Ast.ExprStmt e -> side_effecte e
  | Ast.Return _ -> true
  | Ast.Break | Ast.Continue -> true
  | Ast.If (_, t, f) ->
    side_effects t
    ||
    (match f with
     | Some f -> side_effects f
     | None -> false)
  | Ast.While (_, b) -> side_effects b
  | Ast.Block ss -> List.exists side_effects ss
  | _ -> false
  ;;


let rec c_while = function
  | [] -> false
  | Ast.While _ :: _ -> true
  | Ast.Block ss :: rest -> c_while ss || c_while rest
  | _ :: rest -> c_while rest
;;


let rec con_while = function
  | Number _ -> true
  | Binop (_, e1, e2) -> con_while e1 && con_while e2
  | _ -> false
;;

let rec uvar_expr name = function
  | ID id -> id = name
  | Binop (_, e1, e2) -> uvar_expr name e1 || uvar_expr name e2
  | Unop (_, e) -> uvar_expr name e
  | Call (_, args) -> List.exists (uvar_expr name) args
  | _ -> false
;;

let rec uvar_stmt name stmt =
  match stmt with
  | Ast.Assign (_, e) -> uvar_expr name e
  | Decl (_, Some e) -> uvar_expr name e
  | ExprStmt e -> uvar_expr name e
  | If (cond, s1, s2_opt) ->
    uvar_expr name cond
    || uvar_stmt name s1
    ||
    (match s2_opt with
     | Some s2 -> uvar_stmt name s2
     | None -> false)
  | While (cond, s) -> uvar_expr name cond || uvar_stmt name s
  | Block ss -> List.exists (uvar_stmt name) ss
  | _ -> false
;;

let rec vars_expr = function
  | Ast.ID x -> S_set.singleton x
  | Ast.Unop (_, e) -> vars_expr e
  | Ast.Binop (_, l, r) -> S_set.union (vars_expr l) (vars_expr r)
  | Ast.Call (_, args) ->
    List.fold_left
      (fun acc e -> S_set.union acc (vars_expr e))
      S_set.empty
      args
  | _ -> S_set.empty
;;

let rec vars_stmt = function
  | Ast.ExprStmt e -> vars_expr e
  | Ast.Return (Some e) -> vars_expr e
  | Ast.Return None -> S_set.empty
  | Ast.Decl (_, Some e) -> vars_expr e
  | Ast.Assign (_, e) -> vars_expr e
  | Ast.If (c, t, f) ->
    S_set.union
      (vars_expr c)
      (S_set.union
         (vars_stmt t)
         (match f with
          | Some f -> vars_stmt f
          | None -> S_set.empty))
  | Ast.While (c, b) -> S_set.union (vars_expr c) (vars_stmt b)
  | Ast.Block ss ->
    List.fold_left
      (fun acc s -> S_set.union acc (vars_stmt s))
      S_set.empty
      ss
  | _ -> S_set.empty
;;


let rec r_while stmts =

  let rec go acc = function
    | [] -> List.rev acc
    | stmt :: rest ->
      let keep1 =
        match stmt with
        | Ast.While (_, body) ->
          let se = side_effects body in
          let writes = vars_stmt body in
          let future_reads =
            List.fold_left
              (fun s st -> S_set.union s (vars_stmt st))
              S_set.empty
              rest
          in
          not ((not se) && S_set.is_empty (S_set.inter writes future_reads))
        | Ast.Block _ -> true
        | _ -> true
      in
      let acc1 =
        if keep1
        then (
          let stmt' =
            match stmt with
            | Ast.Block ss -> Ast.Block (r_while ss)
            | other -> other
          in
          stmt' :: acc)
        else acc
      in
      go acc1 rest
  in
  go [] stmts
;;

let pre_ast (cu : Ast.comp_unit) : Ast.comp_unit =
  List.map
    (fun f ->
       if c_while f.Ast.body
       then { f with Ast.body = r_while f.Ast.body }
       else f )
    cu
;;

let rec tri_self_loop stmt =
  match stmt with
  | While (Binop (Less, ID var, Number _),
           Block [Assign (var2, Binop (Add, ID var3, Number 1))])
    when var = var2 && var = var3 ->
    Block []

  | Block stmts ->
    Block (stmts |> List.map tri_self_loop |> List.filter (function Block [] -> false | _ -> true))

  | If (cond, s1, s2_opt) ->
    If (
      cond,
      tri_self_loop s1,
      Option.map tri_self_loop s2_opt
    )

  | While (cond, Block body) ->
    While (cond, Block (List.map tri_self_loop body))

  | other -> other


let rec el_loop (stmt : stmt) : stmt =
  match stmt with
  | While (Binop (Less, ID idx, Number n), Block body) ->
    let match_loop stmts =
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
           let vaild_expr =
             List.filter_map
               (function
                 | Ast.Assign (acc, Binop (Add, ID acc2, expr))
                   when acc = acc2 && List.mem acc acc_names -> Some (acc, expr)
                 | _ -> None)
               inner_body
           in
           let valid =
             List.length vaild_expr = List.length acc_names
             && List.for_all
                  (fun acc -> List.mem acc acc_names)
                  (List.map fst vaild_expr)
           in
           if valid then Some (k_name, m, vaild_expr, tail) else None
         | _ -> None)
      | _ -> None
    in
    (match match_loop body with
     | Some (k_var, m, acc_exprs, tail_after_loop) ->
       let _ = List.map fst acc_exprs in
       let new_accs =
         List.map
           (fun (acc, expr) -> Ast.Assign (acc, Binop (Mul, expr, Number m)))
           acc_exprs
       in
       let k_decl =
         if List.exists (uvar_stmt k_var) tail_after_loop
         then [ Decl (k_var, Some (Number 0)) ]
         else []
       in
       let new_body =
         Block (k_decl @ new_accs @ List.map el_loop tail_after_loop)
       in
       While (Binop (Less, ID idx, Number n), new_body)
     | None ->
       While (Binop (Less, ID idx, Number n), Block (List.map el_loop body)))
  | While (cond, Block body) -> While (cond, Block (List.map el_loop body))
  | Block stmts -> Block (List.map el_loop stmts)
  | If (cond, t_branch, f_branch) ->
    If (cond, el_loop t_branch, Option.map el_loop f_branch)
  | _ -> stmt
;;

let el_loopfunc (f : func_def) : func_def =
  let new_body =
    f.body
    |> List.map el_loop
    |> List.map tri_self_loop
  in
  { f with body = new_body }
;;

let loop_elim_ast (cu : comp_unit) : comp_unit = List.map el_loopfunc cu

module LabelMap = Map.Make (String)

let temp_id = ref 0

let fr_temp () =
  let id = !temp_id in
  incr temp_id;
  Reg ("t" ^ string_of_int id)
;;

let name_id = ref 0

let fr_name base =
  let id = !name_id in
  incr name_id;
  base ^ "_" ^ string_of_int id
;;

let la_id = ref 0
let ir_label_id = ref 0

let fr_label () =
  let id = !la_id in
  incr la_id;
  "L" ^ string_of_int id
;;

let frir_label (label_map : string LabelMap.t) (l : param) : string * string LabelMap.t
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

let string_unop = function
  | Not -> "!"
  | Plus -> "+"
  | Minus -> "-"
;;

let string_binop = function
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"
  | Mod -> "%"
  | Eq -> "=="
  | Neq -> "!="
  | Less -> "<"
  | Leq -> "<="
  | Greater -> ">"
  | Geq -> ">="
  | Land -> "&&"
  | Lor -> "||"
;;

let rec expr_ir (ctx : text) (e : expr) : operand * inst_r list =
  match e with
  | Number n -> Imm n, []
  | ID name ->
    let operand = Estack.l_up name !(ctx.e_stack) in
    operand, []
  | Unop (op, e1) ->
    let operand, code = expr_ir ctx e1 in
    let res = fr_temp () in
    res, code @ [ Unop (string_unop op, res, operand) ]
  | Binop (op, e1, e2) ->
    let lhs, c1 = expr_ir ctx e1 in
    let rhs, c2 = expr_ir ctx e2 in
    (match op with
      | Land | Lor ->
        let dst = fr_temp () in
        dst, c1 @ c2 @ [ Binop (string_binop op, dst, lhs, rhs) ]
      | _ ->
        let dst = fr_temp () in
        dst, c1 @ c2 @ [ Binop (string_binop op, dst, lhs, rhs) ])
  | Call (f, args) ->
    let codes, oprs =
      List.fold_left
        (fun (acc_code, acc_opr) arg ->
           let opr, code = expr_ir ctx arg in
           acc_code @ code, acc_opr @ [ opr ])
        ([], [])
        args
    in
    let ret = fr_temp () in
    ret, codes @ [ Call (ret, f, oprs) ]
;;


type stmt_res =
  | Normal of inst_r list
  | Returned of inst_r list

let flatten = function
  | Normal code | Returned code -> code
;;

let always_returns (res : stmt_res) : bool =
  match res with
  | Returned _ -> true
  | Normal _ -> false
;;

let junp_return insts =
  match List.rev insts with
  | Goto _ :: _ -> true
  | Ret _ :: _ -> true
  | _ -> false
;;


let rec nor_expr = function
  | Ast.Unop (Not, Unop (Not, e)) -> nor_expr e
  | Unop (Not, Binop (Land, a, b)) ->
    nor_expr (Binop (Lor, Unop (Not, a), Unop (Not, b)))
  | Unop (Not, Binop (Lor, a, b)) ->
    nor_expr (Binop (Land, Unop (Not, a), Unop (Not, b)))
  | Unop (Not, Binop (op, a, b)) ->
    let neg =
      match op with
      | Eq -> Neq
      | Neq -> Eq
      | Less -> Geq
      | Leq -> Greater
      | Greater -> Leq
      | Geq -> Less
      | _ -> failwith "unsupported negation of this binary op"
    in
    Ast.Binop (neg, nor_expr a, nor_expr b)
  | Binop (op, a, b) -> Binop (op, nor_expr a, nor_expr b)
  | Unop (op, a) -> Unop (op, nor_expr a)
  | Call (f, args) -> Call (f, List.map nor_expr args)
  | e -> e
;;

let rec des_stmt = function
  | If (cond, then_b, Some else_b) ->
    let cond = nor_expr cond in
    let ands = spand cond in
    if List.length ands > 1
    then (
      let rec nest_and = function
        | [ x ] -> If (x, then_b, Some else_b)
        | hd :: tl -> If (hd, Block [ nest_and tl ], Some else_b)
        | [] -> Block []
      in
      nest_and ands |> des_stmt)
    else (
      let ors = spor cond in
      if List.length ors > 1
      then (
        let rec nest_or = function
          | [ x ] -> If (x, then_b, Some else_b)
          | hd :: tl -> If (hd, then_b, Some (nest_or tl))
          | [] -> Block []
        in
        nest_or ors |> des_stmt)
      else If (cond, des_stmt then_b, Some (des_stmt else_b)))
  | If (cond, then_b, None) ->
    let cond = nor_expr cond in
    let ands = spand cond in
    if List.length ands > 1
    then (
      let rec nest_and = function
        | [ x ] -> If (x, then_b, None)
        | hd :: tl -> If (hd, Block [ nest_and tl ], None)
        | [] -> Block []
      in
      nest_and ands |> des_stmt)
    else (
      let ors = spor cond in
      if List.length ors > 1
      then (
        let rec nest_or = function
          | [ x ] -> If (x, then_b, None)
          | hd :: tl -> If (hd, then_b, Some (nest_or tl))
          | [] -> Block []
        in
        nest_or ors |> des_stmt)
      else If (cond, des_stmt then_b, None))
  | While (cond, body) -> While (nor_expr cond, des_stmt body)
  | Block ss -> Block (List.map des_stmt ss)
  | other -> other
;;

let rec stmt_res (ctx : text) (in_tail : bool) (s : stmt) : stmt_res =
  match s with
  | Empty -> Normal []
  | ExprStmt e ->
    let _, code = expr_ir ctx e in
    Normal code
  | Decl (x, None) ->
    let new_name = fr_name x in
    ctx.e_stack := Estack.add x (Var new_name) !(ctx.e_stack);
    Normal []
  | Decl (x, Some e) ->
    let v, c = expr_ir ctx e in
    let new_name = fr_name x in
    ctx.e_stack := Estack.add x (Var new_name) !(ctx.e_stack);
    Normal (c @ [ Assign (Var new_name, v) ])
  | Assign (x, e) ->
    let v, c = expr_ir ctx e in
    let var = Estack.l_up x !(ctx.e_stack) in
    Normal (c @ [ Assign (var, v) ])
  | Return None -> if in_tail then Returned [] else Returned [ Ret None ]
  | Return (Some e) ->
    (match e with
     | Call (f, args) when f = ctx.func_name ->
       let arg_codes, arg_oprs =
         List.fold_left
           (fun (cc, oo) arg ->
              let o, c = expr_ir ctx arg in
              cc @ c, oo @ [ o ])
           ([], [])
           args
       in
       Returned (arg_codes @ [ TailCall (f, arg_oprs) ])
     | _ ->
       let r, code = expr_ir ctx e in
       Returned (code @ [ Ret (Some r) ]))
  | If (cond, tstmt, Some fstmt) ->
    let cnd, cc = expr_ir ctx cond in
    let lthen = fr_label ()
    and lelse = fr_label ()
    and lend = fr_label () in
    let then_res = stmt_res ctx in_tail tstmt
    and else_res = stmt_res ctx in_tail fstmt in
    let raw_then = flatten then_res in
    let then_code =
      if junp_return raw_then then raw_then else raw_then @ [ Goto lend ]
    in
    let raw_else = flatten else_res in
    let else_code =
      if junp_return raw_else then raw_else else raw_else @ [ Goto lend ]
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
    let cnd, cc = expr_ir ctx cond in
    let lthen = fr_label ()
    and lskip = fr_label () in
    let then_res = stmt_res ctx in_tail tstmt in
    let then_code = flatten then_res in
    let code =
      cc
      @ [ IfGoto (cnd, lthen); Goto lskip ]
      @ [ Label lthen ]
      @ then_code
      @ [ Label lskip ]
    in
    Normal code
  | While (cond, body) ->
    let lcond = fr_label ()
    and lbody = fr_label ()
    and lend = fr_label () in
    let ctx_loop = { ctx with breakb = Some lend; continueb = Some lcond } in
    let cnd, ccode = expr_ir ctx_loop cond in
    let body_res = stmt_res ctx_loop false body in
    let bcode = flatten body_res in
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
    (match ctx.breakb with
     | Some lbl -> Normal [ Goto lbl ]
     | None -> failwith "break used outside loop")
  | Continue ->
    (match ctx.continueb with
     | Some lbl -> Normal [ Goto lbl ]
     | None -> failwith "continue used outside loop")
  | Block stmts ->
    ctx.e_stack := Estack.enter !(ctx.e_stack);
    let rec loop acc = function
      | [] -> Normal acc
      | [ last ] ->
        (match stmt_res ctx in_tail last with
         | Returned c -> Returned (acc @ c)
         | Normal c -> Normal (acc @ c))
      | hd :: tl ->
        (match stmt_res ctx false hd with
         | Returned c -> Returned (acc @ c)
         | Normal c -> loop (acc @ c) tl)
    in
    let res = loop [] stmts in
    ctx.e_stack := Estack.exit !(ctx.e_stack);
    res
;;

let par_block (insts : inst_r list) : block_r list =
  let rec split acc curr label label_map insts =
    match insts with
    | [] -> List.rev acc
    | Label l :: rest ->
      (match curr with
       | [] ->
         let next_label, label_map' = frir_label label_map l in
         split acc [ Label l ] next_label label_map' rest
       | _ ->
         let next_label, label_map' = frir_label label_map l in
         let blk =
           { label
           ; insts = List.rev curr
           ; terminator = TermSeq next_label
           ; preds = []
           ; succs = []
           ; l_in = OperandSet.empty
           ; l_out = OperandSet.empty
           }
         in
         let acc1 = blk :: acc in
         split acc1 [ Label l ] next_label label_map' rest)
    | Goto l :: rest ->
      let goto_label, label_map' = frir_label label_map l in
      let next_label, label_map'' =
        frir_label label_map' ("__blk" ^ string_of_int !ir_label_id)
      in
      let blk =
        { label
        ; insts = List.rev (Goto l :: curr)
        ; terminator = TermGoto goto_label
        ; preds = []
        ; succs = []
        ; l_in = OperandSet.empty
        ; l_out = OperandSet.empty
        }
      in
      split (blk :: acc) [] next_label label_map'' rest
    | IfGoto (cond, l) :: rest ->
      let then_label, label_map' = frir_label label_map l in
      let else_label, label_map'' =
        frir_label label_map' ("__else" ^ string_of_int !ir_label_id)
      in
      let blk =
        { label
        ; insts = List.rev (IfGoto (cond, l) :: curr)
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
        frir_label label_map ("__ret" ^ string_of_int !ir_label_id)
      in
      let blk =
        { label
        ; insts = List.rev (Ret op :: curr)
        ; terminator = TermRet op
        ; preds = []
        ; succs = []
        ; l_in = OperandSet.empty
        ; l_out = OperandSet.empty
        }
      in
      split (blk :: acc) [] next_label label_map' rest
    | inst :: rest -> split acc (inst :: curr) label label_map rest
  in
  let entry_label, label_map = frir_label LabelMap.empty "entry" in
  split [] [] entry_label label_map insts
;;

let func_ir (f : func_def) : func_r =
  let des_body =
    match des_stmt (Block f.body) with
    | Block ss -> ss
    | _ -> f.body
  in
  let f' = { f with body = des_body } in
  let i_env = List.fold_left (fun m p -> Enwli.add p (Var p) m) Enwli.empty f'.params in
  let ctx0 =
    { func_name = f'.func_name
    ; e_stack = ref [ i_env ]
    ; breakb = None
    ; continueb = None
    }
  in
  let raw_res = stmt_res ctx0 false (Block f'.body) in
  let raw_code = flatten raw_res in
  let param_ops = List.map (fun p -> Var p) f'.params in
  let en_lab = fr_label () in
  let code_with_entry = Label en_lab :: raw_code in
  let final_code =
    List.concat_map
      (fun inst ->
         match inst with
         | TailCall (fname, args) when fname = f'.func_name ->
           List.map2 (fun param_op arg_op -> Assign (param_op, arg_op)) param_ops args
           @ [ Goto en_lab ]
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

(* 先只二元运算做 CSE *)
module E_map = Map.Make (struct
  type t = string * operand * operand (* op, lhs, rhs *)

  let compare = compare
end)

let cse_block (blk : block_r) : block_r =
  let expr_table = ref E_map.empty in
  let new_insts =
    List.fold_left
      (fun acc inst ->
         match inst with
         | Binop (op, dst, lhs, rhs) ->
           let key = op, lhs, rhs in
           (match E_map.find_opt key !expr_table with
            | Some prev ->
              Assign (dst, prev) :: acc
            | None ->
              expr_table := E_map.add key dst !expr_table;
              inst :: acc)
         | _ ->
           let kills_all =
             match inst with
             | Store _ | Call _ | TailCall _ | Ret _ -> true
             | _ -> false
           in
           if kills_all then expr_table := E_map.empty;
           inst :: acc)
      []
      blk.insts
    |> List.rev
  in
  { blk with insts = new_insts }
;;

let dcode_elim blocks (print_l : bool) =
  liv_analy blocks print_l;
  List.map
    (fun blk ->
       let live = ref blk.l_out in
       let new_insts =
         List.fold_right
           (fun inst acc ->
              let def, use = def_inst inst in
              let must_keep = has_effect inst in
              let def_is_live =
                (not (OperandSet.is_empty def))
                && OperandSet.exists (fun v -> OperandSet.mem v !live) def
              in
              if must_keep || def_is_live
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

module O_map = Map.Make (struct
  type t = operand

  let compare = compare
end)

let rec res_copy env op =
  match op with
  | Var _ | Reg _ ->
    (match O_map.find_opt op env with
     | Some v when v <> op -> res_copy env v
     | _ -> op)
  | _ -> op
;;

let copy_block (blk : block_r) : block_r =
  let copy_env = ref O_map.empty in
  let propagate_op op = res_copy !copy_env op in
  let new_insts =
    List.filter_map
      (fun inst ->
         match inst with
         | Assign (dst, src) ->
           let src' = propagate_op src in
           if dst = src'
           then None
           else (
             copy_env := O_map.add dst src' !copy_env;
             Some (Assign (dst, src')))
         | Binop (op, dst, lhs, rhs) ->
           let lhs' = propagate_op lhs in
           let rhs' = propagate_op rhs in
           copy_env := O_map.remove dst !copy_env;
           Some (Binop (op, dst, lhs', rhs'))
         | Unop (op, dst, src) ->
           let src' = propagate_op src in
           copy_env := O_map.remove dst !copy_env;
           Some (Unop (op, dst, src'))
         | Load (dst, src) ->
           let src' = propagate_op src in
           copy_env := O_map.remove dst !copy_env;
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
           copy_env := O_map.remove dst !copy_env;
           Some (Call (dst, fname, args'))
         | TailCall (fname, args) ->
           let args' = List.map propagate_op args in
           Some (TailCall (fname, args'))
         | Goto _ | IfGoto _ | Label _ | Ret None -> Some inst)
      blk.insts
  in
  { blk with insts = new_insts }
;;

module StringMap = Map.Make (String)

let dce2_block (blk : block_r) : unit =
  let def_map =
    List.fold_left
      (fun acc inst ->
         match inst with
         | Binop (_, dst, _, _)
         | Unop (_, dst, _)
         | Assign (dst, _)
         | Load (dst, _)
         | Call (dst, _, _) ->
           (match dst with
            | Reg r | Var r -> StringMap.add r inst acc
            | _ -> acc)
         | _ -> acc)
      StringMap.empty
      blk.insts
  in
  let term_vars =
    match blk.terminator with
    | TermRet (Some op) | TermIf (op, _, _) ->
      (match op with
       | Reg r | Var r -> S_set.singleton r
       | _ -> S_set.empty)
    | _ -> S_set.empty
  in
  let roots = term_vars in
  let rec coll acc worklist =
    match worklist with
    | [] -> acc
    | v :: rest when S_set.mem v acc -> coll acc rest
    | v :: rest ->
      let acc = S_set.add v acc in
      let new_vars =
        match StringMap.find_opt v def_map with
        | Some inst ->
          let use_vars =
            match inst with
            | Binop (_, _, lhs, rhs) | Store (lhs, rhs) -> [ lhs; rhs ]
            | Unop (_, _, src) | Load (_, src) | Assign (_, src) -> [ src ]
            | Call (_, _, args) -> args
            | _ -> []
          in
          use_vars
          |> List.filter_map (function
              | Reg r | Var r -> Some r
              | _ -> None)
        | None -> []
      in
      coll acc (new_vars @ rest)
  in
  let useful_vars = coll S_set.empty (S_set.elements roots) in
  blk.insts
  <- List.filter
    (fun inst ->
       match inst with
       | Binop (_, dst, _, _)
       | Unop (_, dst, _)
       | Assign (dst, _)
       | Load (dst, _)
       | Call (dst, _, _) ->
         (match dst with
          | Reg r | Var r -> S_set.mem r useful_vars
          | _ -> false)
       | _ -> true )
    blk.insts
;;

let rec expr_on (e : expr) (vars : S_set.t) : bool =
  match e with
  | ID x -> S_set.mem x vars
  | Number _ -> false
  | Binop (_, e1, e2) | Call (_, [ e1; e2 ]) ->
    expr_on e1 vars || expr_on e2 vars
  | Call (_, args) -> List.exists (fun e -> expr_on e vars) args
  | Unop (_, e1) -> expr_on e1 vars
;;

let func_iro (f : func_def) (print_l : bool) : ir_func_o =
  let des_body =
    match des_stmt (Block f.body) with
    | Block ss -> ss
    | _ -> f.body
  in
  let f' = { f with body = des_body } in
  let i_env = List.fold_left (fun m p -> Enwli.add p (Var p) m) Enwli.empty f'.params in
  let ctx0 =
    { func_name = f'.func_name
    ; e_stack = ref [ i_env ]
    ; breakb = None
    ; continueb = None
    }
  in
  let raw_code =
    try stmt_res ctx0 false (Block f'.body) |> flatten with
    | e ->
      Printf.eprintf
        "Error generating IR for %s: %s\n"
        f'.func_name
        (Printexc.to_string e);
      raise e
  in
  let en_lab = "entry_" ^ f'.func_name in
  let tail_elim_ir = ref [ Label en_lab ] in
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
         tail_elim_ir := !tail_elim_ir @ assigns @ [ Goto en_lab ]
       | _ -> tail_elim_ir := !tail_elim_ir @ [ inst ])
    raw_code;
  let raw_blocks = par_block !tail_elim_ir in
  let cfg_blocks = Cfg.b_cfg raw_blocks in
  let opt_blocks = Cfg.opt cfg_blocks in
  let dce_blocks = dcode_elim opt_blocks print_l in
  let cse_blocks = List.map (fun x -> cse_block x) dce_blocks in
  let copy_blocks = List.map copy_block cse_blocks in
  let final_blocks = dcode_elim copy_blocks print_l in
  { name = f'.func_name; args = f'.params; blocks = final_blocks }
;;


let rec opt_stmt stmt =
  match stmt with
  | While (cond, body) ->
    While (cond, opt_stmt body)
  | Block slist -> Block (List.map opt_stmt slist)
  | If (e, s1, Some s2) -> If (e, opt_stmt s1, Some (opt_stmt s2))
  | If (e, s1, None) -> If (e, opt_stmt s1, None)
  | _ -> stmt
;;

let opt_func (f : func_def) : func_def =
  { f with body = List.map opt_stmt f.body }
;;

let opt (prog : comp_unit) : comp_unit = List.map opt_func prog

let pro_ir (cu : comp_unit) (optimize_flag : bool) (print_l : bool)
  : ir_program
  =
  let cu1 = if optimize_flag then cu |> pre_ast |> loop_elim_ast |> opt |> loop_elim_ast else cu in
  let cu1 = opt cu1 in
  if optimize_flag
  then Ir_funcs_o (List.map (fun f -> func_iro f print_l) cu1)
  else Ir_funcs (List.map func_ir cu1)
;;