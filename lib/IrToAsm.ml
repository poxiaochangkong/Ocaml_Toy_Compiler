open Ir
open Reg

let st_size = 1648
let st_off = ref 0
let var_env = Hashtbl.create 1024
let r_map : (string, string) Hashtbl.t =
  Hashtbl.create 256 (* 建立一个map用于保存变量名和分配的寄存器号的映射 *)
let s_var : (operand, int) Hashtbl.t =
  Hashtbl.create 256  (* 用于保存被暂时存放到内存里的变量名和内存偏移量 *)

let f_call : (string, string list) Hashtbl.t = Hashtbl.create 16
let regpoll = ref [ "t0"; "t1"; "t2"; "t3"; "t4"; "t5"; "t6" ] (* 可以使用的寄存器 *)

let valid_regs =
  [
    "zero";
    "ra";
    "sp";
    "gp";
    "tp";
    "t0";
    "t1";
    "t2";
    "t3";
    "t4";
    "t5";
    "t6";
    "s0";
    "s1";
    "s2";
    "s3";
    "s4";
    "s5";
    "s6";
    "s7";
    "s8";
    "s9";
    "s10";
    "s11";
    "a0";
    "a1";
    "a2";
    "a3";
    "a4";
    "a5";
    "a6";
    "a7";
  ]


let get_offset var = (*获得某个变量的偏移量*)
  try Hashtbl.find var_env var
  with Not_found -> failwith ("Unknown variable: " ^ var)

let all_stack var =   (*修改栈顶的偏移地址*)
  try get_offset var
  with _ ->
    st_off := !st_off + 4;
    Hashtbl.add var_env var (- !st_off - 4);
    (* 从 -8 开始分配 *)
    -(!st_off + 4)

let op_str = function     (*将表达式转变为字符串*)
  | Reg r | Var r -> Printf.sprintf "%d(sp)" (get_offset r)
  | Imm i -> Printf.sprintf "%d" i

let l_oper (reg : string) (op : operand) : string =
  match op with
  | Imm i -> Printf.sprintf "\tli %s, %d\n" reg i
  | Reg r | Var r ->
      Printf.sprintf "\tlw %s, %d(s0)\n" reg
        (get_offset  r)


let fits_imm12 i = i >= -2048 && i <= 2047

let emit_li_and_op instr dst src imm =
  Printf.sprintf "\tli t6, %d\n\t%s %s, %s, t6\n" imm instr dst src

let spill_stack (op : operand) =
  try Hashtbl.find s_var op
  with _ ->
    st_off := !st_off + 4;   (*注意这里是是+4*)
    if !st_off >= 1644 then failwith "to large!\n";
    Hashtbl.add s_var op (- !st_off - 4);
    - !st_off - 4

let com_inst_with_liveness (r_map : string O_hash.t)
    (inst : inst_r) (_live_out : OperandSet.t) (call_restore_code : string)
    (need : bool) : string =
  let temp_regs = ref [ "t5"; "t6"; "t4" ] in
  let temp_r_map = Hashtbl.create 3 in

  let alloc_temp_reg (v : operand) : string =
    match !temp_regs with
    | [] -> failwith "Ran out of temporary registers for spilling"
    | r :: rest ->
        temp_regs := rest;
        Hashtbl.add temp_r_map v r;
        r
  in

  (* 加载代码实际寄存器 *)
  let dstreg (op : operand) : string * string =
    match op with
    | Imm _ -> failwith "Imm can't be dst"
    | _ -> (
        match O_hash.find_opt r_map op with
        | Some reg when reg <> "__SPILL__" -> ("", reg)
        | _ ->
            let tmp_reg = alloc_temp_reg op in
            let var_name =
              match op with
              | Var v -> "Var " ^ v
              | Reg v -> "Reg " ^ v
              | _ -> "?"
            in
            let offset, debug_info =
              try
                let op_string =
                  match op with Var x -> x | Reg x -> x | _ -> failwith ""
                in
                (get_offset op_string, "alloc_var")
              with _ -> (spill_stack op, "spill_var")
            in
            ( Printf.sprintf "\tlw %s, %d(s0) # reload %s -- %s\n" tmp_reg
                offset var_name debug_info,
              tmp_reg ))
  in

  let get_src_reg (op : operand) : string * string =  (*操作数为imm的时候*)
    match op with
    | Imm i ->
        let tmp_reg = alloc_temp_reg op in
        (Printf.sprintf "\tli %s, %d # tmp load imm \n" tmp_reg i, tmp_reg)
    | _ -> (
        match O_hash.find_opt r_map op with
        | Some reg when reg <> "__SPILL__" -> ("", reg)
        | _ ->
            let tmp_reg = alloc_temp_reg op in
            let var_name =
              match op with Var v -> "Var" ^ v | Reg v -> "Reg" ^ v | _ -> "?"
            in
            let offset, debug_info =
              try
                let op_string =
                  match op with Var x -> x | Reg x -> x | _ -> failwith ""
                in
                (get_offset op_string, "alloc_var")
              with _ -> (spill_stack op, "spill_var")
            in
            ( Printf.sprintf "\tlw %s, %d(s0) # reload %s -- %s\n" tmp_reg
                offset var_name debug_info,
              tmp_reg ))
  in

  let argreg (op : operand) : string * string =
    match op with
    | Imm _ -> failwith "Imm can't be dst"
    | _ -> (
        match O_hash.find_opt r_map op with
        | Some reg when reg <> "__SPILL__" -> ("", reg)
        | _ ->
            let tmp_reg = "t6" in
            let var_name =
              match op with
              | Var v -> "Var " ^ v
              | Reg v -> "Reg " ^ v
              | _ -> "?"
            in
            let offset =
              try
                let op_string = match op with Var x -> x | _ -> failwith "" in
                get_offset op_string
              with _ -> spill_stack op
            in
            ( Printf.sprintf "\tlw %s, %d(s0) # reload %s\n" tmp_reg offset
                var_name,
              tmp_reg ))
  in
  let restore_ret =
    if need then
      Printf.sprintf
        "\tlw ra, %d(s0)\n\tlw s0, %d(sp)\n\taddi sp, sp, %d\n\tret\n"
        (get_offset "ra") (st_size - 4) st_size
    else "\tret\n"
  in

 let store_dst dst dst_reg =   (*store指令的生成*)
    let get_stackoff op =
      let op_string = match op with Reg _ | Imm _ -> "" | Var v -> v in
      try Some (get_offset op_string) with _ -> None
    in
    let var_str =
      match dst with
      | Var v -> "Var " ^ v
      | Reg v -> "Reg " ^ v
      | _ -> "Cannot spill imm!"
    in
    match O_hash.find_opt r_map dst with
    | Some "__SPILL__" ->
        let offset = spill_stack dst in
        Printf.sprintf "\tsw %s, %d(s0) # save spilled %s\n" dst_reg offset
          var_str
    | _ -> (
        match get_stackoff dst with
        | Some offset ->
            Printf.sprintf "\tsw %s, %d(s0) # writeback param %s\n" dst_reg
              offset var_str
        | None -> "")
  in
  match inst with
  | TailCall (fname, args) ->
      let par_set =
        List.mapi
          (fun i arg ->
            let load_code, reg = argreg arg in
            if i < 8 then
              load_code ^ Printf.sprintf "\tmv a%d, %s\n" i reg
            else
              let offset = 4 * (i - 8) in
              load_code ^ Printf.sprintf "\tsw %s, %d(s0)\n" reg offset)
          args
        |> String.concat ""
      in
      let entry_lbl = fname ^ "_entry" in
      par_set ^ Printf.sprintf "\tj %s\n" entry_lbl

  | Binop (op, dst, lhs, rhs) -> (
      match dst with
      | Imm _ -> failwith "Binop dst 不应为 Imm"
      | _ ->
        (
          let dst_load, dst_reg = dstreg dst in
          let lhs_load, r1 = get_src_reg lhs in
          let rhs_load, r2 = get_src_reg rhs in
          let i_code =
            match op with
            | "+" -> Printf.sprintf "\tadd %s, %s, %s\n" dst_reg r1 r2
            | "-" -> Printf.sprintf "\tsub %s, %s, %s\n" dst_reg r1 r2
            | "*" -> Printf.sprintf "\tmul %s, %s, %s\n" dst_reg r1 r2
            | "/" -> Printf.sprintf "\tdiv %s, %s, %s\n" dst_reg r1 r2
            | "%" -> Printf.sprintf "\trem %s, %s, %s\n" dst_reg r1 r2
            | "==" ->
                Printf.sprintf "\tsub %s, %s, %s\n\tseqz %s, %s\n" dst_reg
                  r1 r2 dst_reg dst_reg
            | "!=" ->
                Printf.sprintf "\tsub %s, %s, %s\n\tsnez %s, %s\n" dst_reg
                  r1 r2 dst_reg dst_reg
            | "<" -> Printf.sprintf "\tslt %s, %s, %s\n" dst_reg r1 r2
            | ">" -> Printf.sprintf "\tsgt %s, %s, %s\n" dst_reg r1 r2
            | "<=" ->
                Printf.sprintf "\tsgt %s, %s, %s\n\txori %s, %s, 1\n"
                  dst_reg r1 r2 dst_reg dst_reg
            | ">=" ->
                Printf.sprintf "\tslt %s, %s, %s\n\txori %s, %s, 1\n"
                  dst_reg r1 r2 dst_reg dst_reg
            | "&&" -> Printf.sprintf "\tand %s, %s, %s\n" dst_reg r1 r2
            | "||" -> Printf.sprintf "\tor %s, %s, %s\n" dst_reg r1 r2
            | _ -> failwith ("Unknown binop: " ^ op)
          in
          let store_code = store_dst dst dst_reg in
          String.concat ""
            [ lhs_load; rhs_load; dst_load; i_code; store_code ]
        )
    )
  | Unop (op, dst, src) ->
      let dst_load, dst_reg = dstreg dst in
      let src_load, src_reg = get_src_reg src in
      let body =
        match op with
        | "-" -> Printf.sprintf "\tsub %s, zero, %s\n" dst_reg src_reg
        | "!" -> Printf.sprintf "\tseqz %s, %s\n" dst_reg src_reg
        | "+" -> ""
        | _ -> failwith ("Unknown unop: " ^ op)
      in
      let store_code = store_dst dst dst_reg in
      dst_load ^ src_load ^ body ^ store_code
  | Assign (dst, src) -> (
      let dst_load, dst_reg = dstreg dst in
      match src with
      | Imm i ->
          let body = Printf.sprintf "\tli %s, %d\n" dst_reg i in
          let store_code = store_dst dst dst_reg in
          dst_load ^ body ^ store_code
      | _ ->
          let src_load, src_reg = dstreg src in
          let body = Printf.sprintf "\tmv %s, %s\n" dst_reg src_reg in
          let store_code = store_dst dst dst_reg in
          dst_load ^ src_load ^ body ^ store_code)
  | Load (dst, addr) ->
      let dst_load, dst_reg = dstreg dst in
      let addr_load, addr_reg = dstreg addr in
      let body = Printf.sprintf "\tlw %s, 0(%s)\n" dst_reg addr_reg in
      let store_code = store_dst dst dst_reg in
      dst_load ^ addr_load ^ body ^ store_code
  | Store (addr, value) ->
      let addr_load, addr_reg = dstreg addr in
      let val_load, val_reg = dstreg value in
      addr_load ^ val_load ^ Printf.sprintf "\tsw %s, 0(%s)\n" val_reg addr_reg
  | Call (dst, fname, args) ->
      let used_by_callee =
        match Hashtbl.find_opt f_call fname with
        | Some regs -> regs
        | None -> []
      in

      let to_save = ref [] in

      OperandSet.iter
        (fun op ->
          match O_hash.find_opt r_map op with
          | Some reg when reg <> "__SPILL__" && List.mem reg used_by_callee ->
              let offset = spill_stack op in
              to_save := (op, reg, offset) :: !to_save
          | _ -> ())
        _live_out;

      let save_code =
        List.map
          (fun (op, reg, offset) ->
            let var_str =
              match op with
              | Var v -> v
              | Reg v -> v
              | Imm i -> failwith (Printf.sprintf "%d" i)
            in
            Printf.sprintf "\tsw %s, %d(s0)  # save caller-saved %s\n" reg
              offset var_str)
          !to_save
        |> String.concat ""
      in

      let restore_code =
        List.map
          (fun (op, reg, offset) ->
            let var_str =
              match op with
              | Var v -> v
              | Reg v -> v
              | Imm i -> failwith (Printf.sprintf "%d" i)
            in
            Printf.sprintf "\tlw %s, %d(s0)  # restore caller-saved %s\n" reg
              offset var_str)
          !to_save
        |> String.concat ""
      in

      let reg_moved = alloc_temp_reg (Var "__temp_moved") in
      let ret_tmp = Printf.sprintf "\tmv %s, a0 # move a0 to temp_reg\n" reg_moved in
      let _, dst_reg = dstreg dst in
      let tmp_dst =
        Printf.sprintf "\tmv %s, %s  # move return value from temp_reg %s\n" dst_reg reg_moved reg_moved
        ^ store_dst dst dst_reg
      in

      (* 设置函数参数 *)
      let arg_regs = [| "a0"; "a1"; "a2"; "a3"; "a4"; "a5"; "a6"; "a7" |] in
      let args_code =
        List.mapi
          (fun i arg ->
            match arg with
            | Imm n when i < 8 -> Printf.sprintf "\tli %s, %d\n" arg_regs.(i) n
            | _ when i < 8 ->
                let load, reg = argreg arg in
                load ^ Printf.sprintf "\tmv %s, %s\n" arg_regs.(i) reg
            | Imm n ->
                let off = 4 * (i - 8) in
                Printf.sprintf "\tli t6, %d\n\tsw t6, %d(sp)\n" n off
            | _ ->
                let off = 4 * (i - 8) in
                let load, reg = argreg arg in
                load ^ Printf.sprintf "\tsw %s, %d(sp)\n" reg off)
          args
        |> String.concat ""
      in

      save_code ^ args_code
      ^ Printf.sprintf "\tcall %s\n" fname
      ^ ret_tmp
      ^ restore_code
      ^ tmp_dst
  | IfGoto (cond, label) -> (
      match cond with
      | Imm 0 -> ""
      | Imm _ -> Printf.sprintf "\tj %s\n" label
      | _ ->
          let cond_load, cond_reg = dstreg cond in
          cond_load ^ Printf.sprintf "\tbnez %s, %s\n" cond_reg label)
  | Goto label -> Printf.sprintf "\tj %s\n" label
  | Label label -> Printf.sprintf "%s:\n" label
  | Ret None -> call_restore_code ^ restore_ret
  | Ret (Some op) ->
      (match op with
      | Imm i -> Printf.sprintf "\tli a0, %d\n" i
      | _ ->
          let ret_load, ret_reg = dstreg op in
          let mv_code =
            if ret_reg = "a0" then ""
            else Printf.sprintf "\tmv a0, %s\n" ret_reg
          in
          ret_load ^ mv_code)
      ^ call_restore_code ^ restore_ret

let com_inst (inst : inst_r) (need : bool) : string =
  match inst with
  | Binop (op, dst, lhs, rhs) ->
      let dst_off =
        all_stack
          (match dst with Reg r | Var r -> r | _ -> failwith "Bad dst")
      in
      let lhs_code = l_oper "t1" lhs in
      let rhs_code = l_oper "t2" rhs in
      let op_code =
        match op with
        | "+" -> "\tadd t0, t1, t2\n"
        | "-" -> "\tsub t0, t1, t2\n"
        | "*" -> "\tmul t0, t1, t2\n"
        | "/" -> "\tdiv t0, t1, t2\n"
        | "%" -> "\trem t0, t1, t2\n"
        | "==" -> "\tsub t0, t1, t2\n\tseqz t0, t0\n"
        | "!=" -> "\tsub t0, t1, t2\n\tsnez t0, t0\n"
        | "<=" -> "\tsgt t0, t1, t2\n\txori t0, t0, 1\n"
        | ">=" -> "\tslt t0, t1, t2\n\txori t0, t0, 1\n"
        | "<" -> "\tslt t0, t1, t2\n"
        | ">" -> "\tsgt t0, t1, t2\n"
        | "&&" -> "\tand t0, t1, t2\n"
        | "||" -> "\tor t0, t1, t2\n"
        | _ -> failwith ("Unknown binop: " ^ op)
      in
      lhs_code ^ rhs_code ^ op_code ^ Printf.sprintf "\tsw t0, %d(s0)\n" dst_off
  | Unop (op, dst, src) ->
      let dst_off =
        all_stack
          (match dst with Reg r | Var r -> r | _ -> failwith "Bad dst")
      in
      let load_src = l_oper "t1" src in
      let op_code =
        match op with
        | "-" -> "\tneg t0, t1\n"
        | "!" -> "\tseqz t0, t1\n"
        | "+" -> "\tmv t0, t1\n"
        | _ -> failwith ("Unknown unop: " ^ op)
      in
      load_src ^ op_code ^ Printf.sprintf "\tsw t0, %d(s0)\n" dst_off
  | Assign (dst, src) ->
      let dst_off =
        all_stack
          (match dst with Reg r | Var r -> r | _ -> failwith "Bad dst")
      in
      let load_src = l_oper "t0" src in
      load_src ^ Printf.sprintf "\tsw t0, %d(s0)\n" dst_off
  | Load (dst, src) ->
      let dst_off =
        all_stack
          (match dst with Reg r | Var r -> r | _ -> failwith "Bad dst")
      in
      let src_code = l_oper "t1" src in
      src_code ^ "\tlw t0, 0(t1)\n" ^ Printf.sprintf "\tsw t0, %d(s0)\n" dst_off
  | Store (dst, src) ->
      let dst_code = l_oper "t1" dst in
      let src_code = l_oper "t2" src in
      dst_code ^ src_code ^ "\tsw t2, 0(t1)\n"
  | Call (dst, fname, args) ->
      let dst_off =
        all_stack
          (match dst with Reg r | Var r -> r | _ -> failwith "Bad dst")
      in
      let args_code =
        List.mapi
          (fun i arg ->
            if i < 8 then l_oper (Printf.sprintf "a%d" i) arg
            else
              let offset = 4 * (i - 8) in
              l_oper "t0" arg ^ Printf.sprintf "\tsw t0, %d(sp)\n" offset)
          args
        |> String.concat ""
      in
      args_code ^ Printf.sprintf "\tcall %s\n\tsw a0, %d(s0)\n" fname dst_off
      (* 尾调用消除 *)
  | TailCall (fname, args) ->
      let param_stores =
        List.mapi
          (fun i arg ->
            let load = l_oper "t0" arg in
            if i < 8 then
              load ^ Printf.sprintf "\tmv a%d, t0\n" i
            else
              let offset = 4 * (i - 8) in
              load ^ Printf.sprintf "\tsw t0, %d(s0)\n" offset)
          args
        |> String.concat ""
      in
      let entry_label = fname ^ "_entry" in
      param_stores ^ Printf.sprintf "\tj %s\n" entry_label
  | Ret None ->
      if need then
        Printf.sprintf
          "\tlw ra, %d(s0)\n\tlw s0, %d(sp)\n\taddi sp, sp, %d\n\tret\n"
          (get_offset "ra") (st_size - 4) st_size
      else "\tret\n"
  | Ret (Some op) ->
      let load_code = l_oper "a0" op in
      if need then
        let ra_offset = all_stack "ra" in
        load_code
        ^ Printf.sprintf
            "\tlw ra, %d(s0)\n\tlw s0, %d(sp)\n\taddi sp, sp, %d\n\tret\n"
            ra_offset (st_size - 4) st_size
      else load_code ^ "\tret\n"
  | Goto label -> Printf.sprintf "\tj %s\n" label
  | IfGoto (cond, label) -> (
      match cond with
      | Imm 0 -> ""
      | Imm _ -> Printf.sprintf "\tj %s\n" label
      | _ ->
          let cond_code = l_oper "t0" cond in
          cond_code ^ Printf.sprintf "\tbne t0, x0, %s\n" label)
  | Label label -> Printf.sprintf "%s:\n" label

let com_block (blk : block_r) (r_map : string O_hash.t)
    (need : bool) (call_restore_code : string) : string =
  let code_acc = ref [] in
  let live = ref blk.l_out in

  List.iter
    (fun inst ->
      let def, use = Op.def_inst inst in
      let l_out = !live in
      let i_code =
        com_inst_with_liveness r_map inst l_out call_restore_code
          need
      in
      code_acc := i_code :: !code_acc;
      live := OperandSet.union (OperandSet.diff !live def) use)
    (List.rev blk.insts);

  String.concat "" !code_acc

let need_frame (f : ir_func_o) (r_map : string O_hash.t)
    (callee_saved : string list) : bool =
  let calls_other_functions =
    List.exists
      (fun blk ->
        List.exists
          (function
            | Call _ -> true
            | TailCall _ -> true
            | _ -> false)
          blk.insts)
      f.blocks
  in
  let has_spilled_vars =
    O_hash.fold
      (fun _ reg acc -> acc || reg = "__SPILL__")
      r_map false
  in
  calls_other_functions || has_spilled_vars || callee_saved <> []
let com_func (f : func_r) : string =
  Hashtbl.clear var_env;
  st_off := 0;

  let par_tp =
    Printf.sprintf "\tsw s0, %d(sp)\n" (st_size - 4)
  in

  let par_set =
    List.mapi
      (fun i name ->
        if i >= 8 then
          let off = all_stack name in
          Printf.sprintf "\tlw t5, %d(s0)\n\tsw t5, %d(s0)\n"
            (4 * (i - 8))
            off
        else
          let off = all_stack name in
          Printf.sprintf "\tsw a%d, %d(s0)\n" i off)
      f.args
    |> String.concat ""
  in

  let par_set =
    par_set ^ Printf.sprintf "\tsw ra, %d(s0)\n" (all_stack "ra")
  in

  let body_c =
    f.body |> List.map (fun inst -> com_inst
  inst true) |> String.concat ""
  in

  let body_c =
    if not (String.ends_with ~suffix:"\tret\n" body_c) then       (* 检查 body_c 是否以 ret 结束; 没有默认添加 "\taddi sp, sp, 1024\n\tret\n" 语句; 其实可以前移到 IR 阶段 *)
      body_c
      ^ Printf.sprintf
          "\tlw ra, %d(s0)\n\tlw s0, %d(sp)\n\taddi sp, sp, %d\n\tret\n"
          (get_offset "ra") (st_size - 4) st_size
    else body_c
  in
  let func_label = f.name in
  let prologue =
    Printf.sprintf "%s:\n\taddi sp, sp, -%d\n" func_label st_size
    ^ par_tp
    ^ Printf.sprintf "\taddi s0, sp, %d\n" st_size
  in
  prologue ^ par_set ^ body_c


let fresh_temp () : string =     (*从寄存器库中取最新的可以使用的寄存器temp*)
  match !regpoll with
  | r :: rest ->
      regpoll := rest;
      r
  | [] -> failwith "No free temporary registers available"


let use reg =     (*使用确定的可使用的寄存器，并且在库中删除该寄存器*)
  let new_pool = List.filter (fun (x : string) -> x <> reg) !regpoll in
  regpoll := new_pool

let free reg =              (*清空所有的寄存器*)
  let to_remove = ref [] in
  (* 移除所有存放在 reg 里的 var *)
  Hashtbl.iter
    (fun var r -> if r = reg then to_remove := var :: !to_remove)
    r_map;
  List.iter (Hashtbl.remove r_map) !to_remove;
  regpoll := reg :: !regpoll

let com_func_o (f : ir_func_o) (print_alloc : bool) : string =
  Hashtbl.clear var_env;
  Hashtbl.clear r_map;
  Hashtbl.clear s_var;
  st_off := 0;

  Op.liv_analy f.blocks print_alloc;
  let intervals = b_inter f in
  let r_map = lin_alloca intervals print_alloc in
  let used_saveed =
    let caller_saved =
      [
        "t0";
        "t1";
        "t2";
        "t3";
        "t4";
        "t5";
        "t6";
        "a1";
        "a2";
        "a3";
        "a4";
        "a5";
        "a6";
        "a7";
      ]
    in
    O_hash.fold
      (fun _ reg acc ->
        if List.mem reg caller_saved && not (List.mem reg acc) then reg :: acc
        else acc)
      r_map []
  in
  let arg_regs = [| "a0"; "a1"; "a2"; "a3"; "a4"; "a5"; "a6"; "a7" |] in
  let par_reg =
    List.mapi (fun i _ -> if i < 8 then arg_regs.(i) else "") f.args
    |> List.filter (fun r -> r <> "")
  in

  let used_saveed =
    List.fold_left
      (fun acc reg -> if List.mem reg acc then acc else reg :: acc)
      used_saveed par_reg
  in
  Hashtbl.replace f_call f.name used_saveed;

  let call_saved =
    let callee_saved =
      [
        "s0"; "s1"; "s2"; "s3"; "s4"; "s5"; "s6"; "s7"; "s8"; "s9"; "s10"; "s11";
      ]
    in
    O_hash.fold
      (fun _ reg acc ->
        if List.mem reg callee_saved && not (List.mem reg acc) then reg :: acc
        else acc)
      r_map []
  in

  let need = need_frame f r_map call_saved in

  let call_code =
    call_saved
    |> List.map (fun reg ->
            let offset = spill_stack (Reg reg) in
            Printf.sprintf "\tsw %s, %d(s0)  # save callee-saved\n" reg offset)
    |> String.concat ""
  in

  let call_restore_code =
    call_saved
    |> List.map (fun reg ->
            let offset = spill_stack (Reg reg) in
            Printf.sprintf "\tlw %s, %d(s0)  # restore callee-saved\n" reg offset)
    |> String.concat ""
  in

  let prologue, par_set =
    if need then
      let par_tp =
        Printf.sprintf "\tsw s0, %d(sp)\n" (st_size - 4)
      in
      let par_set =
        List.mapi
          (fun i name ->
            if i >= 8 then
              let off = spill_stack (Var name) in
              Printf.sprintf "\tlw t5, %d(s0)\n\tsw t5, %d(s0)\n"
                (4 * (i - 8))
                off
            else
              let off = spill_stack (Var name) in
              Printf.sprintf "\tsw a%d, %d(s0)\n" i off)
          f.args
        |> String.concat ""
      in
      let par_set =
        par_set
        ^ Printf.sprintf "\tsw ra, %d(s0)\n" (all_stack "ra")
        ^ call_code
      in
      let prologue =
        Printf.sprintf "%s:\n\taddi sp, sp, -%d\n" f.name st_size
        ^ par_tp
        ^ Printf.sprintf "\taddi s0, sp, %d\n" st_size
      in
      (prologue, par_set)
    else (Printf.sprintf "%s:\n" f.name, "")
  in

  let body_c =
    f.blocks
    |> List.map (fun blk ->
            com_block blk r_map need call_restore_code)
    |> String.concat ""
  in

  let epilogue =
    if need then
      if not (String.ends_with ~suffix:"\tret\n" body_c) then
        call_restore_code
        ^ Printf.sprintf
            "\tlw ra, %d(s0)\n\tlw s0, %d(sp)\n\taddi sp, sp, %d\n\tret\n"
            (get_offset "ra") (st_size - 4) st_size
      else ""
    else if not (String.ends_with ~suffix:"\tret\n" body_c) then "\tret\n"
    else ""
  in

  prologue ^ par_set ^ body_c ^ epilogue

let com_pro (prog : ir_program) (print_alloc : bool) : string =
  let prologue = ".text\n .globl main\n" in
  let body_asm =
    match prog with
    | Ir_funcs funcs -> List.map com_func funcs |> String.concat "\n"
    | Ir_funcs_o funcs_o ->
        List.map (fun f -> com_func_o f print_alloc) funcs_o
        |> String.concat "\n"
  in
  prologue ^ body_asm