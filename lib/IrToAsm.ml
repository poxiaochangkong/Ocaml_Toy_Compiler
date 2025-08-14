open Ir
open Reg

(* --- Module-level State and Configuration --- *)

let stack_frame_size = 1648
let stack_offset = ref 0
let variable_environment = Hashtbl.create 1024
let register_map : (string, string) Hashtbl.t = Hashtbl.create 256
let spilled_variable_map : (operand, int) Hashtbl.t = Hashtbl.create 256

let function_call_register_usage : (string, string list) Hashtbl.t = Hashtbl.create 16
let temporary_register_pool = ref [ "t0"; "t1"; "t2"; "t3"; "t4"; "t5"; "t6" ]

(* --- Helper Functions for Stack and Register Management --- *)

let get_variable_offset var =
  try Hashtbl.find variable_environment var
  with Not_found -> failwith ("Unknown variable in environment: " ^ var)

let allocate_on_stack var =
  try get_variable_offset var
  with _ ->
    stack_offset := !stack_offset + 4;
    Hashtbl.add variable_environment var (- !stack_offset - 4);
    -(!stack_offset + 4)

let operand_to_string = function
  | Reg r | Var r -> Printf.sprintf "%d(sp)" (get_variable_offset r)
  | Imm i -> string_of_int i

let load_operand_to_register (reg : string) (op : operand) : string =
  match op with
  | Imm i -> Printf.sprintf "\tli %s, %d\n" reg i
  | Reg r | Var r ->
      Printf.sprintf "\tlw %s, %d(s0)\n" reg (get_variable_offset r)

let allocate_spilled_slot (op : operand) =
  try Hashtbl.find spilled_variable_map op
  with _ ->
    stack_offset := !stack_offset + 4;
    if !stack_offset >= 1644 then failwith "Stack frame size exceeded during spilling!\n";
    Hashtbl.add spilled_variable_map op (- !stack_offset - 4);
    - !stack_offset - 4

(* --- Instruction Compilation --- *)

let compile_instruction_optimized (reg_alloc_map : string O_hash.t)
    (inst : inst_r) (live_out_set : OperandSet.t) (callee_restore_code : string)
    (needs_frame : bool) : string =
  let temp_regs = ref [ "t5"; "t6"; "t4" ] in
  let temp_reg_map = Hashtbl.create 3 in

  let alloc_temp_reg (v : operand) : string =
    match !temp_regs with
    | [] -> failwith "Ran out of temporary registers for spilling"
    | r :: rest ->
        temp_regs := rest;
        Hashtbl.add temp_reg_map v r;
        r
  in

  let get_dest_register (op : operand) : string * string =
    match op with
    | Imm _ -> failwith "Immediate value cannot be a destination"
    | _ -> (
        match O_hash.find_opt reg_alloc_map op with
        | Some reg when reg <> "__SPILL__" -> ("", reg)
        | _ ->
            let tmp_reg = alloc_temp_reg op in
            let var_name = match op with Var v -> "Var " ^ v | Reg v -> "Reg " ^ v | _ -> "?" in
            let offset, debug_info =
              try
                let op_string = match op with Var x -> x | Reg x -> x | _ -> failwith "" in
                (get_variable_offset op_string, "from_alloc_var")
              with _ -> (allocate_spilled_slot op, "from_spill_var")
            in
            (Printf.sprintf "\tlw %s, %d(s0) # reload %s -- %s\n" tmp_reg offset var_name debug_info, tmp_reg)
      )
  in

  let get_source_register (op : operand) : string * string =
    match op with
    | Imm i ->
        let tmp_reg = alloc_temp_reg op in
        (Printf.sprintf "\tli %s, %d # tmp load imm \n" tmp_reg i, tmp_reg)
    | _ -> (
        match O_hash.find_opt reg_alloc_map op with
        | Some reg when reg <> "__SPILL__" -> ("", reg)
        | _ ->
            let tmp_reg = alloc_temp_reg op in
            let var_name = match op with Var v -> "Var " ^ v | Reg v -> "Reg " ^ v | _ -> "?" in
            let offset, debug_info =
              try
                let op_string = match op with Var x -> x | Reg x -> x | _ -> failwith "" in
                (get_variable_offset op_string, "from_alloc_var")
              with _ -> (allocate_spilled_slot op, "from_spill_var")
            in
            (Printf.sprintf "\tlw %s, %d(s0) # reload %s -- %s\n" tmp_reg offset var_name debug_info, tmp_reg)
      )
  in

  let get_arg_register (op : operand) : string * string =
    match op with
    | Imm _ -> failwith "Immediate value cannot be a destination for arg"
    | _ -> (
        match O_hash.find_opt reg_alloc_map op with
        | Some reg when reg <> "__SPILL__" -> ("", reg)
        | _ ->
            let tmp_reg = "t6" in
            let var_name = match op with Var v -> "Var " ^ v | Reg v -> "Reg " ^ v | _ -> "?" in
            let offset =
              try
                let op_string = match op with Var x -> x | _ -> failwith "" in
                get_variable_offset op_string
              with _ -> allocate_spilled_slot op
            in
            (Printf.sprintf "\tlw %s, %d(s0) # reload %s for arg\n" tmp_reg offset var_name, tmp_reg)
      )
  in
  let generate_return_sequence =
    if needs_frame then
      Printf.sprintf
        "\tlw ra, %d(s0)\n\tlw s0, %d(sp)\n\taddi sp, sp, %d\n\tret\n"
        (get_variable_offset "ra") (stack_frame_size - 4) stack_frame_size
    else "\tret\n"
  in

  let store_dest_value dst dst_reg =
    let get_stack_offset op =
      let op_string = match op with Reg _ | Imm _ -> "" | Var v -> v in
      try Some (get_variable_offset op_string) with _ -> None
    in
    let var_str = match dst with Var v -> "Var " ^ v | Reg v -> "Reg " ^ v | _ -> "Cannot spill imm!" in
    match O_hash.find_opt reg_alloc_map dst with
    | Some "__SPILL__" ->
        let offset = allocate_spilled_slot dst in
        Printf.sprintf "\tsw %s, %d(s0) # save spilled %s\n" dst_reg offset var_str
    | _ -> (
        match get_stack_offset dst with
        | Some offset ->
            Printf.sprintf "\tsw %s, %d(s0) # writeback param %s\n" dst_reg offset var_str
        | None -> "")
  in
  match inst with
  | TailCall (fname, args) ->
      let arg_setup_code =
        List.mapi
          (fun i arg ->
            let load_code, reg = get_arg_register arg in
            if i < 8 then
              load_code ^ Printf.sprintf "\tmv a%d, %s\n" i reg
            else
              let offset = 4 * (i - 8) in
              load_code ^ Printf.sprintf "\tsw %s, %d(s0)\n" reg offset)
          args
        |> String.concat ""
      in
      let entry_label = fname ^ "_entry" in
      arg_setup_code ^ Printf.sprintf "\tj %s\n" entry_label

  | Binop (op, dst, lhs, rhs) ->
      let dst_load, dst_reg = get_dest_register dst in
      let lhs_load, r1 = get_source_register lhs in
      let rhs_load, r2 = get_source_register rhs in
      let op_code =
        match op with
        | "+" -> Printf.sprintf "\tadd %s, %s, %s\n" dst_reg r1 r2
        | "-" -> Printf.sprintf "\tsub %s, %s, %s\n" dst_reg r1 r2
        | "*" -> Printf.sprintf "\tmul %s, %s, %s\n" dst_reg r1 r2
        | "/" -> Printf.sprintf "\tdiv %s, %s, %s\n" dst_reg r1 r2
        | "%" -> Printf.sprintf "\trem %s, %s, %s\n" dst_reg r1 r2
        | "==" -> Printf.sprintf "\tsub %s, %s, %s\n\tseqz %s, %s\n" dst_reg r1 r2 dst_reg dst_reg
        | "!=" -> Printf.sprintf "\tsub %s, %s, %s\n\tsnez %s, %s\n" dst_reg r1 r2 dst_reg dst_reg
        | "<"  -> Printf.sprintf "\tslt %s, %s, %s\n" dst_reg r1 r2
        | ">"  -> Printf.sprintf "\tsgt %s, %s, %s\n" dst_reg r1 r2
        | "<=" -> Printf.sprintf "\tsgt %s, %s, %s\n\txori %s, %s, 1\n" dst_reg r1 r2 dst_reg dst_reg
        | ">=" -> Printf.sprintf "\tslt %s, %s, %s\n\txori %s, %s, 1\n" dst_reg r1 r2 dst_reg dst_reg
        | "&&" -> Printf.sprintf "\tand %s, %s, %s\n" dst_reg r1 r2
        | "||" -> Printf.sprintf "\tor %s, %s, %s\n" dst_reg r1 r2
        | _ -> failwith ("Unknown binop: " ^ op)
      in
      let store_code = store_dest_value dst dst_reg in
      String.concat "" [ lhs_load; rhs_load; dst_load; op_code; store_code ]

  | Unop (op, dst, src) ->
      let dst_load, dst_reg = get_dest_register dst in
      let src_load, src_reg = get_source_register src in
      let body =
        match op with
        | "-" -> Printf.sprintf "\tsub %s, zero, %s\n" dst_reg src_reg
        | "!" -> Printf.sprintf "\tseqz %s, %s\n" dst_reg src_reg
        | "+" -> ""
        | _ -> failwith ("Unknown unop: " ^ op)
      in
      let store_code = store_dest_value dst dst_reg in
      dst_load ^ src_load ^ body ^ store_code

  | Assign (dst, src) ->
      let dst_load, dst_reg = get_dest_register dst in
      (match src with
      | Imm i ->
          let body = Printf.sprintf "\tli %s, %d\n" dst_reg i in
          let store_code = store_dest_value dst dst_reg in
          dst_load ^ body ^ store_code
      | _ ->
          let src_load, src_reg = get_dest_register src in
          let body = Printf.sprintf "\tmv %s, %s\n" dst_reg src_reg in
          let store_code = store_dest_value dst dst_reg in
          dst_load ^ src_load ^ body ^ store_code)

  | Load (dst, addr) ->
      let dst_load, dst_reg = get_dest_register dst in
      let addr_load, addr_reg = get_dest_register addr in
      let body = Printf.sprintf "\tlw %s, 0(%s)\n" dst_reg addr_reg in
      let store_code = store_dest_value dst dst_reg in
      dst_load ^ addr_load ^ body ^ store_code

  | Store (addr, value) ->
      let addr_load, addr_reg = get_dest_register addr in
      let val_load, val_reg = get_dest_register value in
      addr_load ^ val_load ^ Printf.sprintf "\tsw %s, 0(%s)\n" val_reg addr_reg

  | Call (dst, fname, args) ->
      let used_by_callee =
        match Hashtbl.find_opt function_call_register_usage fname with
        | Some regs -> regs
        | None -> []
      in
      let to_save = ref [] in
      OperandSet.iter
        (fun op ->
          match O_hash.find_opt reg_alloc_map op with
          | Some reg when reg <> "__SPILL__" && List.mem reg used_by_callee ->
              let offset = allocate_spilled_slot op in
              to_save := (op, reg, offset) :: !to_save
          | _ -> ())
        live_out_set;

      let save_code =
        List.map
          (fun (op, reg, offset) ->
            let var_str = match op with Var v -> v | Reg v -> v | Imm i -> string_of_int i in
            Printf.sprintf "\tsw %s, %d(s0)  # save caller-saved %s\n" reg offset var_str)
          !to_save
        |> String.concat ""
      in
      let restore_code =
        List.map
          (fun (op, reg, offset) ->
            let var_str = match op with Var v -> v | Reg v -> v | Imm i -> string_of_int i in
            Printf.sprintf "\tlw %s, %d(s0)  # restore caller-saved %s\n" reg offset var_str)
          !to_save
        |> String.concat ""
      in
      let temp_reg_for_return = alloc_temp_reg (Var "__temp_moved") in
      let move_return_to_temp = Printf.sprintf "\tmv %s, a0 # move a0 to temp_reg\n" temp_reg_for_return in
      let _, dst_reg = get_dest_register dst in
      let move_return_to_dest =
        Printf.sprintf "\tmv %s, %s  # move return value from temp_reg\n" dst_reg temp_reg_for_return
        ^ store_dest_value dst dst_reg
      in
      let arg_regs = [| "a0"; "a1"; "a2"; "a3"; "a4"; "a5"; "a6"; "a7" |] in
      let args_setup_code =
        List.mapi
          (fun i arg ->
            match arg with
            | Imm n when i < 8 -> Printf.sprintf "\tli %s, %d\n" arg_regs.(i) n
            | _ when i < 8 ->
                let load, reg = get_arg_register arg in
                load ^ Printf.sprintf "\tmv %s, %s\n" arg_regs.(i) reg
            | Imm n ->
                let off = 4 * (i - 8) in
                Printf.sprintf "\tli t6, %d\n\tsw t6, %d(sp)\n" n off
            | _ ->
                let off = 4 * (i - 8) in
                let load, reg = get_arg_register arg in
                load ^ Printf.sprintf "\tsw %s, %d(sp)\n" reg off)
          args
        |> String.concat ""
      in
      save_code ^ args_setup_code
      ^ Printf.sprintf "\tcall %s\n" fname
      ^ move_return_to_temp
      ^ restore_code
      ^ move_return_to_dest

  | IfGoto (cond, label) -> (
      match cond with
      | Imm 0 -> ""
      | Imm _ -> Printf.sprintf "\tj %s\n" label
      | _ ->
          let cond_load, cond_reg = get_dest_register cond in
          cond_load ^ Printf.sprintf "\tbnez %s, %s\n" cond_reg label)

  | Goto label -> Printf.sprintf "\tj %s\n" label
  | Label label -> Printf.sprintf "%s:\n" label
  | Ret None -> callee_restore_code ^ generate_return_sequence
  | Ret (Some op) ->
      (match op with
      | Imm i -> Printf.sprintf "\tli a0, %d\n" i
      | _ ->
          let ret_load, ret_reg = get_dest_register op in
          let mv_code = if ret_reg = "a0" then "" else Printf.sprintf "\tmv a0, %s\n" ret_reg in
          ret_load ^ mv_code)
      ^ callee_restore_code ^ generate_return_sequence

let compile_instruction_legacy (inst : inst_r) (needs_frame : bool) : string =
  match inst with
  | Binop (op, dst, lhs, rhs) ->
      let dst_off = allocate_on_stack (match dst with Reg r | Var r -> r | _ -> failwith "Bad dst") in
      let lhs_code = load_operand_to_register "t1" lhs in
      let rhs_code = load_operand_to_register "t2" rhs in
      let op_code =
        match op with
        | "+" -> "\tadd t0, t1, t2\n" | "-" -> "\tsub t0, t1, t2\n" | "*" -> "\tmul t0, t1, t2\n"
        | "/" -> "\tdiv t0, t1, t2\n" | "%" -> "\trem t0, t1, t2\n"
        | "==" -> "\tsub t0, t1, t2\n\tseqz t0, t0\n" | "!=" -> "\tsub t0, t1, t2\n\tsnez t0, t0\n"
        | "<=" -> "\tsgt t0, t1, t2\n\txori t0, t0, 1\n" | ">=" -> "\tslt t0, t1, t2\n\txori t0, t0, 1\n"
        | "<" -> "\tslt t0, t1, t2\n" | ">" -> "\tsgt t0, t1, t2\n"
        | "&&" -> "\tand t0, t1, t2\n" | "||" -> "\tor t0, t1, t2\n"
        | _ -> failwith ("Unknown binop: " ^ op)
      in
      lhs_code ^ rhs_code ^ op_code ^ Printf.sprintf "\tsw t0, %d(s0)\n" dst_off
  | Unop (op, dst, src) ->
      let dst_off = allocate_on_stack (match dst with Reg r | Var r -> r | _ -> failwith "Bad dst") in
      let load_src = load_operand_to_register "t1" src in
      let op_code =
        match op with
        | "-" -> "\tneg t0, t1\n" | "!" -> "\tseqz t0, t1\n" | "+" -> "\tmv t0, t1\n"
        | _ -> failwith ("Unknown unop: " ^ op)
      in
      load_src ^ op_code ^ Printf.sprintf "\tsw t0, %d(s0)\n" dst_off
  | Assign (dst, src) ->
      let dst_off = allocate_on_stack (match dst with Reg r | Var r -> r | _ -> failwith "Bad dst") in
      let load_src = load_operand_to_register "t0" src in
      load_src ^ Printf.sprintf "\tsw t0, %d(s0)\n" dst_off
  | Load (dst, src) ->
      let dst_off = allocate_on_stack (match dst with Reg r | Var r -> r | _ -> failwith "Bad dst") in
      let src_code = load_operand_to_register "t1" src in
      src_code ^ "\tlw t0, 0(t1)\n" ^ Printf.sprintf "\tsw t0, %d(s0)\n" dst_off
  | Store (dst, src) ->
      let dst_code = load_operand_to_register "t1" dst in
      let src_code = load_operand_to_register "t2" src in
      dst_code ^ src_code ^ "\tsw t2, 0(t1)\n"
  | Call (dst, fname, args) ->
      let dst_off = allocate_on_stack (match dst with Reg r | Var r -> r | _ -> failwith "Bad dst") in
      let args_code =
        List.mapi
          (fun i arg ->
            if i < 8 then load_operand_to_register (Printf.sprintf "a%d" i) arg
            else
              let offset = 4 * (i - 8) in
              load_operand_to_register "t0" arg ^ Printf.sprintf "\tsw t0, %d(sp)\n" offset)
          args
        |> String.concat ""
      in
      args_code ^ Printf.sprintf "\tcall %s\n\tsw a0, %d(s0)\n" fname dst_off
  | TailCall (fname, args) ->
      let param_stores =
        List.mapi
          (fun i arg ->
            let load = load_operand_to_register "t0" arg in
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
      if needs_frame then
        Printf.sprintf
          "\tlw ra, %d(s0)\n\tlw s0, %d(sp)\n\taddi sp, sp, %d\n\tret\n"
          (get_variable_offset "ra") (stack_frame_size - 4) stack_frame_size
      else "\tret\n"
  | Ret (Some op) ->
      let load_code = load_operand_to_register "a0" op in
      if needs_frame then
        let ra_offset = allocate_on_stack "ra" in
        load_code
        ^ Printf.sprintf
            "\tlw ra, %d(s0)\n\tlw s0, %d(sp)\n\taddi sp, sp, %d\n\tret\n"
            ra_offset (stack_frame_size - 4) stack_frame_size
      else load_code ^ "\tret\n"
  | Goto label -> Printf.sprintf "\tj %s\n" label
  | IfGoto (cond, label) -> (
      match cond with
      | Imm 0 -> ""
      | Imm _ -> Printf.sprintf "\tj %s\n" label
      | _ ->
          let cond_code = load_operand_to_register "t0" cond in
          cond_code ^ Printf.sprintf "\tbne t0, x0, %s\n" label)
  | Label label -> Printf.sprintf "%s:\n" label

let compile_block (blk : block_r) (reg_alloc_map : string O_hash.t)
    (needs_frame : bool) (callee_restore_code : string) : string =
  let code_acc = ref [] in
  let live = ref blk.l_out in

  List.iter
    (fun inst ->
      let def, use = Op.get_def_use_sets_for_instruction inst in
      let l_out = !live in
      let i_code =
        compile_instruction_optimized reg_alloc_map inst l_out callee_restore_code
          needs_frame
      in
      code_acc := i_code :: !code_acc;
      live := OperandSet.union (OperandSet.diff !live def) use)
    (List.rev blk.insts);

  String.concat "" !code_acc

let needs_stack_frame (f : ir_func_o) (reg_alloc_map : string O_hash.t)
    (callee_saved_regs : string list) : bool =
  let calls_other_functions =
    List.exists
      (fun blk ->
        List.exists
          (function Call _ | TailCall _ -> true | _ -> false)
          blk.insts)
      f.blocks
  in
  let has_spilled_vars =
    O_hash.fold
      (fun _ reg acc -> acc || reg = "__SPILL__")
      reg_alloc_map false
  in
  calls_other_functions || has_spilled_vars || callee_saved_regs <> []

let compile_function_legacy (f : func_r) : string =
  Hashtbl.clear variable_environment;
  stack_offset := 0;

  let save_s0 =
    Printf.sprintf "\tsw s0, %d(sp)\n" (stack_frame_size - 4)
  in

  let param_setup =
    List.mapi
      (fun i name ->
        if i >= 8 then
          let off = allocate_on_stack name in
          Printf.sprintf "\tlw t5, %d(s0)\n\tsw t5, %d(s0)\n"
            (4 * (i - 8))
            off
        else
          let off = allocate_on_stack name in
          Printf.sprintf "\tsw a%d, %d(s0)\n" i off)
      f.args
    |> String.concat ""
  in

  let save_ra =
    param_setup ^ Printf.sprintf "\tsw ra, %d(s0)\n" (allocate_on_stack "ra")
  in

  let body_code =
    f.body |> List.map (fun inst -> compile_instruction_legacy inst true) |> String.concat ""
  in

  let body_with_epilogue =
    if not (String.ends_with ~suffix:"\tret\n" body_code) then
      body_code
      ^ Printf.sprintf
          "\tlw ra, %d(s0)\n\tlw s0, %d(sp)\n\taddi sp, sp, %d\n\tret\n"
          (get_variable_offset "ra") (stack_frame_size - 4) stack_frame_size
    else body_code
  in
  let func_label = f.name in
  let prologue =
    Printf.sprintf "%s:\n\taddi sp, sp, -%d\n" func_label stack_frame_size
    ^ save_s0
    ^ Printf.sprintf "\taddi s0, sp, %d\n" stack_frame_size
  in
  prologue ^ save_ra ^ body_with_epilogue


let compile_function_optimized (f : ir_func_o) (print_alloc_details : bool) : string =
  Hashtbl.clear variable_environment;
  Hashtbl.clear register_map;
  Hashtbl.clear spilled_variable_map;
  stack_offset := 0;

  Op.run_liveness_analysis f.blocks print_alloc_details;
  let intervals = build_live_intervals f in
  let reg_alloc_map = run_linear_scan_allocation intervals print_alloc_details in
  let used_caller_saved =
    let caller_saved_regs = [ "t0";"t1";"t2";"t3";"t4";"t5";"t6";"a1";"a2";"a3";"a4";"a5";"a6";"a7" ] in
    O_hash.fold
      (fun _ reg acc ->
        if List.mem reg caller_saved_regs && not (List.mem reg acc) then reg :: acc
        else acc)
      reg_alloc_map []
  in
  let arg_regs = [| "a0"; "a1"; "a2"; "a3"; "a4"; "a5"; "a6"; "a7" |] in
  let param_regs =
    List.mapi (fun i _ -> if i < 8 then arg_regs.(i) else "") f.args
    |> List.filter (fun r -> r <> "")
  in

  let final_used_caller_saved =
    List.fold_left
      (fun acc reg -> if List.mem reg acc then acc else reg :: acc)
      used_caller_saved param_regs
  in
  Hashtbl.replace function_call_register_usage f.name final_used_caller_saved;

  let used_callee_saved =
    let callee_saved_regs = [ "s0";"s1";"s2";"s3";"s4";"s5";"s6";"s7";"s8";"s9";"s10";"s11" ] in
    O_hash.fold
      (fun _ reg acc ->
        if List.mem reg callee_saved_regs && not (List.mem reg acc) then reg :: acc
        else acc)
      reg_alloc_map []
  in

  let needs_frame = needs_stack_frame f reg_alloc_map used_callee_saved in

  let save_callee_regs_code =
    used_callee_saved
    |> List.map (fun reg ->
            let offset = allocate_spilled_slot (Reg reg) in
            Printf.sprintf "\tsw %s, %d(s0)  # save callee-saved\n" reg offset)
    |> String.concat ""
  in

  let restore_callee_regs_code =
    used_callee_saved
    |> List.map (fun reg ->
            let offset = allocate_spilled_slot (Reg reg) in
            Printf.sprintf "\tlw %s, %d(s0)  # restore callee-saved\n" reg offset)
    |> String.concat ""
  in

  let prologue, param_setup_code =
    if needs_frame then
      let save_s0_and_ra =
        Printf.sprintf "\tsw s0, %d(sp)\n" (stack_frame_size - 4)
      in
      let param_setup =
        List.mapi
          (fun i name ->
            if i >= 8 then
              let off = allocate_spilled_slot (Var name) in
              Printf.sprintf "\tlw t5, %d(s0)\n\tsw t5, %d(s0)\n" (4 * (i - 8)) off
            else
              let off = allocate_spilled_slot (Var name) in
              Printf.sprintf "\tsw a%d, %d(s0)\n" i off)
          f.args
        |> String.concat ""
      in
      let full_param_setup =
        param_setup
        ^ Printf.sprintf "\tsw ra, %d(s0)\n" (allocate_on_stack "ra")
        ^ save_callee_regs_code
      in
      let prologue_code =
        Printf.sprintf "%s:\n\taddi sp, sp, -%d\n" f.name stack_frame_size
        ^ save_s0_and_ra
        ^ Printf.sprintf "\taddi s0, sp, %d\n" stack_frame_size
      in
      (prologue_code, full_param_setup)
    else (Printf.sprintf "%s:\n" f.name, "")
  in

  let body_code =
    f.blocks
    |> List.map (fun blk ->
            compile_block blk reg_alloc_map needs_frame restore_callee_regs_code)
    |> String.concat ""
  in

  let epilogue =
    if needs_frame then
      if not (String.ends_with ~suffix:"\tret\n" body_code) then
        restore_callee_regs_code
        ^ Printf.sprintf
            "\tlw ra, %d(s0)\n\tlw s0, %d(sp)\n\taddi sp, sp, %d\n\tret\n"
            (get_variable_offset "ra") (stack_frame_size - 4) stack_frame_size
      else ""
    else if not (String.ends_with ~suffix:"\tret\n" body_code) then "\tret\n"
    else ""
  in

  prologue ^ param_setup_code ^ body_code ^ epilogue

(* The main function to compile the whole IR program to assembly *)
let compile_ir_to_asm (prog : ir_program) (print_alloc_details : bool) : string =
  let prologue = ".text\n .globl main\n" in
  let body_asm =
    match prog with
    | Ir_funcs funcs -> List.map compile_function_legacy funcs |> String.concat "\n"
    | Ir_funcs_o funcs_o ->
        List.map (fun f -> compile_function_optimized f print_alloc_details) funcs_o
        |> String.concat "\n"
  in
  prologue ^ body_asm
