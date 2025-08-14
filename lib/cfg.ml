(* lib/cfg.ml *)
open Ir

module S_set = Set.Make(String)
module S_map = Map.Make(String)

(* Represents the state of a variable during constant propagation: either a known integer or unknown (None). *)
type const_state = int option;;
type const_env = const_state S_map.t;;

(* Helper to ensure integer operations wrap around correctly for 32-bit architecture. *)
let wrap_int32 n =
    let m = Int32.of_int n in
    Int32.to_int (Int32.logand m 0xFFFFFFFFl)
;;

(* Tries to resolve an operand to a constant value using the current environment. *)
let evaluate_operand env op =
  match op with
  | Var name | Reg name ->
      (try match S_map.find name env with
       | Some i -> Imm i
       | None -> op
       with Not_found -> op)
  | Imm _ -> op
;;

(* Constructs the Control Flow Graph (CFG) from a list of basic blocks. *)
let build_cfg (blocks : block_r list) : block_r list =
  if blocks = [] then [] else
  let label_map =
    List.fold_left (fun m b -> S_map.add b.label b m) S_map.empty blocks
  in
  (* Initialize predecessors and successors *)
  List.iter (fun b -> b.preds <- []; b.succs <- []) blocks;
  (* Add edges based on terminators *)
  List.iter (fun b ->
    let add_edge from_lbl to_lbl =
      match S_map.find_opt to_lbl label_map with
      | Some succ ->
          b.succs <- to_lbl :: b.succs;
          succ.preds <- from_lbl :: succ.preds
      | None -> () (* Edge to a non-existent block, might be cleaned up later *)
    in
    match b.terminator with
    | TermGoto l         -> add_edge b.label l
    | TermSeq l          -> add_edge b.label l
    | TermIf (_, l1, l2) -> add_edge b.label l1; add_edge b.label l2
    | TermRet _          -> ()
  ) blocks;
  (* Remove unreachable blocks using DFS from the entry point *)
  let entry_label = (List.hd blocks).label in
  let visited = Hashtbl.create (List.length blocks) in
  let rec dfs lbl =
    if not (Hashtbl.mem visited lbl) then begin
      Hashtbl.add visited lbl ();
      match S_map.find_opt lbl label_map with
      | Some blk -> List.iter dfs blk.succs
      | None     -> ()
    end
  in
  dfs entry_label;
  let reachable_blocks = List.filter (fun b -> Hashtbl.mem visited b.label) blocks in
  let reachable_set = List.fold_left (fun s b -> S_map.add b.label () s) S_map.empty reachable_blocks in
  (* Clean up edges pointing to now-removed blocks *)
  List.iter (fun b ->
    b.succs <- List.filter (fun l -> S_map.mem l reachable_set) b.succs;
    b.preds <- List.filter (fun l -> S_map.mem l reachable_set) b.preds
  ) reachable_blocks;
  reachable_blocks
;;

(* Merges multiple constant environments from predecessor blocks. *)
let merge_environments (envs : const_env list) : const_env =
  if envs = [] then S_map.empty
  else
    let all_vars = List.fold_left (fun acc env ->
        S_map.fold (fun k _ acc -> S_set.add k acc) env acc
      ) S_set.empty envs in
    S_set.fold (fun var acc ->
        let states = List.map (fun env ->
            try S_map.find var env with Not_found -> None
          ) envs in
        let first_state = List.hd states in
        let all_same = List.for_all ((=) first_state) (List.tl states) in
        if all_same then
          S_map.add var first_state acc
        else
          S_map.add var None acc (* If values differ, variable is not constant *)
      ) all_vars S_map.empty
;;

(* Performs constant folding for binary operations. *)
let fold_constant_binop op op1 op2 =
  match (op1, op2) with
  | (Imm a, Imm b) ->
  (match op with
   | "+" -> Some (wrap_int32 (a + b))
   | "-" -> Some (wrap_int32 (a - b))
   | "*" -> Some (wrap_int32 (a * b))
   | "/" when b <> 0 -> Some (wrap_int32 (a / b))
   | "%" when b <> 0 -> Some (wrap_int32 (a mod b))
   | "==" -> Some (if a = b then 1 else 0)
   | "!=" -> Some (if a <> b then 1 else 0)
   | "<" -> Some (if a < b then 1 else 0)
   | "<=" -> Some (if a <= b then 1 else 0)
   | ">" -> Some (if a > b then 1 else 0)
   | ">=" -> Some (if a >= b then 1 else 0)
   | _ -> None)
  | _ -> None
;;

(* Performs constant folding for unary operations. *)
let fold_constant_unop op op1 =
  match op1 with
  | Imm a ->
  (match op with
   | "!" -> Some (if a = 0 then 1 else 0)
   | "-" -> Some (wrap_int32 (-a))
   | "+" -> Some (wrap_int32 a)
   | _ -> None)
  | _ -> None
;;

(* Propagates constants through a single instruction, returning the new instruction and updated environment. *)
let propagate_through_instruction env inst =
  match inst with
  | TailCall _ ->
      inst, env
  | Assign (dst, src) ->
      let src' = evaluate_operand env src in
      let env' =
        match dst with
        | Var name | Reg name ->
            (match src' with
             | Imm i -> S_map.add name (Some i) env
             | _ -> S_map.add name None env)
        | _ -> env
      in
      Assign (dst, src'), env'

  | Binop (op, dst, src1, src2) ->
      let src1' = evaluate_operand env src1 in
      let src2' = evaluate_operand env src2 in
      (match fold_constant_binop op src1' src2' with
       | Some i -> Assign (dst, Imm i), S_map.add (match dst with Var v | Reg v -> v | _ -> "") (Some i) env
       | None -> Binop (op, dst, src1', src2'), S_map.add (match dst with Var v | Reg v -> v | _ -> "") None env)

  | Unop (op, dst, src) ->
      let src' = evaluate_operand env src in
      (match fold_constant_unop op src' with
       | Some i -> Assign (dst, Imm i), S_map.add (match dst with Var v | Reg v -> v | _ -> "") (Some i) env
       | None -> Unop (op, dst, src'), S_map.add (match dst with Var v | Reg v -> v | _ -> "") None env)

  | Call (dst, fname, args) ->
      let args' = List.map (evaluate_operand env) args in
      let env' = match dst with Var v | Reg v -> S_map.add v None env | _ -> env in
      Call (dst, fname, args'), env'

  | Load (dst, addr) ->
      let addr' = evaluate_operand env addr in
      let env' = match dst with Var v | Reg v -> S_map.add v None env | _ -> env in
      Load (dst, addr'), env'

  | Store (addr, value) ->
      let addr' = evaluate_operand env addr in
      let value' = evaluate_operand env value in
      Store (addr', value'), env

  | IfGoto (cond, label) ->
      IfGoto (evaluate_operand env cond, label), env

  | Ret op_opt ->
      Ret (Option.map (evaluate_operand env) op_opt), env

  | Goto _ | Label _ as t -> t, env
;;

(* Propagates constants through a block's terminator. *)
let propagate_through_terminator env term =
  match term with
  | TermIf (cond, l1, l2) -> TermIf (evaluate_operand env cond, l1, l2)
  | TermRet o -> TermRet (Option.map (evaluate_operand env) o)
  | TermGoto _ | TermSeq _ as t -> t
;;

(* Runs the constant propagation optimization pass on a list of blocks. *)
let run_constant_propagation (blocks : block_r list) : block_r list =
  let block_map = List.fold_left (fun m b -> S_map.add b.label b m) S_map.empty blocks in
  let in_envs = ref S_map.empty in
  let out_envs = ref S_map.empty in
  (* Initialize environments for all blocks *)
  List.iter (fun b ->
    in_envs := S_map.add b.label S_map.empty !in_envs;
    out_envs := S_map.add b.label S_map.empty !out_envs
  ) blocks;
  (* Use a worklist to repeatedly process blocks until no changes occur *)
  let worklist = Queue.create () in
  List.iter (fun b -> Queue.add b.label worklist) blocks;
  while not (Queue.is_empty worklist) do
    let label = Queue.take worklist in
    let blk = S_map.find label block_map in
    let preds = blk.preds in
    (* Merge environments from all predecessors *)
    let in_env =
      if preds = [] then S_map.empty
      else merge_environments (List.map (fun p -> S_map.find p !out_envs) preds)
    in
    in_envs := S_map.add label in_env !in_envs;
    (* Propagate constants through the block's instructions *)
    let new_insts, out_env = List.fold_left (fun (acc_insts, current_env) inst ->
      let inst', env' = propagate_through_instruction current_env inst in
      acc_insts @ [inst'], env'
    ) ([], in_env) blk.insts in
    let new_term = propagate_through_terminator out_env blk.terminator in
    let old_out_env = S_map.find label !out_envs in
    (* If the output environment has changed, re-add successors to the worklist *)
    if not (S_map.equal (=) out_env old_out_env) then begin
      out_envs := S_map.add label out_env !out_envs;
      List.iter (fun succ -> Queue.add succ worklist) blk.succs
    end;
    blk.insts <- new_insts;
    blk.terminator <- new_term;
  done;
  blocks
;;

(* Main entry point for optimizing a CFG. *)
let optimize_cfg blocks =
  blocks |> build_cfg |> run_constant_propagation
;;
