open Ir

(* Helper function to convert an operand to a string for printing. *)
let string_of_operand op =
  match op with
  | Var v -> v
  | Reg r -> r
  | Imm i -> string_of_int i

(* Prints the liveness analysis results for all blocks for debugging. *)
let print_liveness_info blocks =
  List.iter
    (fun blk ->
      Printf.printf "Block: %s\n" blk.label;
      Printf.printf "  live_in: {%s}\n"
        (String.concat ", " (List.map string_of_operand (OperandSet.elements blk.l_in)));
      Printf.printf "  live_out: {%s}\n"
        (String.concat ", " (List.map string_of_operand (OperandSet.elements blk.l_out))))
    blocks

(* Determines the set of variables defined (DEF) and used (USE) by a block's terminator. *)
let get_def_use_sets_for_terminator = function
  | TermRet (Some op) ->
      (OperandSet.empty, (match op with Imm _ -> OperandSet.empty | _ -> OperandSet.singleton op))
  | TermRet None -> (OperandSet.empty, OperandSet.empty)
  | TermIf (cond, _, _) ->
      (OperandSet.empty, (match cond with Imm _ -> OperandSet.empty | _ -> OperandSet.singleton cond))
  | TermGoto _ | TermSeq _ -> (OperandSet.empty, OperandSet.empty)

(* Determines the set of variables defined (DEF) and used (USE) by a single instruction. *)
let get_def_use_sets_for_instruction (inst : inst_r) : OperandSet.t * OperandSet.t =
  let operand_to_set op = match op with Imm _ -> OperandSet.empty | _ -> OperandSet.singleton op in
  let args_to_set args =
    List.fold_left
      (fun acc op -> match op with Imm _ -> acc | _ -> OperandSet.add op acc)
      OperandSet.empty args
  in
  match inst with
  | Binop (_, dst, lhs, rhs) ->
      (OperandSet.singleton dst, OperandSet.union (operand_to_set lhs) (operand_to_set rhs))
  | Unop (_, dst, src) | Assign (dst, src) | Load (dst, src) ->
      (OperandSet.singleton dst, operand_to_set src)
  | Store (dst, src) ->
      (OperandSet.empty, OperandSet.union (operand_to_set dst) (operand_to_set src))
  | Call (dst, _, args) ->
      let def = (match dst with Imm _ -> OperandSet.empty | _ -> OperandSet.singleton dst) in
      (def, args_to_set args)
  | TailCall (_, args) -> (OperandSet.empty, args_to_set args)
  | Ret (Some op) -> (OperandSet.empty, operand_to_set op)
  | IfGoto (cond, _) -> (OperandSet.empty, operand_to_set cond)
  | Ret None | Goto _ | Label _ -> (OperandSet.empty, OperandSet.empty)

(* Aggregates the DEF and USE sets for an entire basic block. *)
let get_def_use_sets_for_block (blk : block_r) : OperandSet.t * OperandSet.t =
  let defs, uses =
    List.fold_right
      (fun inst (current_defs, current_uses) ->
        let def, use = get_def_use_sets_for_instruction inst in
        let new_uses = OperandSet.union use current_uses in
        let new_defs = OperandSet.union def current_defs in
        (new_defs, new_uses))
      blk.insts
      (OperandSet.empty, OperandSet.empty)
  in
  let term_def, term_use = get_def_use_sets_for_terminator blk.terminator in
  let final_use = OperandSet.union term_use uses in
  let final_def = OperandSet.union defs term_def in
  (final_def, final_use)

(*
 * Runs iterative backward liveness analysis on the CFG.
 * A variable is "live" at a point if its value may be read later in the execution.
 * The data-flow equations are:
 * OUT[B] = U_{S in SUCC[B]} IN[S]
 * IN[B]  = USE[B] U (OUT[B] - DEF[B])
 * We iterate until a fixed point is reached (i.e., no sets change).
*)
let run_liveness_analysis (blocks : block_r list) (print_results : bool) : unit =
  let changed = ref true in
  (* Initialize IN and OUT sets for all blocks to empty. *)
  List.iter
    (fun blk ->
      blk.l_in <- OperandSet.empty;
      blk.l_out <- OperandSet.empty)
    blocks;

  while !changed do
    changed := false;
    List.iter
      (fun blk ->
        (* Calculate OUT[B] by uniting the IN sets of all successors. *)
        let new_out =
          List.fold_left
            (fun acc successor_label ->
              match List.find_opt (fun b -> b.label = successor_label) blocks with
              | Some succ -> OperandSet.union acc succ.l_in
              | None -> acc)
            OperandSet.empty blk.succs
        in
        let def, use = get_def_use_sets_for_block blk in
        (* Calculate IN[B] using the data-flow equation. *)
        let new_in = OperandSet.union use (OperandSet.diff new_out def) in

        (* If any set has changed, we need to continue iterating. *)
        if not (OperandSet.equal blk.l_in new_in) || not (OperandSet.equal blk.l_out new_out)
        then changed := true;

        blk.l_in <- new_in;
        blk.l_out <- new_out)
      blocks
  done;

  if print_results then print_liveness_info blocks
