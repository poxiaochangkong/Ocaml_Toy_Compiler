open Ir

(* A custom hash table for operands, allowing Var, Reg, and Imm to be used as keys. *)
module O_key = struct
  type t = operand
  let equal a b =
    match (a, b) with
    | Var x, Var y | Reg x, Reg y -> String.equal x y
    | Imm x, Imm y -> x = y
    | _, _ -> false
  let hash = function
    | Var x -> Hashtbl.hash ("var", x)
    | Reg x -> Hashtbl.hash ("reg", x)
    | Imm i -> Hashtbl.hash ("imm", i)
end
module O_hash = Hashtbl.Make (O_key)

(* The set of available physical registers for allocation. *)
let physical_registers =
  [| "a0"; "a1"; "a2"; "a3"; "a4"; "a5"; "a6"; "a7";
     "t0"; "t1"; "t2"; "t3";
     "s1"; "s2"; "s3"; "s4"; "s5"; "s6"; "s7"; "s8"; "s9"; "s10"; "s11" |]
let number_of_physical_registers = Array.length physical_registers

(* Represents the live interval of a variable (operand). *)
type live_interval = {
  name : operand;
  mutable start_point : int;
  mutable end_point : int;
  is_parameter : bool;
}

(* Step 1: Build live intervals for all variables from liveness analysis data. *)
let build_live_intervals (f : ir_func_o) : live_interval list =
  let intervals_map = Hashtbl.create 128 in
  let block_positions = Hashtbl.create 64 in
  let counter = ref 0 in

  (* Assign a unique position to each block for interval calculation. *)
  List.iter
    (fun block ->
      incr counter;
      Hashtbl.add block_positions block.label !counter)
    f.blocks;

  let is_function_parameter op =
    match op with Var name -> List.mem name f.args | _ -> false
  in

  (* Update or create a live interval for a variable at a given position. *)
  let update_interval var pos =
    match Hashtbl.find_opt intervals_map var with
    | Some interval ->
        interval.start_point <- min interval.start_point pos;
        interval.end_point <- max interval.end_point pos
    | None ->
        let interval =
          { name = var; start_point = pos; end_point = pos; is_parameter = is_function_parameter var }
        in
        Hashtbl.add intervals_map var interval
  in

  (* Iterate through all blocks and their live-in/live-out sets to build intervals. *)
  List.iter
    (fun block ->
      let pos = Hashtbl.find block_positions block.label in
      OperandSet.iter (fun v -> update_interval v pos) block.l_in;
      OperandSet.iter (fun v -> update_interval v pos) block.l_out)
    f.blocks;

  Hashtbl.fold (fun _ interval acc -> interval :: acc) intervals_map []

(* Helper to print the result of register allocation for debugging. *)
let print_allocation_result reg_map : unit =
  Printf.printf "=== Register Allocation Result ===\n";
  O_hash.iter
    (fun op reg ->
      let name =
        match op with
        | Reg r -> Printf.sprintf "Reg %s" r
        | Var v -> Printf.sprintf "Var %s" v
        | Imm i -> Printf.sprintf "Imm %d" i
      in
      Printf.printf "%-10s -> %s\n" name reg)
    reg_map

(* Step 2: Run the linear scan register allocation algorithm. *)
let run_linear_scan_allocation (intervals : live_interval list) (print_details : bool) =
  (* Sort intervals by their starting point. *)
  let sorted_intervals = List.sort (fun a b -> compare a.start_point b.start_point) intervals in
  let active_intervals : live_interval list ref = ref [] in

  let assigned_registers = O_hash.create 32 in
  let final_allocation_map = O_hash.create 512 in

  (* Expire old intervals from the active list that no longer overlap with the current one. *)
  let expire_old_intervals current =
    active_intervals :=
      List.filter
        (fun itv ->
          if itv.end_point >= current.start_point then true
          else (
            (* This interval has ended, so its register is now free. *)
            O_hash.remove assigned_registers itv.name;
            false))
        !active_intervals
  in

  List.iter
    (fun current_interval ->
      expire_old_intervals current_interval;

      if current_interval.is_parameter then (
        (* Parameters passed on the stack are marked for spilling immediately. *)
        O_hash.add assigned_registers current_interval.name "__SPILL__";
        O_hash.replace final_allocation_map current_interval.name "__SPILL__")
      else if List.length !active_intervals = number_of_physical_registers then (
        (* No free registers, must spill. *)
        if print_details then
           let name = match current_interval.name with Reg r | Var r -> r | Imm _ -> "imm" in
           Printf.printf "Spilling variable: %s\n" name;
        O_hash.add assigned_registers current_interval.name "__SPILL__";
        O_hash.replace final_allocation_map current_interval.name "__SPILL__")
      else
        (* Find an available physical register. *)
        let used_regs = O_hash.fold (fun _ r acc -> r :: acc) assigned_registers [] in
        let available_reg =
          List.find
            (fun r -> not (List.mem r used_regs))
            (Array.to_list physical_registers)
        in
        O_hash.add assigned_registers current_interval.name available_reg;
        O_hash.replace final_allocation_map current_interval.name available_reg;
        active_intervals := current_interval :: !active_intervals)
    sorted_intervals;

  if print_details then print_allocation_result final_allocation_map;
  final_allocation_map
