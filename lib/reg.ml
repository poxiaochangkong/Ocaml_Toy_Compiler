open Ir

module O_key = struct
  type t = operand

  let equal a b =
    match (a, b) with
    | Var x, Var y -> String.equal x y
    | Reg x, Reg y -> String.equal x y
    | Imm x, Imm y -> x = y
    | _, _ -> false

  let hash = function
    | Var x -> Hashtbl.hash ("var", x)
    | Reg x -> Hashtbl.hash ("reg", x)
    | Imm i -> Hashtbl.hash ("imm", i)
end

module O_hash = Hashtbl.Make (O_key)


let spi_map : (operand, int) Hashtbl.t = Hashtbl.create 32
let stack_count = ref 0

let k_registers = 8 + 4 + 11

let phy_reg =
  [|
    "a0";
    "a1";
    "a2";
    "a3";
    "a4";
    "a5";
    "a6";
    "a7";
    "t0";
    "t1";
    "t2";
    "t3";
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
  |]

  type inter = {
  name : operand;
  mutable start : int;
  mutable end_ : int;
  is_param : bool;
}

let b_inter (f : ir_func_o) : inter list =
  let reg_inters = Hashtbl.create 128 in
  let block_pos = Hashtbl.create 64 in
  let counter = ref 0 in

  List.iter
    (fun block ->
      incr counter;
      Hashtbl.add block_pos block.label !counter)
    f.blocks;

  let par_oper op =
    match op with Var name -> List.mem name f.args | _ -> false
  in

  let add_live v pos =
    let op = v in
    match Hashtbl.find_opt reg_inters op with
    | Some i ->
        i.start <- min i.start pos;
        i.end_ <- max i.end_ pos
    | None ->
        let i =
          { name = op; start = pos; end_ = pos; is_param = par_oper op }
        in
        Hashtbl.add reg_inters op i
  in

  List.iter
    (fun block ->
      let pos = Hashtbl.find block_pos block.label in
      OperandSet.iter (fun v -> add_live v pos) block.l_in;
      OperandSet.iter (fun v -> add_live v pos) block.l_out)
    f.blocks;

  Hashtbl.fold (fun _ itv acc -> itv :: acc) reg_inters []

let print_reg reg_map : unit =
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


let lin_alloca (inters : inter list) (p_alloca : bool) =
  let inters = List.sort (fun a b -> compare a.start b.start) inters in
  let active : inter list ref = ref [] in

  let reg_map = O_hash.create 32 in
  let alloc_map = O_hash.create 512 in

  let exp_inter current =
    active :=
      List.filter
        (fun itv ->
          if itv.end_ >= current.start then true
          else (
            O_hash.remove reg_map itv.name;
            false))
        !active
  in

  List.iter
    (fun itv ->
      exp_inter itv;

      if itv.is_param then (
        O_hash.add reg_map itv.name "__SPILL__";
        O_hash.replace alloc_map itv.name "__SPILL__")
      else if List.length !active = k_registers then (
        (if
           p_alloca
         then
           let name =
             match itv.name with Reg r | Var r -> r | Imm _ -> "imm"
           in
           Printf.printf "Spill: %s\n" name);
        O_hash.add reg_map itv.name "__SPILL__";
        O_hash.replace alloc_map itv.name "__SPILL__")
      else
        let used_regs =
          O_hash.fold (fun _ r acc -> r :: acc) reg_map []
        in
        let avail =
          List.find
            (fun r -> not (List.mem r used_regs))
            (Array.to_list phy_reg)
        in
        O_hash.add reg_map itv.name avail;
        O_hash.replace alloc_map itv.name avail;
        active := itv :: !active)
    inters;
  if p_alloca then print_reg alloc_map;
  alloc_map
