(* lib/cfg.ml *)
open Ir

module S_set = Set.Make(String)
module S_map = Map.Make(String)

type const_state = int option;;
type const_env = const_state S_map.t;;

let w_mod n =
    let m = Int32.of_int n in
    Int32.to_int (Int32.logand m 0xFFFFFFFFl)
;;

let e_oper env op =
  match op with
  | Var name | Reg name ->
      (try match S_map.find name env with
       | Some i -> Imm i
       | None -> op
       with Not_found -> op)
  | Imm _ -> op
;;

let b_cfg (blocks : block_r list) : block_r list =
  if blocks = [] then [] else
  let label_map =
    List.fold_left (fun m b -> S_map.add b.label b m) S_map.empty blocks
  in
  List.iter (fun b -> b.preds <- []; b.succs <- []) blocks;
  List.iter (fun b ->
    let add_edge from_lbl to_lbl =
      match S_map.find_opt to_lbl label_map with
      | Some succ ->
          b.succs <- to_lbl :: b.succs;
          succ.preds <- from_lbl :: succ.preds
      | None -> ()
    in
    match b.terminator with
    | TermGoto l         -> add_edge b.label l
    | TermSeq l          -> add_edge b.label l
    | TermIf (_, l1, l2) -> add_edge b.label l1; add_edge b.label l2
    | TermRet _          -> ()
  ) blocks;
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
  let reachable = List.filter (fun b -> Hashtbl.mem visited b.label) blocks in
  let reach_set = List.fold_left (fun s b -> S_map.add b.label () s) S_map.empty reachable in
  List.iter (fun b ->
    b.succs <- List.filter (fun l -> S_map.mem l reach_set) b.succs;
    b.preds <- List.filter (fun l -> S_map.mem l reach_set) b.preds
  ) reachable;
  reachable
;;

let m_envs (envs : const_env list) : const_env =
  if envs = [] then S_map.empty
  else
    let all_vars = List.fold_left (fun acc env ->
        S_map.fold (fun k _ acc -> S_set.add k acc) env acc
      ) S_set.empty envs in
    S_set.fold (fun var acc ->
        let states = List.map (fun env ->
            try S_map.find var env with Not_found -> None
          ) envs in
        let is_same = match states with
          | [] -> true
          | hd::tl -> List.for_all ((=) hd) tl
        in
        if is_same then
          S_map.add var (List.hd states) acc
        else
          S_map.add var None acc
      ) all_vars S_map.empty
;;

let e_binop op op1 op2 =
  match (op1, op2) with
  | (Imm a, Imm b) ->
  (match op with
   | "+" -> Some (w_mod (a + b))
   | "-" -> Some (w_mod (a - b))
   | "*" -> Some (w_mod (a * b))
   | "/" when b <> 0 -> Some (w_mod (a / b))
   | "%" when b <> 0 -> Some (w_mod (a mod b))
   | "==" -> Some (if a = b then 1 else 0)
   | "!=" -> Some (if a <> b then 1 else 0)
   | "<" -> Some (if a < b then 1 else 0)
   | "<=" -> Some (if a <= b then 1 else 0)
   | ">" -> Some (if a > b then 1 else 0)
   | ">=" -> Some (if a >= b then 1 else 0)
   | _ -> None)
  | _ -> None
;;

let eval_unop op op1 =
  match op1 with
  | Imm a ->
  (match op with
   | "!" -> Some (if a = 0 then 1 else 0)
   | "-" -> Some (w_mod (-a))
   | "+" -> Some (w_mod a)
   | _ -> None)
  | _ -> None
;;

let p_inst env inst =
  match inst with
  | TailCall _ ->
      inst, env
  | Assign (dst, src) ->
      let src' = e_oper env src in
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
      let src1' = e_oper env src1 in
      let src2' = e_oper env src2 in
      (match e_binop op src1' src2' with
       | Some i -> Assign (dst, Imm i), S_map.add (match dst with Var v | Reg v -> v | _ -> "") (Some i) env
       | None -> Binop (op, dst, src1', src2'), S_map.add (match dst with Var v | Reg v -> v | _ -> "") None env)

  | Unop (op, dst, src) ->
      let src' = e_oper env src in
      (match eval_unop op src' with
       | Some i -> Assign (dst, Imm i), S_map.add (match dst with Var v | Reg v -> v | _ -> "") (Some i) env
       | None -> Unop (op, dst, src'), S_map.add (match dst with Var v | Reg v -> v | _ -> "") None env)

  | Call (dst, fname, args) ->
      let args' = List.map (e_oper env) args in
      let env' = match dst with Var v | Reg v -> S_map.add v None env | _ -> env in
      Call (dst, fname, args'), env'

  | Load (dst, addr) ->
      let addr' = e_oper env addr in
      let env' = match dst with Var v | Reg v -> S_map.add v None env | _ -> env in
      Load (dst, addr'), env'

  | Store (addr, value) ->
      let addr' = e_oper env addr in
      let value' = e_oper env value in
      Store (addr', value'), env

  | IfGoto (cond, label) ->
      IfGoto (e_oper env cond, label), env

  | Ret op_opt ->
      Ret (Option.map (e_oper env) op_opt), env

  | Goto _ | Label _ as t -> t, env
;;

let termina env term =
  match term with
  | TermIf (cond, l1, l2) -> TermIf (e_oper env cond, l1, l2)
  | TermRet o -> TermRet (Option.map (e_oper env) o)
  | TermGoto _ | TermSeq _ as t -> t
;;

let const_pro (blocks : block_r list) : block_r list =
  let b_map = List.fold_left (fun m b -> S_map.add b.label b m) S_map.empty blocks in
  let i_envs = ref S_map.empty in
  let o_envs = ref S_map.empty in
  List.iter (fun b ->
    i_envs := S_map.add b.label S_map.empty !i_envs;
    o_envs := S_map.add b.label S_map.empty !o_envs
  ) blocks;
  let worklist = Queue.create () in
  List.iter (fun b -> Queue.add b.label worklist) blocks;
  while not (Queue.is_empty worklist) do
    let label = Queue.take worklist in
    let blk = S_map.find label b_map in
    let preds = blk.preds in
    let in_env =
      if preds = [] then S_map.empty
      else m_envs (List.map (fun p -> S_map.find p !o_envs) preds)
    in
    i_envs := S_map.add label in_env !i_envs;
    let new_insts, out_env = List.fold_left (fun (acc, env) inst ->
      let inst', env' = p_inst env inst in
      acc @ [inst'], env'
    ) ([], in_env) blk.insts in
    let new_term = termina out_env blk.terminator in
    let old_out = S_map.find label !o_envs in
    if not (S_map.equal (=) out_env old_out) then begin
      o_envs := S_map.add label out_env !o_envs;
      List.iter (fun succ -> Queue.add succ worklist) blk.succs
    end;
    blk.insts <- new_insts;
    blk.terminator <- new_term;
  done;
  blocks
;;

let opt blocks =
  blocks |> b_cfg |> const_pro
;;