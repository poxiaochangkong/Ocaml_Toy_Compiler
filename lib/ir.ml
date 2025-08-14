
type operand =
  | Reg of string 
  | Imm of int 
  | Var of string

module OperandSet = Set.Make (struct
  type t = operand
  let compare = compare
end)


type inst_r =
  | Binop of string * operand * operand * operand 
  | Unop of string * operand * operand 
  | Load of operand * operand 
  | Store of operand * operand 
  | Goto of string 
  | IfGoto of operand * string 
  | Label of string 
  | Call of operand * string * operand list
  | TailCall of string * operand list 
  | Ret of operand option 
  | Assign of operand * operand 

  type term_r =
  | TermGoto of string
  | TermIf of operand * string * string
  | TermRet of operand option
  | TermSeq of string

  type block_r = {
  label : string;
  mutable insts : inst_r list;
  mutable terminator : term_r;
  mutable preds : string list;
  mutable succs : string list;
  mutable l_in : OperandSet.t;
  mutable l_out : OperandSet.t;
}
type func_r = { name : string; args : string list; body : inst_r list }


type ir_func_o = { name : string; args : string list; blocks : block_r list }
type ir_program = Ir_funcs of func_r list | Ir_funcs_o of ir_func_o list
