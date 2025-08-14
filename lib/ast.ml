(* 基本类型定义 *)
type typ =
  | TInt
  | TVoid 

type binop =
  | Add
  | Sub
  | Mul
  | Div
  | Mod
  | Eq
  | Neq
  | Less
  | Leq
  | Greater
  | Geq
  | Land
  | Lor

type unop = Not | Plus | Minus
type param = string 

type expr =
  | Binop of binop * expr * expr
  | Unop of unop * expr
  | ID of string
  | Number of int
  | Call of string * expr list

type stmt =
  | Block of stmt list 
  | Empty 
  | ExprStmt of expr 
  | Decl of string * expr option 
  | Assign of string * expr 
  | If of expr * stmt * stmt option 
  | While of expr * stmt 
  | Break 
  | Continue 
  | Return of expr option 


type func_def = {
  ret_type : typ;
  func_name : string;
  params : param list ;
  body : stmt list ;
}


type comp_unit = func_def list 

let rec spand = function
  | Binop (Land, x, y) -> spand x @ spand y
  | e -> [e]

let rec spor = function
  | Binop (Lor, x, y) -> spor x @ spor y
  | e -> [e]