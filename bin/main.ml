open Compilerlib
open Ast

(* parse_program 和 read_input 函数保持不变 *)
let parse_program (s : string) : func_def list =
  let lexbuf = Lexing.from_string s in
  try Parser.comp_unit Lexer.token lexbuf
  with Parsing.Parse_error ->
    let pos = lexbuf.Lexing.lex_curr_p in
    let line = pos.Lexing.pos_lnum in
    let col = pos.Lexing.pos_cnum - pos.Lexing.pos_bol + 1 in
    let token = Lexing.lexeme lexbuf in
    Printf.eprintf "Syntax error at line %d, column %d: unexpected token '%s'\n"
      line col token;
    exit 1

let read_input () =
  let rec aux acc =
    try
      let line = input_line stdin in
      aux (line :: acc)
    with End_of_file -> String.concat "\n" (List.rev acc)
  in
  aux []

let () =
  Printexc.record_backtrace true;

  (* 1. 使用 ref 定义需要被命令行设置的变量 *)
  let print_liveness = ref false in
  let bl_ir = ref false in
  let opt_flag = ref false in
  let print_alloc = ref false in

  (* 2. 定义参数规格列表 *)
  let speclist = [
    ("-print-live", Arg.Set print_liveness, "Print liveness analysis results");
    ("-block-ir", Arg.Set bl_ir, "Enable block-based IR generation");
    ("-opt", Arg.Set opt_flag, "Enable optimizations (implies -block-ir)");
    ("-print-alloc", Arg.Set print_alloc, "Print register allocation details");
  ] in

  (* 3. 定义使用说明 *)
  let usage_msg = "Usage: toyc [options] < source.tc" in

  (* 4. 执行解析 *)
  Arg.parse speclist (fun _ -> ()) usage_msg;

  (* 5. 根据解析结果设置最终的标志 *)
  let optimize_enabled = !bl_ir || !opt_flag in
  
  (* 编译流程保持不变 *)
  let input = read_input () in
  let ast = parse_program input in
  let ir = AstToIR.pro_ir ast optimize_enabled !print_liveness in
  let asm = IrToAsm.com_pro ir !print_alloc in
  Printf.printf "\n\n%s\n" asm