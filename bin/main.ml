open Compilerlib
open Ast

(* 解析程序字符串为 AST *)
let parse_program (s : string) : func_def list =
  let lexbuf = Lexing.from_string s in
  try Parser.comp_unit Lexer.token lexbuf
  with Parsing.Parse_error ->
    let pos = lexbuf.Lexing.lex_curr_p in
    let line = pos.Lexing.pos_lnum in
    let col = pos.Lexing.pos_cnum - pos.Lexing.pos_bol + 1 in
    let token = Lexing.lexeme lexbuf in
    Printf.eprintf "语法错误在行 %d, 列 %d: 未预期的符号 '%s'\n"
      line col token;
    exit 1

let () =
  (* 启用异常回溯信息，便于调试 *)
  Printexc.record_backtrace true;

  (* 从标准输入一次性读取所有内容 *)
  let input_source = In_channel.input_all In_channel.stdin in

  (* 解析命令行参数 *)
  let args = Array.to_list Sys.argv |> List.tl in
  let print_liveness = List.exists (( = ) "-print-live") args in
  let enable_block_ir = List.exists (( = ) "-block-ir") args in
  let enable_optimizations_flag = List.exists (( = ) "-opt") args in
  let print_allocation_details = List.exists (( = ) "-print-alloc") args in
  
  (* 确定是否启用优化 *)
  let optimizations_enabled = enable_block_ir || enable_optimizations_flag in

  (* 执行编译流程 *)
  let ast = parse_program input_source in
  let ir_program = AstToIR.translate_program_to_ir ast optimizations_enabled print_liveness in
  let assembly_code = IrToAsm.compile_ir_to_asm ir_program print_allocation_details in

  (* 将生成的汇编代码打印到标准输出 *)
  Printf.printf "\n\n%s\n" assembly_code;

  (* 将生成的汇编代码写入文件 output.txt *)
  try
    let out_channel = open_out "output.txt" in
    output_string out_channel assembly_code;
    close_out out_channel
  with Sys_error msg ->
    Printf.eprintf "写入 output.txt 时发生错误: %s\n" msg

