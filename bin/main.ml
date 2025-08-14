open Compilerlib
open Ast

(* "parse_program" 是一个清晰的函数名，无需改动。 *)
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

let () =
  Printexc.record_backtrace true;

  let read_input () =
    let rec aux acc =
      try
        let line = input_line stdin in
        aux (line :: acc)
      with End_of_file -> String.concat "\n" (List.rev acc)
    in
    aux []
  in
  let args = Array.to_list Sys.argv |> List.tl in
  
  (* 为了更清晰，重命名了用于解析命令行参数的变量 *)
  let print_liveness = List.exists (( = ) "-print-live") args in
  let enable_block_ir = List.exists (( = ) "-block-ir") args in
  let enable_optimizations_flag = List.exists (( = ) "-opt") args in
  let print_allocation_details = List.exists (( = ) "-print-alloc") args in
  
  (* 逻辑保持不变，但变量名更清晰地表达了其用途 *)
  let optimizations_enabled = enable_block_ir || enable_optimizations_flag in

  let input_source = read_input () in

  let ast = parse_program input_source in

  (* 重命名函数调用，使其更易于理解 *)
  let ir_program = AstToIR.translate_program_to_ir ast optimizations_enabled print_liveness in

  let assembly_code = IrToAsm.compile_ir_to_asm ir_program print_allocation_details in

  (* 保持打印到标准输出流 *)
  Printf.printf "\n\n%s\n" assembly_code;

  (* --- 新增代码开始 (最小化修改) --- *)
  (* 将同样的内容写入 output.txt *)
  try
    let out_channel = open_out "output.txt" in
    output_string out_channel assembly_code;
    close_out out_channel
  with Sys_error msg ->
    Printf.eprintf "Error writing to output.txt: %s\n" msg
  (* --- 新增代码结束 --- *)

