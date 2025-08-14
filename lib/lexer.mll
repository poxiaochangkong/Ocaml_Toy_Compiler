{
open Parser  
open Lexing  

let reserved = [
  ("int", INT);
  ("void", VOID);
  ("if", IF);
  ("else", ELSE);
  ("while", WHILE);
  ("break", BREAK);
  ("continue", CONTINUE);
  ("return", RETURN);
]


}

let dig = ('0' | ['1'-'9'] ['0'-'9']*)
let nondig = ['a'-'z' 'A'-'Z' '_']
let ident = nondig (nondig | dig)*

let space = [' ' '\t' '\r']

rule token = parse
  | space+    { token lexbuf }  
  | '\n'           { new_line lexbuf; token lexbuf } 
  
  | "//" [^ '\n']* { token lexbuf }  
  | "/*"           { comment lexbuf } 
  
  | ident as id    { 
      try List.assoc id reserved 
      with Not_found -> ID id 
    }
  
  | dig as n   { NUMBER (int_of_string n) }
  
  | "=="   { EQ }
  | "!="   { NEQ }
  | "<="   { LE }
  | ">="   { GE }
  | '<'    { LT }
  | '>'    { GT }
  | "&&"   { LAND }
  | "||"   { LOR }
  | '='    { ASSIGN }
  | '+'    { PLUS }
  | '-'    { MINUS }
  | '*'    { TIMES }
  | '/'    { DIV }
  | '%'    { MOD }
  | '!'    { NOT }
  
  | ';'    { SEMI }
  | ','    { COMMA }
  | '('    { LPAREN }
  | ')'    { RPAREN }
  | '{'    { LBRACE }
  | '}'    { RBRACE }
  
  | eof    { EOF }
  
  | _ as c  {
      let pos = lexbuf.lex_curr_p in
      failwith (Printf.sprintf "Illegal character '%c' at line %d, column %d"
        c pos.pos_lnum (pos.pos_cnum - pos.pos_bol)) }

and comment = parse
  | "*/"   { token lexbuf }     
  | '\n'   { new_line lexbuf; comment lexbuf }
  | _      { comment lexbuf }     
  | eof    { failwith "Unterminated comment" }