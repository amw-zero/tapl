{
  open Lexing
  open Parser

  exception SyntaxError of string
}

let whitespace = [' ' '\t']

rule read = parse
  | [' ' '\t' '\r']+   { read lexbuf }
  | "true"            { TRUE }
  | "false"           { FALSE }
  | "if"              { IF }
  | "then"            { THEN }
  | "else"            { ELSE }
  | _                 { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
  
  | eof               { EOF }