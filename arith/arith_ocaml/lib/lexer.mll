{
  open Lexing
  open Parser

  exception SyntaxError of string
}

let whitespace = [' ' '\t' '\r' '\n']

rule read = parse
  | whitespace+       { read lexbuf }
  | "true"            { TRUE }
  | "false"           { FALSE }
  | "0"               { ZERO }
  | "if"              { IF }
  | "then"            { THEN }
  | "else"            { ELSE }
  | "succ"            { SUCC }
  | "pred"            { PRED }
  | "iszero"          { ISZERO }
  | '('               { LPAREN }
  | ')'               { RPAREN }
  | _                 { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
  | eof               { EOF }