{
  open Lexing
  open Parser

  exception SyntaxError of string
}

let true = "true"
let false = "false"

rule read = parse
  | true  { TRUE }
  | false  { FALSE }
  | _     { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
  | eof   { EOF }