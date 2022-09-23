open Lexing
open Parser

let evaluate expr =
  let lexbuf = Lexing.from_string expr in
  match Parser.prog Lexer.read lexbuf with
  | Some value ->
    let parsed = Util.print_arith value in
    Printf.printf "Parsed term: %s\n" parsed;
  | None -> ()

let () = evaluate "if (if true then false else true) then true else (if true then false else true)"; ()