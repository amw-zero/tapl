open Arith_ocaml
open Arith_ocaml.Lexer
open Lexing

let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  Printf.fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error lexbuf =
  try Parser.prog Lexer.read lexbuf with
  | SyntaxError msg ->
    Printf.fprintf stderr "%a: %s\n" print_position lexbuf msg;
    None
  | Parser.Error ->
    Printf.fprintf stderr "%a: syntax error\n" print_position lexbuf;
    exit (-1)

let rec parse_and_print lexbuf =
  match parse_with_error lexbuf with
  | Some value ->
    let parsed = Util.print_arith value in
    Printf.printf "Parsed term: %s\n" parsed;

    let result = Core.Arith.bigstep_ex value |> Util.print_arith in
    Printf.printf "Result: %s\n" result;
    
    parse_and_print lexbuf
  | None -> ()

let execute filename () =
  let inx = open_in filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  parse_and_print lexbuf; 
  close_in inx

let () = execute "arithprog.txt" ()
