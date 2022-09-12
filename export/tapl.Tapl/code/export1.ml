module Arith : sig
  type nat = Zero_nat | Suc of nat
end = struct

type nat = Zero_nat | Suc of nat;;

end;; (*struct Arith*)

module Tapl : sig
  type tapl_bool
  val bevalf : Arith.nat -> tapl_bool -> tapl_bool
end = struct

type tapl_bool = TTrue | FFalse | IfElse of tapl_bool * tapl_bool * tapl_bool;;

let rec beval1f
  = function IfElse (TTrue, t2, t3) -> t2
    | IfElse (FFalse, t2, t3) -> t3
    | IfElse (IfElse (v, va, vb), t2, t3) ->
        IfElse (beval1f (IfElse (v, va, vb)), t2, t3)
    | TTrue -> TTrue
    | FFalse -> FFalse;;

let rec bevalf
  x0 t = match x0, t with Arith.Zero_nat, t -> t
    | Arith.Suc v, TTrue -> TTrue
    | Arith.Suc v, FFalse -> FFalse
    | Arith.Suc fuel, IfElse (v, va, vb) ->
        bevalf fuel (beval1f (IfElse (v, va, vb)));;

let print_tapl_bool t = match t with TTrue -> "true"
  | FFalse -> "false"
  | IfElse (t1, t2, t3) -> "ifelse";;

let program = IfElse (TTrue, IfElse (FFalse, TTrue, FFalse), FFalse);;

print_tapl_bool program |> print_endline;

bevalf (Suc (Suc Zero_nat)) program |> print_tapl_bool |> print_endline;;

end;; (*struct Tapl*)
