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

end;; (*struct Tapl*)
