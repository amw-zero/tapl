open Core.Arith

let rec print_arith t = match t with
  | ATrue -> "true"
  | AFalse -> "false"
  | AZero -> "zero"
  | AIfElse (t1, t2, t3) -> "ifelse " ^ print_arith t1 ^ " " ^ print_arith t2 ^ " " ^ print_arith t3
  | ASucc _ -> "succ"
  | APred _ -> "pred"
  | AIsZero _ -> "iszero"