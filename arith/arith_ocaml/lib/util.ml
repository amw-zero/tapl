open Core.Arith

let print_arith t = match t with
  | ATrue -> "true"
  | AFalse -> "false"
  | AZero -> "zero"
  | AIfElse (_, _, _) -> "ifelse"
  | ASucc _ -> "succ"
  | APred _ -> "pred"
  | AIsZero _ -> "iszero"