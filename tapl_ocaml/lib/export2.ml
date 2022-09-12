module HOL : sig
  type 'a equal = {equal : 'a -> 'a -> bool}
  val equal : 'a equal -> 'a -> 'a -> bool
  val eq : 'a equal -> 'a -> 'a -> bool
end = struct

type 'a equal = {equal : 'a -> 'a -> bool};;
let equal _A = _A.equal;;

let rec eq _A a b = equal _A a b;;

end;; (*struct HOL*)

module Predicate : sig
  type 'a seq
  type 'a pred
  val the : 'a HOL.equal -> 'a pred -> 'a
  val bind : 'a pred -> ('a -> 'b pred) -> 'b pred
  val bot_pred : 'a pred
  val single : 'a -> 'a pred
  val sup_pred : 'a pred -> 'a pred -> 'a pred
end = struct

type 'a seq = Empty | Insert of 'a * 'a pred | Join of 'a pred * 'a seq
and 'a pred = Seq of (unit -> 'a seq);;

let rec is_empty (Seq f) = null (f ())
and null = function Empty -> true
           | Insert (x, p) -> false
           | Join (p, xq) -> is_empty p && null xq;;

let rec singleton _A
  default (Seq f) =
    (match f () with Empty -> default ()
      | Insert (x, p) ->
        (if is_empty p then x
          else (let y = singleton _A default p in
                 (if HOL.eq _A x y then x else default ())))
      | Join (p, xq) ->
        (if is_empty p then the_only _A default xq
          else (if null xq then singleton _A default p
                 else (let x = singleton _A default p in
                       let y = the_only _A default xq in
                        (if HOL.eq _A x y then x else default ())))))
and the_only _A
  default x1 = match default, x1 with default, Empty -> default ()
    | default, Insert (x, p) ->
        (if is_empty p then x
          else (let y = singleton _A default p in
                 (if HOL.eq _A x y then x else default ())))
    | default, Join (p, xq) ->
        (if is_empty p then the_only _A default xq
          else (if null xq then singleton _A default p
                 else (let x = singleton _A default p in
                       let y = the_only _A default xq in
                        (if HOL.eq _A x y then x else default ()))));;

let rec the _A
  a = singleton _A (fun _ -> failwith "not_unique" (fun _ -> the _A a)) a;;

let rec bind (Seq g) f = Seq (fun _ -> apply f (g ()))
and apply f x1 = match f, x1 with f, Empty -> Empty
            | f, Insert (x, p) -> Join (f x, Join (bind p f, Empty))
            | f, Join (p, xq) -> Join (bind p f, apply f xq);;

let bot_pred : 'a pred = Seq (fun _ -> Empty);;

let rec single x = Seq (fun _ -> Insert (x, bot_pred));;

let rec adjunct p x1 = match p, x1 with p, Empty -> Join (p, Empty)
                  | p, Insert (x, q) -> Insert (x, sup_pred q p)
                  | p, Join (q, xq) -> Join (q, adjunct p xq)
and sup_pred
  (Seq f) (Seq g) =
    Seq (fun _ ->
          (match f () with Empty -> g ()
            | Insert (x, p) -> Insert (x, sup_pred p (Seq g))
            | Join (p, xq) -> adjunct (Seq g) (Join (p, xq))));;

end;; (*struct Predicate*)

module Tapl : sig
  type tapl_bool
  val beval_ex : tapl_bool -> tapl_bool
end = struct

type tapl_bool = TTrue | FFalse | IfElse of tapl_bool * tapl_bool * tapl_bool;;

let rec equal_tapl_boola
  x0 x1 = match x0, x1 with FFalse, IfElse (x31, x32, x33) -> false
    | IfElse (x31, x32, x33), FFalse -> false
    | TTrue, IfElse (x31, x32, x33) -> false
    | IfElse (x31, x32, x33), TTrue -> false
    | TTrue, FFalse -> false
    | FFalse, TTrue -> false
    | IfElse (x31, x32, x33), IfElse (y31, y32, y33) ->
        equal_tapl_boola x31 y31 &&
          (equal_tapl_boola x32 y32 && equal_tapl_boola x33 y33)
    | FFalse, FFalse -> true
    | TTrue, TTrue -> true;;

let equal_tapl_bool = ({HOL.equal = equal_tapl_boola} : tapl_bool HOL.equal);;

let rec beval1_i_o
  x = Predicate.sup_pred
        (Predicate.bind (Predicate.single x)
          (fun a ->
            (match a with TTrue -> Predicate.bot_pred
              | FFalse -> Predicate.bot_pred
              | IfElse (TTrue, t2, _) -> Predicate.single t2
              | IfElse (FFalse, _, _) -> Predicate.bot_pred
              | IfElse (IfElse (_, _, _), _, _) -> Predicate.bot_pred)))
        (Predicate.sup_pred
          (Predicate.bind (Predicate.single x)
            (fun a ->
              (match a with TTrue -> Predicate.bot_pred
                | FFalse -> Predicate.bot_pred
                | IfElse (TTrue, _, _) -> Predicate.bot_pred
                | IfElse (FFalse, _, t3) -> Predicate.single t3
                | IfElse (IfElse (_, _, _), _, _) -> Predicate.bot_pred)))
          (Predicate.bind (Predicate.single x)
            (fun a ->
              (match a with TTrue -> Predicate.bot_pred
                | FFalse -> Predicate.bot_pred
                | IfElse (t1, t2, t3) ->
                  Predicate.bind (beval1_i_o t1)
                    (fun xa -> Predicate.single (IfElse (xa, t2, t3)))))));;

let rec beval
  x = Predicate.sup_pred
        (Predicate.bind (Predicate.single x)
          (fun xa -> Predicate.bind (beval1_i_o xa) Predicate.single))
        (Predicate.sup_pred
          (Predicate.bind (Predicate.single x) Predicate.single)
          (Predicate.bind (Predicate.single x)
            (fun xa ->
              Predicate.bind (beval xa)
                (fun xb -> Predicate.bind (beval xb) Predicate.single))));;

let rec beval_ex t = Predicate.the equal_tapl_bool (beval t);;

end;; (*struct Tapl*)
