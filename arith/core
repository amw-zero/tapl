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
  val if_pred : bool -> unit pred
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

let rec if_pred b = (if b then single () else bot_pred);;

end;; (*struct Predicate*)

module Arith : sig
  type arith = ATrue | AFalse | AZero | AIfElse of arith * arith * arith |
    ASucc of arith | APred of arith | AIsZero of arith
  val bigstep_ex : arith -> arith
end = struct

type arith = ATrue | AFalse | AZero | AIfElse of arith * arith * arith |
  ASucc of arith | APred of arith | AIsZero of arith;;

let rec equal_aritha
  x0 x1 = match x0, x1 with APred x6, AIsZero x7 -> false
    | AIsZero x7, APred x6 -> false
    | ASucc x5, AIsZero x7 -> false
    | AIsZero x7, ASucc x5 -> false
    | ASucc x5, APred x6 -> false
    | APred x6, ASucc x5 -> false
    | AIfElse (x41, x42, x43), AIsZero x7 -> false
    | AIsZero x7, AIfElse (x41, x42, x43) -> false
    | AIfElse (x41, x42, x43), APred x6 -> false
    | APred x6, AIfElse (x41, x42, x43) -> false
    | AIfElse (x41, x42, x43), ASucc x5 -> false
    | ASucc x5, AIfElse (x41, x42, x43) -> false
    | AZero, AIsZero x7 -> false
    | AIsZero x7, AZero -> false
    | AZero, APred x6 -> false
    | APred x6, AZero -> false
    | AZero, ASucc x5 -> false
    | ASucc x5, AZero -> false
    | AZero, AIfElse (x41, x42, x43) -> false
    | AIfElse (x41, x42, x43), AZero -> false
    | AFalse, AIsZero x7 -> false
    | AIsZero x7, AFalse -> false
    | AFalse, APred x6 -> false
    | APred x6, AFalse -> false
    | AFalse, ASucc x5 -> false
    | ASucc x5, AFalse -> false
    | AFalse, AIfElse (x41, x42, x43) -> false
    | AIfElse (x41, x42, x43), AFalse -> false
    | AFalse, AZero -> false
    | AZero, AFalse -> false
    | ATrue, AIsZero x7 -> false
    | AIsZero x7, ATrue -> false
    | ATrue, APred x6 -> false
    | APred x6, ATrue -> false
    | ATrue, ASucc x5 -> false
    | ASucc x5, ATrue -> false
    | ATrue, AIfElse (x41, x42, x43) -> false
    | AIfElse (x41, x42, x43), ATrue -> false
    | ATrue, AZero -> false
    | AZero, ATrue -> false
    | ATrue, AFalse -> false
    | AFalse, ATrue -> false
    | AIsZero x7, AIsZero y7 -> equal_aritha x7 y7
    | APred x6, APred y6 -> equal_aritha x6 y6
    | ASucc x5, ASucc y5 -> equal_aritha x5 y5
    | AIfElse (x41, x42, x43), AIfElse (y41, y42, y43) ->
        equal_aritha x41 y41 && (equal_aritha x42 y42 && equal_aritha x43 y43)
    | AZero, AZero -> true
    | AFalse, AFalse -> true
    | ATrue, ATrue -> true;;

let equal_arith = ({HOL.equal = equal_aritha} : arith HOL.equal);;

let rec is_value_arith
  t = (match t with ATrue -> true | AFalse -> true | AZero -> true
        | AIfElse (_, _, _) -> false | ASucc _ -> true | APred _ -> false
        | AIsZero _ -> false);;

let rec is_numeric
  t = (match t with ATrue -> false | AFalse -> false | AZero -> true
        | AIfElse (_, _, _) -> false | ASucc _ -> true | APred _ -> false
        | AIsZero _ -> false);;

let rec bigstep
  x = Predicate.sup_pred
        (Predicate.bind (Predicate.single x)
          (fun xa ->
            Predicate.bind (Predicate.if_pred (is_value_arith xa))
              (fun () -> Predicate.single xa)))
        (Predicate.sup_pred
          (Predicate.bind (Predicate.single x)
            (fun a ->
              (match a with ATrue -> Predicate.bot_pred
                | AFalse -> Predicate.bot_pred | AZero -> Predicate.bot_pred
                | AIfElse (t1, t2, _) ->
                  Predicate.bind (bigstep t1)
                    (fun aa ->
                      (match aa
                        with ATrue ->
                          Predicate.bind (bigstep t2) Predicate.single
                        | AFalse -> Predicate.bot_pred
                        | AZero -> Predicate.bot_pred
                        | AIfElse (_, _, _) -> Predicate.bot_pred
                        | ASucc _ -> Predicate.bot_pred
                        | APred _ -> Predicate.bot_pred
                        | AIsZero _ -> Predicate.bot_pred))
                | ASucc _ -> Predicate.bot_pred | APred _ -> Predicate.bot_pred
                | AIsZero _ -> Predicate.bot_pred)))
          (Predicate.sup_pred
            (Predicate.bind (Predicate.single x)
              (fun a ->
                (match a with ATrue -> Predicate.bot_pred
                  | AFalse -> Predicate.bot_pred | AZero -> Predicate.bot_pred
                  | AIfElse (t1, _, t3) ->
                    Predicate.bind (bigstep t1)
                      (fun aa ->
                        (match aa with ATrue -> Predicate.bot_pred
                          | AFalse ->
                            Predicate.bind (bigstep t3) Predicate.single
                          | AZero -> Predicate.bot_pred
                          | AIfElse (_, _, _) -> Predicate.bot_pred
                          | ASucc _ -> Predicate.bot_pred
                          | APred _ -> Predicate.bot_pred
                          | AIsZero _ -> Predicate.bot_pred))
                  | ASucc _ -> Predicate.bot_pred
                  | APred _ -> Predicate.bot_pred
                  | AIsZero _ -> Predicate.bot_pred)))
            (Predicate.sup_pred
              (Predicate.bind (Predicate.single x)
                (fun a ->
                  (match a with ATrue -> Predicate.bot_pred
                    | AFalse -> Predicate.bot_pred | AZero -> Predicate.bot_pred
                    | AIfElse (_, _, _) -> Predicate.bot_pred
                    | ASucc t ->
                      Predicate.bind (bigstep t)
                        (fun xa ->
                          Predicate.bind (Predicate.if_pred (is_numeric xa))
                            (fun () -> Predicate.single (ASucc xa)))
                    | APred _ -> Predicate.bot_pred
                    | AIsZero _ -> Predicate.bot_pred)))
              (Predicate.sup_pred
                (Predicate.bind (Predicate.single x)
                  (fun a ->
                    (match a with ATrue -> Predicate.bot_pred
                      | AFalse -> Predicate.bot_pred
                      | AZero -> Predicate.bot_pred
                      | AIfElse (_, _, _) -> Predicate.bot_pred
                      | ASucc _ -> Predicate.bot_pred
                      | APred t ->
                        Predicate.bind (bigstep t)
                          (fun aa ->
                            (match aa with ATrue -> Predicate.bot_pred
                              | AFalse -> Predicate.bot_pred
                              | AZero -> Predicate.single AZero
                              | AIfElse (_, _, _) -> Predicate.bot_pred
                              | ASucc _ -> Predicate.bot_pred
                              | APred _ -> Predicate.bot_pred
                              | AIsZero _ -> Predicate.bot_pred))
                      | AIsZero _ -> Predicate.bot_pred)))
                (Predicate.sup_pred
                  (Predicate.bind (Predicate.single x)
                    (fun a ->
                      (match a with ATrue -> Predicate.bot_pred
                        | AFalse -> Predicate.bot_pred
                        | AZero -> Predicate.bot_pred
                        | AIfElse (_, _, _) -> Predicate.bot_pred
                        | ASucc _ -> Predicate.bot_pred
                        | APred t ->
                          Predicate.bind (bigstep t)
                            (fun aa ->
                              (match aa with ATrue -> Predicate.bot_pred
                                | AFalse -> Predicate.bot_pred
                                | AZero -> Predicate.bot_pred
                                | AIfElse (_, _, _) -> Predicate.bot_pred
                                | ASucc v ->
                                  Predicate.bind
                                    (Predicate.if_pred (is_numeric v))
                                    (fun () -> Predicate.single v)
                                | APred _ -> Predicate.bot_pred
                                | AIsZero _ -> Predicate.bot_pred))
                        | AIsZero _ -> Predicate.bot_pred)))
                  (Predicate.sup_pred
                    (Predicate.bind (Predicate.single x)
                      (fun a ->
                        (match a with ATrue -> Predicate.bot_pred
                          | AFalse -> Predicate.bot_pred
                          | AZero -> Predicate.bot_pred
                          | AIfElse (_, _, _) -> Predicate.bot_pred
                          | ASucc _ -> Predicate.bot_pred
                          | APred _ -> Predicate.bot_pred
                          | AIsZero t ->
                            Predicate.bind (bigstep t)
                              (fun aa ->
                                (match aa with ATrue -> Predicate.bot_pred
                                  | AFalse -> Predicate.bot_pred
                                  | AZero -> Predicate.single ATrue
                                  | AIfElse (_, _, _) -> Predicate.bot_pred
                                  | ASucc _ -> Predicate.bot_pred
                                  | APred _ -> Predicate.bot_pred
                                  | AIsZero _ -> Predicate.bot_pred)))))
                    (Predicate.bind (Predicate.single x)
                      (fun a ->
                        (match a with ATrue -> Predicate.bot_pred
                          | AFalse -> Predicate.bot_pred
                          | AZero -> Predicate.bot_pred
                          | AIfElse (_, _, _) -> Predicate.bot_pred
                          | ASucc _ -> Predicate.bot_pred
                          | APred _ -> Predicate.bot_pred
                          | AIsZero t ->
                            Predicate.bind (bigstep t)
                              (fun aa ->
                                (match aa with ATrue -> Predicate.bot_pred
                                  | AFalse -> Predicate.bot_pred
                                  | AZero -> Predicate.bot_pred
                                  | AIfElse (_, _, _) -> Predicate.bot_pred
                                  | ASucc v ->
                                    Predicate.bind
                                      (Predicate.if_pred (is_numeric v))
                                      (fun () -> Predicate.single AFalse)
                                  | APred _ -> Predicate.bot_pred
                                  | AIsZero _ -> Predicate.bot_pred)))))))))));;

let rec bigstep_ex t = Predicate.the equal_arith (bigstep t);;

end;; (*struct Arith*)
