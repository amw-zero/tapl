theory Tapl

imports Main

begin

datatype tapl_term = 
  true | 
  false | 
  zero | 
  If tapl_term tapl_term tapl_term |
  suc tapl_term |
  pred  tapl_term |
  iszero tapl_term

section "Recursive function definition of S"

fun terms :: "nat \<Rightarrow> tapl_term set" where
"terms 0 = {}" |
"terms (Suc n) = 
  {true, false, zero} 
  \<union> {suc t | t. t \<in> terms n} \<union> {pred t | t. t \<in> terms n} \<union> {iszero t | t. t \<in> terms n}
  \<union> {If t1 t2 t3 | t1 t2 t3. let termsn = terms n in t1 \<in> termsn \<and> t2 \<in> termsn \<and> t3 \<in> termsn}"


theorem terms_cumulative_apply: "terms n \<subseteq> terms (n + 1)"
  apply(induction n)
   apply(auto)
    apply(simp_all add: Let_def)
    apply(blast+)
  done

(*
theorem terms_cumulative: "terms n \<subseteq> terms (n + 1)"
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  have "t \<in> terms (Suc n) \<Longrightarrow> t \<in> terms (Suc (Suc n))" for t
  proof(induction t)
      case (suc t)
      then show ?case
      proof(induction n)
        case 0
        then show ?case by auto
      next
        case (Suc n)
        then show ?case sorry
      qed
    next
      case (If t1 t2 t3)
      then show ?case
      proof(induction n)
        case 0
        then show ?case by auto
      next
        case (Suc n)
        then show ?case by auto
      qed
    next   
      case (pred t)
      then show ?case
      proof(induction n)
        case 0
        then show ?case by auto
      next
        case (Suc n)
        then show ?case by auto
      qed
    next
      case (iszero t)
      then show ?case
      proof(induction n)
        case 0
        then show ?case by auto
      next
        case (Suc n)
        then show ?case by auto
      qed
    qed auto
  then show ?case
    by blast
qed
*)

theorem terms_cumulative_isar: "terms n \<subseteq> terms (n + 1)"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
    apply(auto)
      apply(simp_all add: Let_def)
      apply(blast+)
    done
qed

section "Inductive definition of S"

inductive_set terms_is :: "tapl_term set" where
 t: "true: terms_is" |
 f: "false: terms_is" |
 z: "zero: terms_is" | 
 i: "If tapl_term tapl_term tapl_term: terms_is" |
 s: "suc t: terms_is" |
 p: "pred t: terms_is" |
 iz: "iszero t: terms_is"

theorem "terms_is = (\<Union>n. terms n)"
  oops

section "Boolean expressions"

datatype tapl_bool =
  TTrue | 
  FFalse | 
  IfElse tapl_bool tapl_bool tapl_bool

(*
inductive is_value_b :: "tapl_bool \<Rightarrow> bool" where
is_value_true: "is_value_b TTrue" |
is_value_false: "is_value_b FFalse"
*)

definition is_value_bd :: "tapl_bool \<Rightarrow> bool" where
"is_value_bd t = (case t of TTrue \<Rightarrow> True | FFalse \<Rightarrow> True | _ \<Rightarrow> False)"

inductive beval1 :: "tapl_bool \<Rightarrow> tapl_bool \<Rightarrow> bool" where
beval1_if_true: "beval1 (IfElse TTrue t2 t3) t2" |
beval1_if_false: "beval1 (IfElse FFalse t2 t3) t3" |
beval1_if: "beval1 t1 t1' \<Longrightarrow> beval1 (IfElse t1 t2 t3) (IfElse t1' t2 t3)"

fun beval1f :: "tapl_bool \<Rightarrow> tapl_bool" where
"beval1f (IfElse TTrue t2 t3) = t2" |
"beval1f (IfElse FFalse t2 t3) = t3" |
"beval1f (IfElse t1 t2 t3) = (IfElse (beval1f t1) t2 t3)" |
"beval1f t = t"

fun bevalf :: "nat \<Rightarrow> tapl_bool \<Rightarrow> tapl_bool" where
"bevalf 0 t = t" | 
"bevalf _ TTrue = TTrue" |
"bevalf _ FFalse = FFalse" |
"bevalf (Suc fuel) t = bevalf fuel (beval1f t)"

theorem beval1f_determinacy: "\<lbrakk>beval1f t = t'; beval1f t = t''\<rbrakk> \<Longrightarrow> t' = t''"
proof(induction t)
  case TTrue
  then show ?case by simp
next
  case FFalse
  then show ?case by simp
next
  case (IfElse t1 t2 t3)
  then show ?case by simp
qed

export_code bevalf in OCaml

code_pred beval1 .

(*export_code beval1 in OCaml*)

definition "nested_if =
  (IfElse (IfElse TTrue FFalse TTrue) TTrue FFalse)"

values "{t. beval1 (IfElse FFalse TTrue FFalse) t}"

values "{t. beval1 nested_if t}"

values "{t. beval1 TTrue t}"

(* Using Sledgehammer *)
theorem beval1_determinacy:
  "\<lbrakk> beval1 t t'; beval1 t t''\<rbrakk> \<Longrightarrow> t' = t''"
proof (induction t t' arbitrary: t'' rule: beval1.induct)
  case (beval1_if_true t2 t3)
  then show ?case by (auto elim: beval1.cases)
next
  case (beval1_if_false t2 t3)
  then show ?case by (auto elim: beval1.cases)
next
  case (beval1_if t1 t1' t2 t3)
  then show ?case
    (* found with sledgehammer *)
    by (smt (verit, del_insts) beval1.simps tapl_bool.distinct(4) tapl_bool.distinct(6) tapl_bool.inject)
qed

section "Normal form"

definition is_normal :: "tapl_bool \<Rightarrow> bool" where
"is_normal b \<equiv> \<forall>t. \<not>(beval1 b t)"

theorem "is_value_bd t \<Longrightarrow> is_normal t"
  by (auto simp: is_normal_def is_value_bd_def elim: beval1.cases)

theorem "is_normal t \<Longrightarrow> is_value_bd t"
  unfolding is_normal_def
  unfolding is_value_bd_def
proof (induction t)
  case TTrue
  then show ?case by simp
next
  case FFalse
  then show ?case by simp
next
  case (IfElse t1 t2 t3)
  then show ?case
    (* Found with sledgehammer *)
    by (metis beval1_if beval1_if_false beval1_if_true tapl_bool.exhaust tapl_bool.simps(10))
qed

(* Contraposative of is_normal t \<Longrightarrow> is_value_b t. 
  Tricky part is, showing the TTrue and FFalse cases leads to a contradiction becauset
  they are values. Don't know how to leave them out of the proof though, since they are
  part of the datatype
theorem "\<not>is_value_b t \<Longrightarrow> \<not>is_normal t"
proof (induction t)
  case TTrue
  then show ?case 
next
  case FFalse
  then show ?case sorry
next
  case (IfElse t1 t2 t3)
  then show ?case sorry
qed
*)

inductive beval :: "tapl_bool \<Rightarrow> tapl_bool \<Rightarrow> bool" where
once: "beval1 t t' \<Longrightarrow> beval t t'" |
reflexive: "beval t t" |
transitive: "beval t t' \<Longrightarrow> beval t' t'' \<Longrightarrow> beval t t''"

(* Same logic of evaluation with less rules. Easier for proving *)
inductive beval_better :: "tapl_bool \<Rightarrow> tapl_bool \<Rightarrow> bool" where
reflexive: "beval_better t t" |
step: "beval1 t t' \<Longrightarrow> beval_better t' t'' \<Longrightarrow> beval_better t t''"

code_pred (modes: i => o => bool as beval') beval . 

definition "beval_ex t = Predicate.the (beval' t)"

export_code beval_ex in OCaml

(*
theorem "beval t t' \<Longrightarrow> is_normal t' \<Longrightarrow> is_normal t'' \<Longrightarrow>  beval t t'' \<Longrightarrow> t' = t''"
proof (induction t t' rule: beval.induct)
  case (once t t')
  then show ?case
    apply(metis is_normal_def beval1_determinacy)
next
  case (reflexive t)
  then show ?case sorry
next
  case (transitive t t' t'')
  then show ?case sorry
qed
*)

section "Introduction of 'funny' evaluation rules"

inductive beval1_funny :: "tapl_bool \<Rightarrow> tapl_bool \<Rightarrow> bool" where
beval1_if_true: "beval1_funny (IfElse TTrue t2 t3) t2" |
beval1_if_false: "beval1_funny (IfElse FFalse t2 t3) t3" |
beval1_if: "beval1_funny t1 t1' \<Longrightarrow> beval1_funny (IfElse t1 t2 t3) (IfElse t1' t2 t3)" |
beval1_funny: "beval1_funny (IfElse TTrue t2 t3) t3"


code_pred beval1_funny .

(* Nondeterministic evaluation *)
values "{t. beval1_funny (IfElse TTrue TTrue FFalse) t}"

theorem beval1_funny_determinacy:
  "beval1_funny t t' \<Longrightarrow> beval1_funny t t'' \<Longrightarrow> t' = t''"
  quickcheck
  oops


definition is_normal_funny :: "tapl_bool \<Rightarrow> bool" where
"is_normal_funny b \<equiv> \<forall>t. \<not>(beval1_funny b t)"

theorem "is_normal_funny t \<Longrightarrow> is_value_bd t"
  unfolding is_normal_funny_def
  unfolding is_value_bd_def
proof (induction t)
  case TTrue
  then show ?case by simp
next
  case FFalse
  then show ?case by simp
next
  case (IfElse t1 t2 t3)
  then show ?case
    (* Found with sledgehammer *)
    by (metis beval1_if beval1_if_false beval1_if_true tapl_bool.exhaust tapl_bool.simps(10))
qed

inductive beval2_funny :: "tapl_bool \<Rightarrow> tapl_bool \<Rightarrow> bool" where
beval1_if_true: "beval2_funny (IfElse TTrue t2 t3) t2" |
beval1_if_false: "beval2_funny (IfElse FFalse t2 t3) t3" |
beval1_if: "beval2_funny t1 t1' \<Longrightarrow> beval2_funny (IfElse t1 t2 t3) (IfElse t1' t2 t3)" |
beval1_funny: "beval2_funny t2 t2' \<Longrightarrow> beval2_funny (IfElse t1 t2 t3) (IfElse t1 t2' t3)"

values "{t. beval1_funny (IfElse TTrue TTrue FFalse) t}"

section "Arithmetic Expressions"

datatype tapl_arith = 
  TTrue | 
  FFalse | 
  Zero |
  IfElse tapl_arith tapl_arith tapl_arith |
  Succ tapl_arith |
  Pred  tapl_arith |
  IsZero tapl_arith

definition is_numeric :: "tapl_arith \<Rightarrow> bool" where
"is_numeric t = 
  (case t of 
    Zero \<Rightarrow> True |
    Succ _ \<Rightarrow> True |
    _ \<Rightarrow> False)" 

definition "is_value_arith" :: "tapl_arith \<Rightarrow> bool" where
"is_value_arith t =
  (case t of 
    TTrue \<Rightarrow> True |
    FFalse \<Rightarrow> True |
    Zero \<Rightarrow> True |
    Succ _ \<Rightarrow> True |
    _ \<Rightarrow> False)"

inductive aeval1 :: "tapl_arith \<Rightarrow> tapl_arith \<Rightarrow> bool" where
(* Bool evaluation *)
aeval1_if_true: "aeval1 (IfElse TTrue t2 t3) t2" |
aeval1_if_false: "aeval1 (IfElse FFalse t2 t3) t3" |
aeval1_if: "aeval1 t1 t1' \<Longrightarrow> aeval1 (IfElse t1 t2 t3) (IfElse t1' t2 t3)" |

(* Arithmetic evaluation *)
aeval1_succ: "aeval1 t1 t1' \<Longrightarrow> aeval1 (Succ t1) (Succ t1')" |
aeval1_pred_0: "aeval1 (Pred Zero) Zero" |
aeval1_pred_succ_0: "is_numeric nv \<Longrightarrow> aeval1 (Pred (Succ nv)) nv" |
aeval1_pred: "aeval1 t1 t1' \<Longrightarrow> aeval1 (Pred t1) (Pred t1')" |
aeval1_iszero_0: "aeval1 (IsZero Zero) TTrue" |
aeval1_iszero_suc: "is_numeric nv \<Longrightarrow> aeval1 (IsZero (Succ nv)) FFalse" |
aeval1_iszero: "aveal1 t1 t1' \<Longrightarrow> aeval1 (IsZero t1) (IsZero t1')"

lemma "aeval1 (IfElse (IsZero Zero) TTrue FFalse) (IfElse TTrue TTrue FFalse)"
  apply(rule aeval1_if)
  apply(rule aeval1_iszero_0)
  done

(*
theorem arith_determinacy: "\<lbrakk>aeval1 t t'; aeval1 t' t''\<rbrakk> \<Longrightarrow> t' = t''"
proof (induction t)
  case TTrue
  then show ?case sorry
next
  case FFalse
  then show ?case sorry
next
  case Zero
  then show ?case sorry
next
  case (IfElse t1 t2 t3)
  then show ?case sorry
next
  case (Succ t1)
  then show ?case
    (* Sledgehammer found a proof *)
    (*by (smt (verit, ccfv_SIG) aeval1.simps tapl_arith.distinct(31) tapl_arith.distinct(37) tapl_arith.distinct(39) tapl_arith.inject(2))*)
next
  case (Pred t)
  then show ?case sorry
next
  case (IsZero t)
  then show ?case sorry
qed

theorem arith_determinacy: "\<lbrakk>aeval1 t t'; aeval1 t' t''\<rbrakk> \<Longrightarrow> t' = t''"
proof (induction t t' arbitrary: t'' rule: aeval1.induct)
  case (aeval1_if_true t2 t3)
  then show ?case by (auto intro: aeval1_if_true elim: aeval1.cases)
next
  case (aeval1_if_false t2 t3)
  then show ?case sorry
next
  case (aeval1_if t1 t1' t2 t3)
  then show ?case by (auto del: aeval1.simps)
next
  case (aeval1_succ t1 t1')
  from aeval1_succ.prems aeval1_succ.hyps show ?case
  by auto(elim: aeval1.cases)
next
  case aeval1_pred_0
  then show ?case sorry
next
  case (aeval1_pred_succ_0 nv)
  then show ?case sorry
next
  case (aeval1_pred t1 t1')
  then show ?case sorry
next
  case aeval1_iszero_0
  then show ?case sorry
next
  case (aeval1_iszero_suc nv)
  then show ?case sorry
next
  case (aeval1_iszero aveal1 t1 t1')
  then show ?case sorry
qed

*)

end
