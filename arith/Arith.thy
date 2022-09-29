theory Arith

imports Main

begin

section "Arithmetic Expressions"

datatype arith = 
  ATrue | 
  AFalse | 
  AZero |
  AIfElse arith arith arith |
  ASucc arith |
  APred  arith |
  AIsZero arith

definition is_numeric :: "arith \<Rightarrow> bool" where
"is_numeric t = 
  (case t of 
    AZero \<Rightarrow> True |
    ASucc _ \<Rightarrow> True |
    _ \<Rightarrow> False)"

definition "is_value_arith" :: "arith \<Rightarrow> bool" where
"is_value_arith t =
  (case t of 
    ATrue \<Rightarrow> True |
    AFalse \<Rightarrow> True |
    AZero \<Rightarrow> True |
    ASucc _ \<Rightarrow> True |
    _ \<Rightarrow> False)"

inductive aeval1 :: "arith \<Rightarrow> arith \<Rightarrow> bool" where
(* Bool evaluation *)
aeval1_if_true: "aeval1 (AIfElse ATrue t2 t3) t2" |
aeval1_if_false: "aeval1 (AIfElse AFalse t2 t3) t3" |
aeval1_if: "aeval1 t1 t1' \<Longrightarrow> aeval1 (AIfElse t1 t2 t3) (AIfElse t1' t2 t3)" |

(* Arithmetic evaluation *)
aeval1_succ: "aeval1 t1 t1' \<Longrightarrow> aeval1 (ASucc t1) (ASucc t1')" |
aeval1_pred_0: "aeval1 (APred AZero) AZero" |
aeval1_pred_succ_0: "is_numeric nv \<Longrightarrow> aeval1 (APred (ASucc nv)) nv" |
aeval1_pred: "aeval1 t1 t1' \<Longrightarrow> aeval1 (APred t1) (Pred t1')" |
aeval1_iszero_0: "aeval1 (AIsZero AZero) ATrue" |
aeval1_iszero_suc: "is_numeric nv \<Longrightarrow> aeval1 (AIsZero (ASucc nv)) AFalse" |
aeval1_iszero: "aveal1 t1 t1' \<Longrightarrow> aeval1 (AIsZero t1) (AIsZero t1')"

lemma "aeval1 (AIfElse (AIsZero AZero) ATrue AFalse) (AIfElse ATrue ATrue AFalse)"
  apply(rule aeval1_if)
  apply(rule aeval1_iszero_0)
  done

lemma "aeval1 (ASucc (AIfElse (AIsZero AZero) ATrue AFalse)) (ASucc (AIfElse ATrue ATrue AFalse))"
  apply(rule aeval1_succ)
  apply(rule aeval1_if)
  apply(rule aeval1_iszero_0)
  done

(*
theorem arith_determinacy: "\<lbrakk>aeval1 t t'; aeval1 t' t''\<rbrakk> \<Longrightarrow> t' = t''"
  using [[simp_trace]]
proof (induction t t' arbitrary: t'' rule: aeval1.induct)
  case (aeval1_if_true t2 t3)
  then show ?case sorry
next
  case (aeval1_if_false t2 t3)
  then show ?case sorry
next
  case (aeval1_if t1 t1' t2 t3)
  from aeval1_if.prems aeval1_if.hyps show ?case sorry
next
  case (aeval1_succ t1 t1')
  then show ?case by (auto elim: aeval1.cases)
next
  case aeval1_pred_0
  then show ?case by (auto elim: aeval1.cases)
next
  case (aeval1_pred_succ_0 nv)
  then show ?case sorry
next
  case (aeval1_pred t1 t1')
  then show ?case sorry
next
  case aeval1_iszero_0
  then show ?case by (auto elim: aeval1.cases)
next
  case (aeval1_iszero_suc nv)
  then show ?case sorry
next
  case (aeval1_iszero aveal1 t1 t1')
  then show ?case sorry
qed
*)

inductive aeval :: "arith \<Rightarrow> arith \<Rightarrow> bool" where
reflexive: "aeval t t" |
step: "aeval1 t t' \<Longrightarrow> aeval t' t'' \<Longrightarrow> aeval t t''"

print_theorems

section "Big-step semantics"

inductive bigstep :: "arith \<Rightarrow> arith \<Rightarrow> bool" where
bval: "is_value_arith t \<Longrightarrow> bigstep t t" |
bif_true: "\<lbrakk> bigstep t1 ATrue; bigstep t2 v\<rbrakk> \<Longrightarrow> bigstep (AIfElse t1 t2 t3) v" |
bif_false: "\<lbrakk> bigstep t1 AFalse; bigstep t3 v\<rbrakk> \<Longrightarrow> bigstep (AIfElse t1 t2 t3) v" |
bsucc: "\<lbrakk>is_numeric v; bigstep t v\<rbrakk> \<Longrightarrow> bigstep (ASucc t) (ASucc v)" |
bpred_zero: "bigstep t AZero \<Longrightarrow> bigstep (APred t) AZero" |
bpred_succ: "\<lbrakk>is_numeric v; bigstep t (ASucc v)\<rbrakk> \<Longrightarrow> bigstep (APred t) v" |
bis_zero_zero: "bigstep t AZero \<Longrightarrow> bigstep (AIsZero t) ATrue" |
bis_zero_succ: "\<lbrakk>is_numeric v; bigstep t (ASucc v)\<rbrakk> \<Longrightarrow> bigstep (AIsZero t) AFalse"

code_pred (modes: i => o => bool as bigstep') bigstep . 

definition "bigstep_ex t = Predicate.the (bigstep' t)"

(* ATrue is exported to export constructors of arith type *)
export_code bigstep_ex ATrue in OCaml file_prefix "core"

values "{t. bigstep ATrue t}"

fun bigstep_f :: "arith \<Rightarrow> arith" where
"bigstep_f (AIfElse ATrue t2 t3) = bigstep_f t2" |
"bigstep_f _ = ATrue"

(*

theorem "bigstep t t' \<Longrightarrow> aeval t t'"
proof(induction t t' rule: bigstep.induct)
  case (bval t)
  then show ?case
    by (simp add: aeval.reflexive)
next
  case (bif_true t1 t2 v t3)
  then show ?case sorry
next
  case (bif_false t1 t3 v t2)
  then show ?case sorry
next
  case (bsucc v t)
  then show ?case try 
next
  case (bpred_zero t)
  then show ?case sorry
next
  case (bpred_succ v t)
  then show ?case sorry
next
  case (bis_zero_zero t)
  then show ?case sorry
next
  case (bis_zero_succ v t)
  then show ?case sorry
qed

*)

(*
lemma "aeval t1 t1' \<Longrightarrow> aeval (AIfElse t1 t2 t3) (AIfElse t1' t2 t3)"
proof(induction t1)
  case ATrue
  then show ?case sorry
next
  case AFalse
  then show ?case sorry
next
  case AZero
  then show ?case sorry
next
  case (AIfElse t11 t12 t13)
  then show ?case by (auto elim: aeval.cases
next
  case (ASucc t1)
  then show ?case sorry
next
  case (APred t1)
  then show ?case sorry
next
  case (AIsZero t1)
  then show ?case sorry
qed
*)

end