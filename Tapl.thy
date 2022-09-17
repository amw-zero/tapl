theory Tapl

imports Main "HOL.String" "HOL-Library.Code_Target_Nat"

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

inductive tapl_consts :: "tapl_term \<Rightarrow> tapl_term set \<Rightarrow> bool" where
c_true: "tapl_consts true {true}" |
c_false: "tapl_consts false {false}" |
c_0: "tapl_consts zero {zero}" |
c_succ: "tapl_consts t1 s \<Longrightarrow> tapl_consts (suc t1) s" |
c_pred: "tapl_consts t1 s \<Longrightarrow> tapl_consts (pred t1) s" |
c_iszero: "tapl_consts t1 s \<Longrightarrow> tapl_consts (iszero t1) s" |
c_if: "\<lbrakk>tapl_consts t1 s1; tapl_consts t2 s2; tapl_consts t3 s3\<rbrakk> \<Longrightarrow> tapl_consts (If t1 t2 t3) (s1 \<union> s2 \<union> s3)"

inductive tapl_size :: "tapl_term \<Rightarrow> nat \<Rightarrow> bool" where
s_true: "tapl_size true 1" |
s_false: "tapl_size false 1" |
s_0: "tapl_size zero 1" |
s_succ: "tapl_size t1 s \<Longrightarrow> tapl_size (suc t1) (s + 1)" |
s_pred: "tapl_size t1 s \<Longrightarrow> tapl_size (pred t1) (s + 1)" |
s_iszero: "tapl_size t1 s \<Longrightarrow> tapl_size (iszero t1) (s + 1)" |
s_if: "\<lbrakk>tapl_size t1 s1; tapl_size t2 s2; tapl_size t3 s3\<rbrakk> \<Longrightarrow> tapl_size (If t1 t2 t3) (Suc (s1 + s2 + s3))"

inductive tapl_depth :: "tapl_term \<Rightarrow> nat \<Rightarrow> bool" where
d_true: "tapl_depth true 1" |
d_false: "tapl_depth false 1" |
d_0: "tapl_depth zero 1" |
d_succ: "tapl_depth t1 s \<Longrightarrow> tapl_depth (suc t1) (s + 1)" |
d_pred: "tapl_depth t1 s \<Longrightarrow> tapl_depth (pred t1) (s + 1)" |
d_iszero: "tapl_depth t1 s \<Longrightarrow> tapl_depth (iszero t1) (s + 1)" |
d_if: "\<lbrakk>tapl_depth t1 s1; tapl_depth t2 s2; tapl_depth t3 s3\<rbrakk> \<Longrightarrow> tapl_depth (If t1 t2 t3) (Suc ((max s1 (max s2 s3))))"

lemma 
  assumes "finite c"
  shows "\<lbrakk>tapl_consts t c; tapl_size t s; tapl_depth t d\<rbrakk> \<Longrightarrow> card c \<le> s"
  using [[simp_trace_new]]
proof(induction d rule: less_induct)
  case (less x)
  then show ?case
  proof (induction t)
    case true
    then show ?case sorry
  next
    case false
    then show ?case sorry
  next
    case zero
    then show ?case sorry
  next
    case (If t1 t2 t3)
    then show ?case sorry
  next
    case (suc t)
    then show ?case sorry
  next
    case (pred t)
    then show ?case sorry
  next
    case (iszero t)
    then show ?case sorry
  qed
qed

fun tapl_constsf :: "tapl_term \<Rightarrow> tapl_term set" where
"tapl_constsf true = {true}" |
"tapl_constsf false = {false}" |
"tapl_constsf zero = {zero}" |
"tapl_constsf (suc t1) = tapl_constsf t1" |
"tapl_constsf (pred t1) = tapl_constsf t1" |
"tapl_constsf (iszero t1) = tapl_constsf t1" |
"tapl_constsf (If t1 t2 t3) = (tapl_constsf t1 \<union> tapl_constsf t2 \<union> tapl_constsf t3)"

fun tapl_sizef :: "tapl_term \<Rightarrow> nat" where
"tapl_sizef true = 1" |
"tapl_sizef false = 1" |
"tapl_sizef zero = 1" |
"tapl_sizef (suc t1) = (tapl_sizef t1) + 1" |
"tapl_sizef (pred t1) = (tapl_sizef t1) + 1" |
"tapl_sizef (iszero t1) = (tapl_sizef t1) + 1" |
"tapl_sizef (If t1 t2 t3) = tapl_sizef t1 + tapl_sizef t2 + tapl_sizef t3 + 1"

fun tapl_depthf :: "tapl_term \<Rightarrow> nat" where
"tapl_depthf true = 1" |
"tapl_depthf false = 1" |
"tapl_depthf  zero = 1" |
"tapl_depthf (suc t1) = (tapl_depthf t1) + 1" |
"tapl_depthf (pred t1) = (tapl_depthf t1) + 1" |
"tapl_depthf (iszero t1) = (tapl_depthf t1) + 1" |
"tapl_depthf (If t1 t2 t3) = max (tapl_depthf t1) (max (tapl_depthf t2) (tapl_depthf t3)) + 1"

(*
lemma example:
  fixes f :: "nat \<Rightarrow> nat"
  assumes asm: "f (f n) < f (n + 1)" and "kf = f n"
  shows "n \<le> f n"
  proof (induction kf rule: less_induct)
  case (less k)
    then have IH: "y < k \<Longrightarrow> n \<le> f n" by simp
    show ?case
    proof cases
    assume "n = 0"
    then show ?thesis by simp
  next
    assume "n \<noteq> 0"
    then obtain m where "n = m + 1" by (cases n) simp_all
    from asm have "f (f m) < f n" unfolding \<open>n = m + 1\<close> .
    with IH have f m \<le> f (f m) .
    also note 〈f (f m) < f n〉
    finally have f m < f n .
    with IH have m \<le> f m .
    also note 〈f m < f n〉
    finally have m < f n .
    then show n \<le> f n using 〈n = m + 1〉 by simp
  qed
qed
*)

lemma "card (tapl_constsf t) \<le> tapl_sizef t"
proof (induction t)
  case true
  print_theorems
  then show ?case by simp
next
  case false
  then show ?case by simp
next
  case zero
  then show ?case by simp
next
  case (If t1 t2 t3)
  then show ?case sorry
next
  case (suc t)
  then show ?case by auto
next
  case (pred t)
  then show ?case by auto
next
  case (iszero t)
  then show ?case by auto
qed

lemma "\<lbrakk>tapl_depthf t = d\<rbrakk> \<Longrightarrow> card (tapl_constsf t) \<le> tapl_sizef t"
proof (induction d arbitrary: t rule: less_induct)
  case (less x)
  print_theorems
  show ?case
  proof (cases t)
    case true
    thm less.IH
    then show ?thesis by simp
  next
    case false
    then show ?thesis by simp
  next
    case zero
    then show ?thesis by simp
  next
    case (If t1 t2 t3)
    then show ?thesis sorry
  next
    case (suc t1)
    with less.IH and less.prems show ?thesis by force
  next
    case (pred x6)
    with less.IH and less.prems show ?thesis by force
  next
    case (iszero x7)
    with less.IH and less.prems show ?thesis by force
  qed
qed

datatype small_term = suc small_term | zero

fun consts_st :: "small_term \<Rightarrow> small_term set" where
"consts_st zero = {zero}" |
"consts_st (suc t1) = consts_st t1"

fun size_st :: "small_term \<Rightarrow> nat" where
"size_st zero = 1" |
"size_st (suc t1) = (size_st t1) + 1"

fun depth_st :: "small_term \<Rightarrow> nat" where
"depth_st  zero = 1" |
"depth_st (suc t1) = (depth_st t1) + 1"

lemma "\<lbrakk>depth_st t = d\<rbrakk> \<Longrightarrow> card (consts_st t) \<le> size_st t"
proof (induction d arbitrary: t rule: less_induct)
  case (less x)
  then show ?case
  proof (cases t)
    case (suc x1)
    with less.prems and less.IH show ?thesis by force
  next
    case zero
    then show ?thesis by simp
  qed
qed

lemma "card (tapl_constsf t) \<le> tapl_sizef t"
proof(induction t)
  case true
  then show ?case by simp
next
  case false
  then show ?case by simp
next
  case zero
  then show ?case by simp
next
  case (If t1 t2 t3)
  then show ?case sorry
next
  case (suc t)
  then show ?case by simp
next
  case (pred t)
  then show ?case by simp
next
  case (iszero t)
  then show ?case by simp
qed

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


end
